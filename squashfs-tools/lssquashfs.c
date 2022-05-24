/*
 * List a squashfs filesystem.  This is a highly compressed read only
 * filesystem.
 *
 * Copyright (c) 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011,
 * 2012, 2013, 2014, 2022
 * Phillip Lougher <phillip@squashfs.org.uk>
 * Alan REN <renang@nationalchip.com>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2,
 * or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * lssquashfs.c
 */

#include "unsquashfs.h"
#include "squashfs_swap.h"
#include "squashfs_compat.h"
#include "compressor.h"
#include "xattr.h"
#include "unsquashfs_info.h"
#include "stdarg.h"

#include <sys/sysinfo.h>
// #include <sys/types.h>
#include <sys/sysmacros.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <limits.h>
#include <ctype.h>
#include <getopt.h>

int fd;
int swap;
struct super_block sBlk;
squashfs_operations s_ops;                  // File System Operations
char *inode_table = NULL;
char *directory_table = NULL;
struct hash_table_entry *inode_table_hash[65536];
struct hash_table_entry *directory_table_hash[65536];
unsigned int *uid_table;
unsigned int *guid_table;
int inode_number = 1;

int lookup_type[] = {
    0,
    S_IFDIR,
    S_IFREG,
    S_IFLNK,
    S_IFBLK,
    S_IFCHR,
    S_IFIFO,
    S_IFSOCK,
    S_IFDIR,
    S_IFREG,
    S_IFLNK,
    S_IFBLK,
    S_IFCHR,
    S_IFIFO,
    S_IFSOCK
};

//-------------------------------------------------------------------------------------------------

static struct compressor *_compressor;
static unsigned int _block_size;
static unsigned int _block_log;
static int _dump_list = 0;
static enum {
    DUMP_TYPE_NORMAL = 0,
    DUMP_TYPE_CSV,
    DUMP_TYPE_TABLE
} _dump_type = DUMP_TYPE_NORMAL;

//=================================================================================================

int read_fs_bytes(int fd, long long byte, int bytes, void *buff)
{
    off_t off = byte;
    int res, count;

    TRACE("read_bytes: reading from position 0x%llx, bytes %d\n", byte, bytes);

    if(lseek(fd, off, SEEK_SET) == -1) {
        printf("Lseek failed because %s\n", strerror(errno));
        return FALSE;
    }

    for(count = 0; count < bytes; count += res) {
        res = read(fd, buff + count, bytes - count);
        if(res < 1) {
            if(res == 0) {
                printf("Read on filesystem failed because EOF\n");
                return FALSE;
            } else if(errno != EINTR) {
                printf("Read on filesystem failed because %s\n", strerror(errno));
                return FALSE;
            } else
                res = 0;
        }
    }

    return TRUE;
}

int read_block(int fd, long long start, long long *next, int expected, void *block)
{
    unsigned short c_byte;
    int offset = 2, res, compressed;
    int outlen = expected ? expected : SQUASHFS_METADATA_SIZE;

    if(swap) {
        if(read_fs_bytes(fd, start, 2, &c_byte) == FALSE)
            goto failed;
        c_byte = (c_byte >> 8) | ((c_byte & 0xff) << 8);
    } else
        if(read_fs_bytes(fd, start, 2, &c_byte) == FALSE)
            goto failed;

    TRACE("read_block: block @0x%llx, %d %s bytes\n", start,
           SQUASHFS_COMPRESSED_SIZE(c_byte), SQUASHFS_COMPRESSED(c_byte) ?
           "compressed" : "uncompressed");

    if(SQUASHFS_CHECK_DATA(sBlk.s.flags))
        offset = 3;

    compressed = SQUASHFS_COMPRESSED(c_byte);
    c_byte = SQUASHFS_COMPRESSED_SIZE(c_byte);

    /*
     * The block size should not be larger than
     * the uncompressed size (or max uncompressed size if
     * expected is 0)
     */
    if(c_byte > outlen)
        return 0;

    if(compressed) {
        char buffer[c_byte];
        int error;

        res = read_fs_bytes(fd, start + offset, c_byte, buffer);
        if(res == FALSE)
            goto failed;

        res = compressor_uncompress(_compressor, block, buffer, c_byte, outlen, &error);

        if(res == -1) {
            ERROR("%s uncompress failed with error code %d\n",
                  _compressor->name, error);
            goto failed;
        }
    } else {
        res = read_fs_bytes(fd, start + offset, c_byte, block);
        if(res == FALSE)
            goto failed;
        res = c_byte;
    }

    if(next)
        *next = start + offset + c_byte;

    /*
     * if expected, then check the (uncompressed) return data
     * is of the expected size
     */
    if(expected && expected != res)
        return 0;
    else
        return res;

failed:
    ERROR("read_block: failed to read block @0x%llx\n", start);
    return FALSE;
}

void progressbar_error(char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
}

int lookup_entry(struct hash_table_entry *hash_table[], long long start)
{
    int hash = CALCULATE_HASH(start);
    struct hash_table_entry *hash_table_entry;

    for(hash_table_entry = hash_table[hash]; hash_table_entry; hash_table_entry = hash_table_entry->next){
        if(hash_table_entry->start == start)
            return hash_table_entry->bytes;
    }

    return -1;
}

void prep_exit()
{
}

//=================================================================================================

static int _mount_squashfs(const char *source)
{
    /*
     * Try to read a Squashfs 4 superblock
     */
    struct squashfs_super_block sBlk_4;
    read_fs_bytes(fd, SQUASHFS_START, sizeof(struct squashfs_super_block), &sBlk_4);
    swap = sBlk_4.s_magic != SQUASHFS_MAGIC;
    SQUASHFS_INSWAP_SUPER_BLOCK(&sBlk_4);

    if(sBlk_4.s_magic == SQUASHFS_MAGIC && sBlk_4.s_major == 4 && sBlk_4.s_minor == 0) {
        // Setup operators
        s_ops.squashfs_opendir = squashfs_opendir_4;
        s_ops.read_fragment = read_fragment_4;
        s_ops.read_fragment_table = read_fragment_table_4;
        s_ops.read_block_list = read_block_list_2;
        s_ops.read_inode = read_inode_4;
        s_ops.read_uids_guids = read_uids_guids_4;
        memcpy(&sBlk, &sBlk_4, sizeof(sBlk_4));

        /*
         * Check the compression type
         */
        _compressor = lookup_compressor_id(sBlk.s.compression);
        return TRUE;
    }

    /*
      * Not a Squashfs 4 superblock, try to read a squashfs 3 superblock
      * (compatible with 1 and 2 filesystems)
      */
    squashfs_super_block_3 sBlk_3;
    read_fs_bytes(fd, SQUASHFS_START, sizeof(squashfs_super_block_3), &sBlk_3);

    /*
     * Check it is a SQUASHFS superblock
     */
    swap = 0;
    if(sBlk_3.s_magic != SQUASHFS_MAGIC) {
        if(sBlk_3.s_magic == SQUASHFS_MAGIC_SWAP) {
            squashfs_super_block_3 sblk;
            ERROR("Reading a different endian SQUASHFS filesystem on %s\n", source);
            SQUASHFS_SWAP_SUPER_BLOCK_3(&sblk, &sBlk_3);
            memcpy(&sBlk_3, &sblk, sizeof(squashfs_super_block_3));
            swap = 1;
        } else  {
            ERROR("Can't find a SQUASHFS superblock on %s\n", source);
            goto failed_mount;
        }
    }

    sBlk.s.s_magic = sBlk_3.s_magic;
    sBlk.s.inodes = sBlk_3.inodes;
    sBlk.s.mkfs_time = sBlk_3.mkfs_time;
    sBlk.s.block_size = sBlk_3.block_size;
    sBlk.s.fragments = sBlk_3.fragments;
    sBlk.s.block_log = sBlk_3.block_log;
    sBlk.s.flags = sBlk_3.flags;
    sBlk.s.s_major = sBlk_3.s_major;
    sBlk.s.s_minor = sBlk_3.s_minor;
    sBlk.s.root_inode = sBlk_3.root_inode;
    sBlk.s.bytes_used = sBlk_3.bytes_used;
    sBlk.s.inode_table_start = sBlk_3.inode_table_start;
    sBlk.s.directory_table_start = sBlk_3.directory_table_start;
    sBlk.s.fragment_table_start = sBlk_3.fragment_table_start;
    sBlk.s.lookup_table_start = sBlk_3.lookup_table_start;
    sBlk.no_uids = sBlk_3.no_uids;
    sBlk.no_guids = sBlk_3.no_guids;
    sBlk.uid_start = sBlk_3.uid_start;
    sBlk.guid_start = sBlk_3.guid_start;
    sBlk.s.xattr_id_table_start = SQUASHFS_INVALID_BLK;

    /* Check the MAJOR & MINOR versions */
    if(sBlk.s.s_major == 1 || sBlk.s.s_major == 2) {
        sBlk.s.bytes_used = sBlk_3.bytes_used_2;
        sBlk.uid_start = sBlk_3.uid_start_2;
        sBlk.guid_start = sBlk_3.guid_start_2;
        sBlk.s.inode_table_start = sBlk_3.inode_table_start_2;
        sBlk.s.directory_table_start = sBlk_3.directory_table_start_2;

        if(sBlk.s.s_major == 1) {
            sBlk.s.block_size = sBlk_3.block_size_1;
            sBlk.s.fragment_table_start = sBlk.uid_start;
            s_ops.squashfs_opendir = squashfs_opendir_1;
            s_ops.read_fragment_table = read_fragment_table_1;
            s_ops.read_block_list = read_block_list_1;
            s_ops.read_inode = read_inode_1;
            s_ops.read_uids_guids = read_uids_guids_1;
        } else {
            sBlk.s.fragment_table_start =
                sBlk_3.fragment_table_start_2;
            s_ops.squashfs_opendir = squashfs_opendir_1;
            s_ops.read_fragment = read_fragment_2;
            s_ops.read_fragment_table = read_fragment_table_2;
            s_ops.read_block_list = read_block_list_2;
            s_ops.read_inode = read_inode_2;
            s_ops.read_uids_guids = read_uids_guids_1;
        }
    } else if(sBlk.s.s_major == 3) {
        s_ops.squashfs_opendir = squashfs_opendir_3;
        s_ops.read_fragment = read_fragment_3;
        s_ops.read_fragment_table = read_fragment_table_3;
        s_ops.read_block_list = read_block_list_2;
        s_ops.read_inode = read_inode_3;
        s_ops.read_uids_guids = read_uids_guids_1;
    } else {
        ERROR("Filesystem on %s is (%d:%d), ", source, sBlk.s.s_major,
            sBlk.s.s_minor);
        ERROR("which is a later filesystem version than I support!\n");
        goto failed_mount;
    }

    /*
     * 1.x, 2.x and 3.x filesystems use gzip compression.
     */
    _compressor = lookup_compressor("gzip");
    return TRUE;

failed_mount:
    return FALSE;
}

static void _add_entry(struct hash_table_entry *hash_table[], long long start, int bytes)
{
    int hash = CALCULATE_HASH(start);
    struct hash_table_entry *hash_table_entry;

    hash_table_entry = malloc(sizeof(struct hash_table_entry));
    if(hash_table_entry == NULL)
        EXIT_UNSQUASH("Out of memory in add_entry\n");

    hash_table_entry->start = start;
    hash_table_entry->bytes = bytes;
    hash_table_entry->next = hash_table[hash];
    hash_table[hash] = hash_table_entry;
}

static int _read_inode_table(long long start, long long end)
{
    int size = 0, bytes = 0, res;

    TRACE("read_inode_table: start %lld, end %lld\n", start, end);

    while(start < end) {
        if(size - bytes < SQUASHFS_METADATA_SIZE) {
            inode_table = realloc(inode_table, size += SQUASHFS_METADATA_SIZE);
            if(inode_table == NULL) {
                ERROR("Out of memory in read_inode_table");
                goto failed;
            }
        }

        _add_entry(inode_table_hash, start, bytes);

        res = read_block(fd, start, &start, 0, inode_table + bytes);
        if(res == 0) {
            ERROR("read_inode_table: failed to read block\n");
            goto failed;
        }
        bytes += res;

        /*
         * If this is not the last metadata block in the inode table
         * then it should be SQUASHFS_METADATA_SIZE in size.
         * Note, we can't use expected in read_block() above for this
         * because we don't know if this is the last block until
         * after reading.
         */
        if(start != end && res != SQUASHFS_METADATA_SIZE) {
            ERROR("read_inode_table: metadata block should be %d bytes in length, it is %d bytes\n",
                  SQUASHFS_METADATA_SIZE, res);

            goto failed;
        }
    }

    return TRUE;

failed:
    free(inode_table);
    return FALSE;
}

static int _read_directory_table(long long start, long long end)
{
    int bytes = 0, size = 0, res;

    TRACE("read_directory_table: start %lld, end %lld\n", start, end);

    while(start < end) {
        if(size - bytes < SQUASHFS_METADATA_SIZE) {
            directory_table = realloc(directory_table, size +=
                SQUASHFS_METADATA_SIZE);
            if(directory_table == NULL) {
                ERROR("Out of memory in "
                        "read_directory_table\n");
                goto failed;
            }
        }

        _add_entry(directory_table_hash, start, bytes);

        res = read_block(fd, start, &start, 0, directory_table + bytes);
        if(res == 0) {
            ERROR("read_directory_table: failed to read block\n");
            goto failed;
        }

        bytes += res;

        /*
         * If this is not the last metadata block in the directory table
         * then it should be SQUASHFS_METADATA_SIZE in size.
         * Note, we can't use expected in read_block() above for this
         * because we don't know if this is the last block until
         * after reading.
         */
        if(start != end && res != SQUASHFS_METADATA_SIZE) {
            ERROR("read_directory_table: metadata block "
                "should be %d bytes in length, it is %d "
                "bytes\n", SQUASHFS_METADATA_SIZE, res);
            goto failed;
        }
    }

    return TRUE;

failed:
    free(directory_table);
    return FALSE;
}

static int _squashfs_readdir(struct dir *dir, char **name, unsigned int *start_block, unsigned int *offset, unsigned int *type)
{
    if(dir->cur_entry == dir->dir_count)
        return FALSE;

    *name = dir->dirs[dir->cur_entry].name;
    *start_block = dir->dirs[dir->cur_entry].start_block;
    *offset = dir->dirs[dir->cur_entry].offset;
    *type = dir->dirs[dir->cur_entry].type;
    dir->cur_entry ++;

    return TRUE;
}

static void _squashfs_closedir(struct dir *dir)
{
    free(dir->dirs);
    free(dir);
}

//-------------------------------------------------------------------------------------------------

static void _print_brief(const char *source)
{
#if __BYTE_ORDER == __BIG_ENDIAN
    printf("Found a valid %sSQUASHFS %d:%d on %s.\n",
            sBlk.s.s_major == 4 ? "" : swap ? "little endian " : "big endian ",
            sBlk.s.s_major,
            sBlk.s.s_minor,
            source);
#else
    printf("Found a valid %sSQUASHFS %d:%d on %s.\n",
            sBlk.s.s_major == 4 ? "" : swap ? "big endian " : "little endian ",
            sBlk.s.s_major,
            sBlk.s.s_minor,
            source);
#endif
}

static void _print_super_block(void)
{
    // mkfs_time
    time_t mkfs_time = (time_t)sBlk.s.mkfs_time;
    char *mkfs_str = ctime(&mkfs_time);
    printf("Creation or last append time:        %s",
            mkfs_str ? mkfs_str : "failed to get time\n");

    // bytes_used
    printf("Filesystem size:                     %lld bytes (%.2f Mbytes)\n",
            sBlk.s.bytes_used,
            sBlk.s.bytes_used / (1024.0 * 1024.0));

    // flags
    printf("Filesystem flags:                    0x%x\n", sBlk.s.flags);
    printf("\t-noI=%d:                      Inodes are %scompressed\n", SQUASHFS_UNCOMPRESSED_INODES(sBlk.s.flags),
           SQUASHFS_UNCOMPRESSED_INODES(sBlk.s.flags) ? "un" : "");
    printf("\t-noD=%d:                      Data is %scompressed\n", SQUASHFS_UNCOMPRESSED_DATA(sBlk.s.flags),
           SQUASHFS_UNCOMPRESSED_DATA(sBlk.s.flags) ? "un" : "");
    printf("\t-check=%d:                    Check data is %spresent in the filesystem\n", SQUASHFS_BIT(sBlk.s.flags, SQUASHFS_CHECK),
           SQUASHFS_CHECK_DATA(sBlk.s.flags) ? "" : "not ");
    printf("\t-noF=%d:                      Fragments are %scompressed\n", SQUASHFS_UNCOMPRESSED_FRAGMENTS(sBlk.s.flags),
           SQUASHFS_UNCOMPRESSED_FRAGMENTS(sBlk.s.flags) ? "un" : "");
    printf("\t-no-fragments=%d:             %s\n", SQUASHFS_NO_FRAGMENTS(sBlk.s.flags),
           SQUASHFS_NO_FRAGMENTS(sBlk.s.flags) ? "Fragments are not stored" : "");
    printf("\t-always-use-fragments=%d:     Always-use-fragments option is %sspecified\n", SQUASHFS_ALWAYS_FRAGMENTS(sBlk.s.flags),
           SQUASHFS_ALWAYS_FRAGMENTS(sBlk.s.flags) ? "" : "not ");
    printf("\t-no-duplicates=%d:            Duplicates are %sremoved\n", !SQUASHFS_DUPLICATES(sBlk.s.flags),
           SQUASHFS_DUPLICATES(sBlk.s.flags) ? "" : "not ");
    printf("\t-no-exports=%d:               Filesystem is %sexportable via NFS\n", !SQUASHFS_EXPORTABLE(sBlk.s.flags),
           SQUASHFS_EXPORTABLE(sBlk.s.flags) ? "" : "not ");
    printf("\t-noX=%d:                      Xattrs are %scompressed\n", SQUASHFS_UNCOMPRESSED_XATTRS(sBlk.s.flags),
           SQUASHFS_UNCOMPRESSED_XATTRS(sBlk.s.flags) ? "un" : "");
    printf("\t-xattrs=%d:                   Xattrs are %sstored\n", !SQUASHFS_NO_XATTRS(sBlk.s.flags),
           SQUASHFS_NO_XATTRS(sBlk.s.flags) ? "not " : "");

    // compression type
    if(sBlk.s.s_major == 4) {
        printf("Compression:                         %s\n", _compressor->name);

        if(SQUASHFS_COMP_OPTS(sBlk.s.flags)) {
            char buffer[SQUASHFS_METADATA_SIZE] __attribute__ ((aligned));
            int bytes;

            bytes = read_block(fd, sizeof(sBlk.s), NULL, 0, buffer);
            if(bytes == 0) {
                ERROR("Failed to read compressor options\n");
                return;
            }

            compressor_display_options(_compressor, buffer, bytes);
        }
        else {
            printf("\tNo extra compession options\n");
        }
    }

    // block_size, block_log
    printf("Block size:                          %d(2^%d)\n", sBlk.s.block_size, sBlk.s.block_log);

    // Inode
    printf("I-node Number:                       %d\n", sBlk.s.inodes);

    // Fragment Number
    if(sBlk.s.s_major > 1)
        printf("Fragments Number:                    %d\n", sBlk.s.fragments);

    // UID / GID
    if(sBlk.s.s_major == 4)
        printf("UID/GID Number:                      %d\n", sBlk.s.no_ids);
    else {
        printf("UID Number:                          %d\n", sBlk.no_uids);
        printf("GID Number:                          %d\n", sBlk.no_guids);
    }

    // Root Inode
    printf("Root Inode:                          0x%llx <%x:%x>\n",
            sBlk.s.root_inode,
            SQUASHFS_INODE_BLK(sBlk.s.root_inode),
            SQUASHFS_INODE_OFFSET(sBlk.s.root_inode));

    // Fragment & Block Zone Info
    long long block_fragment_pos;
    if (sBlk.s.s_major == 4) {
        block_fragment_pos = sizeof(struct squashfs_super_block);
        if(SQUASHFS_COMP_OPTS(sBlk.s.flags)) {
            block_fragment_pos += SQUASHFS_METADATA_SIZE;
        }
    }
    else {
        block_fragment_pos = sizeof(squashfs_super_block_3);
    }
    printf("Block & Fragment:                    pos=%lld(0x%llx) size=%lld\n", block_fragment_pos, block_fragment_pos,
           sBlk.s.inode_table_start - block_fragment_pos);

    // Inode Table Position
    printf("Inode Table:                         pos=%lld(0x%llx) size=%lld\n", sBlk.s.inode_table_start, sBlk.s.inode_table_start,
           sBlk.s.directory_table_start - sBlk.s.inode_table_start);

    // Directory Table Position
    long long directory_table_size = - sBlk.s.directory_table_start;
    if (sBlk.s.fragment_table_start != -1) {
        directory_table_size += sBlk.s.fragment_table_start;
    }
    else if (sBlk.s.lookup_table_start != -1) {
        directory_table_size += sBlk.s.lookup_table_start;
    }
    else {
        directory_table_size += (sBlk.s.s_major == 4 ? sBlk.s.id_table_start : sBlk.uid_start);
    }
    printf("Directory Table:                     pos=%lld(0x%llx) size=%lld\n", sBlk.s.directory_table_start, sBlk.s.directory_table_start,
            directory_table_size);

    // Fragment Table Position
    long long fragment_table_size = - sBlk.s.fragment_table_start;
    if (sBlk.s.fragment_table_start == -1) {
        fragment_table_size = 0;
    }
    else if (sBlk.s.lookup_table_start != -1) {
        fragment_table_size += sBlk.s.lookup_table_start ;
    }
    else {
        fragment_table_size += (sBlk.s.s_major == 4 ? sBlk.s.id_table_start : sBlk.uid_start);
    }
    if(sBlk.s.s_major > 1) {
        printf("Fragment Table:                      pos=%lld(0x%llx) size=%lld\n", sBlk.s.fragment_table_start, sBlk.s.fragment_table_start,
                fragment_table_size);
    }

    // Lookup Table
    long long lookup_table_size = - sBlk.s.lookup_table_start;
    if (sBlk.s.lookup_table_start == -1) {
        lookup_table_size = 0;
    }
    else {
        lookup_table_size += (sBlk.s.s_major == 4 ? sBlk.s.id_table_start : sBlk.uid_start);
    }
    if(sBlk.s.s_major > 2) {
        printf("Export Table:                        pos=%lld(0x%llx) size=%lld\n", sBlk.s.lookup_table_start, sBlk.s.lookup_table_start,
                lookup_table_size);
    }

    // UID/GID Table
    if(sBlk.s.s_major == 4) {
        printf("ID Table:                            pos=%lld(0x%llx) size=%lld\n", sBlk.s.id_table_start, sBlk.s.id_table_start,
                sBlk.s.xattr_id_table_start == -1 ? sBlk.s.bytes_used - sBlk.s.id_table_start : sBlk.s.xattr_id_table_start - sBlk.s.id_table_start);
        printf("Xattr Table:                         pos=%lld(0x%llx) size=%lld\n", sBlk.s.xattr_id_table_start, sBlk.s.xattr_id_table_start,
                sBlk.s.xattr_id_table_start == -1 ? 0 : sBlk.s.bytes_used - sBlk.s.xattr_id_table_start);
    } else {
        printf("UID Table:                           pos=%lld(0x%llx) size=%lld\n", sBlk.uid_start, sBlk.uid_start,
                sBlk.guid_start == -1 ? sBlk.s.bytes_used - sBlk.uid_start : sBlk.guid_start - sBlk.uid_start);
        printf("GUID Table:                          pos=%lld(0x%llx) size=%lld\n", sBlk.guid_start, sBlk.guid_start,
                sBlk.guid_start == -1 ? 0 : sBlk.s.bytes_used - sBlk.guid_start);
    }
}

//-------------------------------------------------------------------------------------------------
static int _fragment_file_num = 0;
static void _print_fragment_file(char *parent_name, unsigned int start_block, unsigned int offset, int fragment_id)
{
    unsigned int type;
    char *name;

    struct inode *dir_inode;
    struct dir *dir = s_ops.squashfs_opendir(start_block, offset, &dir_inode);
    if(dir == NULL)
        return;

    while(_squashfs_readdir(dir, &name, &start_block, &offset, &type)) {

        // Generate the pathname
        char *pathname = NULL;
        if (asprintf(&pathname, "%s/%s", parent_name, name) == -1)
            EXIT_UNSQUASH("asprintf failed in dir_scan\n");

        if(type == SQUASHFS_DIR_TYPE) {
            _print_fragment_file(pathname, start_block, offset, fragment_id);
        }
        else {
            if(type == SQUASHFS_FILE_TYPE || type == SQUASHFS_LREG_TYPE) {
                // Read Inode
                struct inode *inode = s_ops.read_inode(start_block, offset);
                if (inode->fragment == fragment_id) {
                    printf("\t% 8d %-8d            %s/%s\n", inode->offset, inode->frag_bytes, parent_name, name);
                    _fragment_file_num++;
                }
            }
        }

        free(pathname);
    }

    _squashfs_closedir(dir);
}

static int _get_fragment_file_size(unsigned int start_block, unsigned int offset, int fragment_id)
{
    struct inode *dir_inode;
    struct dir *dir = s_ops.squashfs_opendir(start_block, offset, &dir_inode);
    if(dir == NULL)
        return 0;

    int frag_file_size = 0;
    char *name;
    unsigned int type;
    while(_squashfs_readdir(dir, &name, &start_block, &offset, &type)) {
        if(type == SQUASHFS_DIR_TYPE) {
            frag_file_size += _get_fragment_file_size(start_block, offset, fragment_id);
        }
        else {
            if(type == SQUASHFS_FILE_TYPE || type == SQUASHFS_LREG_TYPE) {
                // Read Inode
                struct inode *inode = s_ops.read_inode(start_block, offset);
                if (inode->fragment == fragment_id) {
                    frag_file_size += inode->frag_bytes;
                }
            }
        }
    }

    _squashfs_closedir(dir);
    return frag_file_size;
}

static void _print_fragments(void)
{
    if (_dump_type != DUMP_TYPE_NORMAL) {
        printf("Fragment, Pos Dec, Pos Hex, Frag Size, File Size, Fill Ratio, Compress Ratio\n");
    }

    _fragment_file_num = 0;
    for (int i = 0; i < sBlk.s.fragments; i++) {
        int frag_size;
        long long frag_start;
        s_ops.read_fragment(i, &frag_start, &frag_size);

        int file_size = _get_fragment_file_size(SQUASHFS_INODE_BLK(sBlk.s.root_inode), SQUASHFS_INODE_OFFSET(sBlk.s.root_inode), i);

        static const char *format[] = {
            "Fragement %d: pos=%lld(%llx) size=%d/%d fr=%.2f%% cr=%.2f\n",
            "%d, %lld, 0x%llx, %d, %d, %.2f%%, %.2f\n",
            "|%d | %lld | %llx | %d | %d | %.2f%% | %.2f |\n",
        };

        printf(format[_dump_type], i,
                frag_start, frag_start, frag_size, file_size,
                file_size * 100.0 / sBlk.s.block_size,
                file_size * 1.0 / frag_size);

        if (_dump_list)
            _print_fragment_file("", SQUASHFS_INODE_BLK(sBlk.s.root_inode), SQUASHFS_INODE_OFFSET(sBlk.s.root_inode), i);
    }
    printf("total fragment file number: %d\n", _fragment_file_num);
}

//-------------------------------------------------------------------------------------------------

static int _block_file_num = 0;
static int _block_block_num = 0;
static void _print_block_file(char *parent_name, unsigned int start_block, unsigned int offset)
{
    unsigned int type;
    char *name;

    struct inode *dir_inode;
    struct dir *dir = s_ops.squashfs_opendir(start_block, offset, &dir_inode);
    if(dir == NULL)
        return;

    while(_squashfs_readdir(dir, &name, &start_block, &offset, &type)) {

        // Generate the pathname
        char *pathname = NULL;
        if (asprintf(&pathname, "%s/%s", parent_name, name) == -1)
            EXIT_UNSQUASH("asprintf failed in %s:%d\n", __FUNCTION__, __LINE__);

        if(type == SQUASHFS_DIR_TYPE) {
            _print_block_file(pathname, start_block, offset);
        }
        else {
            if(type == SQUASHFS_FILE_TYPE || type == SQUASHFS_LREG_TYPE) {

                struct inode *inode = s_ops.read_inode(start_block, offset);
                if (inode->blocks) {
                    // get block list
                    unsigned int *block_list = malloc(inode->blocks * sizeof(unsigned int));
                    if (block_list == NULL)
                        EXIT_UNSQUASH("malloc failed in %s:%d\n", __FUNCTION__, __LINE__);
                    s_ops.read_block_list(block_list, inode->block_ptr, inode->blocks);

                    // get compress size
                    int compress_size = 0;
                    for (int i = 0; i < inode->blocks; i++) {
                        compress_size += SQUASHFS_COMPRESSED_SIZE_BLOCK(block_list[i]);
                    }

                    static const char *format[] = {
                        "%d %s/%s: pos=%lld(0x%llx) bn=%d size=%d/%lld cr=%.2f\n",
                        "%d, %s/%s, %lld, 0x%llx, %d, %d, %lld, %.2f\n",
                        "|%d|%s/%s | %lld | 0x%llx | %d | %d | %lld | %.2f |\n",
                    };

                    printf(format[_dump_type], _block_file_num, parent_name, name,
                           inode->start, inode->start, inode->blocks,
                           compress_size, inode->data,
                           inode->data / (float)compress_size);

                    _block_file_num ++;
                    _block_block_num += inode->blocks;

                    if (_dump_list) {
                        long long block_start = inode->start;
                        int file_end = inode->data / _block_size;
                        for (int i = 0; i < inode->blocks; i++) {
                            int blk_size = SQUASHFS_COMPRESSED_SIZE_BLOCK(block_list[i]);
                            int data_size = i == file_end ? inode->data & (_block_size - 1) : _block_size;
                            printf("\tblock %d: pos=%lld(0x%llx)\tsize=% 8d / %-8d\tcr=%.2f\n", i, block_start, block_start,
                                blk_size, data_size, data_size / (float)blk_size);

                            block_start += SQUASHFS_COMPRESSED_SIZE_BLOCK(block_list[i]);
                        }
                    }


                    free(block_list);
                }
            }
        }

        free(pathname);
    }

    _squashfs_closedir(dir);
}

static void _print_blocks(void)
{
    _block_file_num = 0;
    _block_block_num = 0;
    _print_block_file("", SQUASHFS_INODE_BLK(sBlk.s.root_inode), SQUASHFS_INODE_OFFSET(sBlk.s.root_inode));

    printf("total block file num:       %d\n", _block_file_num);
    printf("total block num:            %d\n", _block_block_num);
}

//-------------------------------------------------------------------------------------------------

static void _print_inodes(char *parent_name, unsigned int start_block, unsigned int offset, unsigned int inode_block)
{
    unsigned int type;
    char *name;

    struct inode *dir_inode;
    struct dir *dir = s_ops.squashfs_opendir(start_block, offset, &dir_inode);
    if(dir == NULL)
        return;

    while(_squashfs_readdir(dir, &name, &start_block, &offset, &type)) {

        // Generate the pathname
        char *pathname = NULL;
        if (asprintf(&pathname, "%s/%s", parent_name, name) == -1)
            EXIT_UNSQUASH("asprintf failed in dir_scan\n");

        if (start_block == inode_block) {
            printf("\t%04x:%04x %d %s\n",
                   start_block, offset, type,
                   pathname);
        }

        if(type == SQUASHFS_DIR_TYPE) {
            _print_inodes(pathname, start_block, offset, inode_block);
        }

        free(pathname);
    }

    _squashfs_closedir(dir);
}

static void _print_inode_table(long long start, long long end)
{
    int i = 0;
    int offset = 0;
    while(start < end) {
        unsigned short prefix;
        if (read_fs_bytes(fd, start, 2, &prefix) == FALSE)
            return;

        if (swap) {
            prefix = (prefix >> 8) | ((prefix & 0xff) << 8);
        }

        int compressed = SQUASHFS_COMPRESSED(prefix);
        int size = SQUASHFS_COMPRESSED_SIZE(prefix);

        printf("inode block %d: pos=%lld(0x%llx) offset=%d(0x%x) size=%d compress=%d\n", i,
                start, start,
                offset, offset,
                size, compressed);

        if (_dump_list)
            _print_inodes("", SQUASHFS_INODE_BLK(sBlk.s.root_inode), SQUASHFS_INODE_OFFSET(sBlk.s.root_inode), offset);

        offset += size + 2;
        start += size + 2;
        i++;
    }
}

static void _print_directory_table(long long start, long long end)
{
    int i = 0;
    int offset = 0;
    while(start < end) {
        unsigned short prefix;
        if (read_fs_bytes(fd, start, 2, &prefix) == FALSE)
            return;

        if (swap) {
            prefix = (prefix >> 8) | ((prefix & 0xff) << 8);
        }

        int compressed = SQUASHFS_COMPRESSED(prefix);
        int size = SQUASHFS_COMPRESSED_SIZE(prefix);

        printf("directory block %d: pos=%lld(0x%llx) offset=%d(0x%x) size=%d compress=%d\n", i,
                start, start,
                offset, offset,
                size, compressed);

        offset += size + 2;
        start += size + 2;
        i++;
    }
}

//=================================================================================================

static void _print_cmdline_usage(const char *me)
{
    printf("Usage: %s [options] <FileSystem>\n", me);
    printf("  <FileSystem>      Specify the path to the squashfs image\n");
    printf("  -h, --help        Print this usage\n");
    printf("  -a, --all         Dump all information\n");
    printf("  -s, --super       Dump super block\n");
    printf("  -f, --fragment    Dump fragment\n");
    printf("  -b, --block       Dump block\n");
    printf("  -i, --inode       Dump inode table\n");
    printf("  -d, --directory   Dump directory table\n");
    printf("  -l, --list        Dump with list of files");
    printf("  -c, --csv         Dump as CSV\n");
    printf("  -t, --table       Dump as Table\n");
}

int main(int argc, char *argv[])
{
    // options
    int dump_superblock = 0;
    int dump_fragment = 0;
    int dump_block = 0;
    int dump_inode = 0;
    int dump_directory = 0;

    // 解析选项
    struct option long_options[] = {
        {"help",        no_argument,        0,      'h' },
        {"all",         no_argument,        0,      'a' },
        {"super",       no_argument,        0,      's' },
        {"fragement",   no_argument,        0,      'f' },
        {"block",       no_argument,        0,      'b' },
        {"inode",       no_argument,        0,      'i' },
        {"directory",   no_argument,        0,      'd' },
        {"list",        no_argument,        0,      'l' },
        {"csv",         no_argument,        0,      'c' },
        {"table",       no_argument,        0,      't' },
        { 0,            0,                  0,       0  }
    };

    while (1) {
        /* getopt_long stores the option index here. */
        int option_index = 0;
        int c = getopt_long(argc, argv, "hasfbidlct", long_options, &option_index);

        /* Detect the end of the options. */
        if (c == -1)
            break;

        switch(c) {
        case 0:
            /* If this option set a flag, do nothing else now. */
            if (long_options[option_index].flag != 0)
                break;
            printf("option %s", long_options[option_index].name);
            if (optarg)
                printf (" with arg %s", optarg);
            printf ("\n");
            break;
        case '?':
        case 'h':
            /* getopt_long already printed an error message. */
            _print_cmdline_usage(argv[0]);
            return 0;

        case 'a':
            dump_superblock = 1;
            dump_fragment = 1;
            dump_block = 1;
            dump_inode = 1;
            dump_directory = 1;
            break;

        case 's':
            dump_superblock = 1;
            break;

        case 'f':
            dump_fragment = 1;
            break;

        case 'b':
            dump_block = 1;
            break;

        case 'i':
            dump_inode = 1;
            break;

        case 'd':
            dump_directory = 1;
            break;

        case 'l':
            _dump_list = 1;
            break;

        case 'c':
            _dump_type = DUMP_TYPE_CSV;
            break;

        case 't':
            _dump_type = DUMP_TYPE_TABLE;
            break;

        default:
            printf("Unkown options %c", c);
            _print_cmdline_usage(argv[0]);
            return 0;
        }
    }

    // Parse the <filesystem>
    if (optind + 1 > argc) {
        printf("Please specify <filesystem>!\n");
        _print_cmdline_usage(argv[0]);
        return 0;
    }
    const char *fs_path = argv[optind];

    // try to open the squashfs image file
    if((fd = open(fs_path, O_RDONLY)) == -1) {
        printf("Could not open %s, because %s\n", fs_path, strerror(errno));
        exit(1);
    }

    // read super
    if(_mount_squashfs(fs_path) == FALSE)
        exit(1);

    _block_size = sBlk.s.block_size;
    _block_log = sBlk.s.block_log;

    /*
     * Sanity check block size and block log.
     *
     * Check they're within correct limits
     */
    if(_block_size > SQUASHFS_FILE_MAX_SIZE || _block_log > SQUASHFS_FILE_MAX_LOG)
        EXIT_UNSQUASH("Block size or block_log too large."
            "  File system is corrupt.\n");
    /*
     * Check block_size and block_log match
     */
    if(_block_size != (1 << _block_log))
        EXIT_UNSQUASH("Block size and block_log do not match."
            "  File system is corrupt.\n");

    // Read UID/GUID Table
    if(s_ops.read_uids_guids() == FALSE)
        EXIT_UNSQUASH("failed to uid/gid table\n");

    // Read Fragment Table
    long long directory_table_end;
    if(s_ops.read_fragment_table(&directory_table_end) == FALSE)
        EXIT_UNSQUASH("failed to read fragment table\n");

    // Read Inode Table
    if(_read_inode_table(sBlk.s.inode_table_start, sBlk.s.directory_table_start) == FALSE)
        EXIT_UNSQUASH("failed to read inode table\n");

    // Read Directory Table
    if(_read_directory_table(sBlk.s.directory_table_start, directory_table_end) == FALSE)
        EXIT_UNSQUASH("failed to read directory table\n");

    // Read XAttr Table
    if(read_xattrs_from_disk(fd, &sBlk.s) == 0)
        EXIT_UNSQUASH("failed to read the xattr table\n");

    _print_brief(fs_path);

    if (dump_superblock) {
        printf("------------------------------------- SUPER BLOCK ------------------------------------------\n");
        _print_super_block();
    }

    if (dump_fragment) {
        printf("-------------------------------------- FRAGMENTS --------------------------------------------\n");
        _print_fragments();
    }

    if (dump_block) {
        printf("---------------------------------------- BLOCKS ---------------------------------------------\n");
        _print_blocks();
    }

    if (dump_inode) {
        printf("---------------------------------------- INODES ---------------------------------------------\n");
        _print_inode_table(sBlk.s.inode_table_start, sBlk.s.directory_table_start);
    }

    if (dump_directory) {
        printf("------------------------------------- DIRECTORIES -------------------------------------------\n");
        _print_directory_table(sBlk.s.directory_table_start, directory_table_end);
    }

    return 0;
}
