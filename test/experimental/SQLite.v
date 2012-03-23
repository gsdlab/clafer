import env;

concept SQLite
{
	mandatory abstract feature Parameters {
		//This macro determines if SQLite creates databases with the auto_vacuum flag set by default to OFF (0), FULL (1), or INCREMENTAL (2). The default value is 0 meaning that databases are created with auto-vacuum turned off. In any case the compile-time default may be overridden by the PRAGMA auto_vacuum command.
		//<0 or 1 or 2>
		int SQLITE_DEFAULT_AUTOVACUUM=0;

		//This macro sets the default size of the page-cache for each attached database, in pages. This can be overridden by the PRAGMA cache_size command. The default value is 2000.
		//<pages>
		int SQLITE_DEFAULT_CACHE_SIZE=2000;		

		//The default schema-level file format used by SQLite when creating new database files is set by this macro. The file formats are all very similar. The difference between formats 1 and 4 is that format 4 understands descending indices and has a tighter encoding for boolean values.
		//SQLite (as of version 3.6.0) can read and write any file format between 1 and 4. But older versions of SQLite might not be able to read formats greater than 1. So that older versions of SQLite will be able to read and write database files created by newer versions of SQLite, the default file format is set to 1 for maximum compatibility.
		//The file format for a new database can be set at runtime using the PRAGMA legacy_file_format command.
		//<1 or 4>
		int SQLITE_DEFAULT_FILE_FORMAT=1;	

		//This macro determines whether enforcement of foreign key constraints is enabled or disabled by default for new database connections. Each database connection can always turn enforcement of foreign key constraints on and off and run-time using the foreign_keys pragma. Enforcement of foreign key constraints is normally off by default, but if this compile-time parameter is set to 1, enforcement of foreign key constraints will be on by default.
		//<0 or 1>
		int SQLITE_DEFAULT_FOREIGN_KEYS=0;		

		//This option sets the size limit on rollback journal files in persistent journal mode. When this compile-time option is omitted there is no upper bound on the size of the rollback journal file. The journal file size limit can be changed at run-time using the journal_size_limit pragma.
		//<bytes>
		int SQLITE_DEFAULT_JOURNAL_SIZE_LIMIT=0;	//0xFFFFFFFF;
		
		//This macro is used to determine whether or not the features enabled and disabled using the SQLITE_CONFIG_MEMSTATUS argument to sqlite3_config() are available by default. The default value is 1 (SQLITE_CONFIG_MEMSTATUS related features enabled).
		//<1 or 0>
		int SQLITE_DEFAULT_MEMSTATUS=1;
		
		//This macro is used to set the default page-size used when a database is created. The value assigned must be a power of 2. The default value is 1024. The compile-time default may be overridden at runtime by the PRAGMA page_size command.
		//<bytes> (power of 2)
		int SQLITE_DEFAULT_PAGE_SIZE=1024;
		
		//This macro sets the default size of the page-cache for temporary files created by SQLite to store intermediate results, in pages. It does not affect the page-cache for the temp database, where tables created using CREATE TEMP TABLE are stored. The default value is 500.
		//<pages>
		int SQLITE_DEFAULT_TEMP_CACHE_SIZE=500;

		//This macro sets the default page count for the WAL automatic checkpointing feature. If unspecified, the default page count is 1000.
		//<pages>
		int SQLITE_DEFAULT_WAL_AUTOCHECKPOINT=1000;

		//This macro sets the maximum depth of the LALR(1) stack used by the SQL parser within SQLite. The default value is 100. A typical application will use less than about 20 levels of the stack. Developers whose applications contain SQL statements that need more than 100 LALR(1) stack entries should seriously consider refactoring their SQL as it is likely to be well beyond the ability of any human to comprehend.
		//<max_depth>
		int YYSTACKDEPTH=100;
    }

    mandatory abstract feature EnableFeatures
    {
        feature SQLITE_ENABLE_FTS3_PARENTHESIS;
        feature SQLITE_ENABLE_FTS3;
        feature SQLITE_ENABLE_COLUMN_METADATA;
        feature SQLITE_ENABLE_ATOMIC_WRITE;
        feature YYTRACKMAXSTACKDEPTH;
        feature SQLITE_SOUNDEX;
        feature SQLITE_ENABLE_UNLOCK_NOTIFY;
        feature SQLITE_ENABLE_UPDATE_DELETE_LIMIT;
        feature SQLITE_ENABLE_STAT2;
        feature SQLITE_ENABLE_RTREE;
        abstract feature ChooseMemSys
        {
        someof {
            feature SQLITE_ENABLE_MEMSYS3;
            feature SQLITE_ENABLE_MEMSYS5;
        }
        } //ChooseMemSys

        feature SQLITE_ENABLE_MEMORY_MANAGEMENT;
        feature SQLITE_ENABLE_ICU;
    } //EnableFeatures

    mandatory abstract feature OperatingCharacteristics
    {
        //On most systems, the malloc() system call returns a buffer that is aligned to an 8-byte boundary. But on some systems (ex: windows) malloc() returns 4-byte aligned pointer. This compile-time option must be used on systems that return 4-byte aligned pointers from malloc().
        mandatory feature SQLITE_4_BYTE_ALIGNED_MALLOC;
        
		//This compile-time option changes the default setting of the secure_delete pragma. When this option is not used, secure_delete defaults to off. When this option is present, secure_delete defaults to on.
		//The secure_delete setting causes deleted content to be overwritten with zeros. There is a small performance penalty for this since additional I/O must occur. On the other hand, secure_delete can prevent sensitive information from lingering in unused parts of the database file after it has allegedly been deleted. See the documentation on the secure_delete pragma for additional information.
        feature SQLITE_SECURE_DELETE;
        
        //The option causes SQLite to omit its built-in operating system interfaces for Unix, Windows, and OS/2. The resulting library will have no default operating system interface. Applications must use sqlite3_vfs_register() to register an appropriate interface before using SQLite. Applications must also supply implementations for the sqlite3_os_init() and sqlite3_os_end() interfaces. The usual practice is for the supplied sqlite3_os_init() to invoke sqlite3_vfs_register(). SQLite will automatically invoke sqlite3_os_init() when it initializes.
		//This option is typically used when building SQLite for an embedded platform with a custom operating system.
		//<0 or 1>
		int SQLITE_OS_OTHER=0;
        
        //If this option is present, then SQLite will use the isnan() function from the system math library. Without this option (the default behavior) SQLite uses its own internal implementation of isnan(). SQLite uses its own internal isnan() implementation by default because of past problems with system isnan() functions.
        feature SQLITE_HAVE_ISNAN;
        
        //If this option is present, then the built-in LIKE operator will be case sensitive. This same effect can be achieved at run-time using the case_sensitive_like pragma.
        feature SQLITE_CASE_SENSITIVE_LIKE;
             
        /*   
			This option controls whether or not code is included in SQLite to enable it to operate safely in a multithreaded environment. The default is SQLITE_THREADSAFE=1 which is safe for use in a multithreaded environment. When compiled with SQLITE_THREADSAFE=0 all mutexing code is omitted and it is unsafe to use SQLite in a multithreaded program. When compiled with SQLITE_THREADSAFE=2, SQLite can be used in a multithreaded program so long as no two threads attempt to use the same database connection at the same time.
			To put it another way, SQLITE_THREADSAFE=1 sets the default threading mode to Serialized. SQLITE_THREADSAFE=2 sets the default threading mode to Multi-threaded. And SQLITE_THREADSAFE=0 sets the threading mode to Single-threaded.
			The value of SQLITE_THREADSAFE can be determined at run-time using the sqlite3_threadsafe() interface.
			When SQLite has been compiled with SQLITE_THREADSAFE=1 or SQLITE_THREADSAFE=2 then the threading mode can be altered at run-time using the sqlite3_config() interface together with one of these verbs:
				SQLITE_CONFIG_SINGLETHREAD
				SQLITE_CONFIG_MULTITHREAD
				SQLITE_CONFIG_SERIALIZED
			The SQLITE_OPEN_NOMUTEX and SQLITE_OPEN_FULLMUTEX flags to sqlite3_open_v2() can also be used to adjust the threading mode of individual database connections at run-time.
			Note that when SQLite is compiled with SQLITE_THREADSAFE=0, the code to make SQLite threadsafe is omitted from the build. When this occurs, it is impossible to change the threading mode at start-time or run-time.
			See the threading mode documentation for additional information on aspects of using SQLite in a multithreaded environment.
			<0 or 1 or 2>
		*/
		int SQLITE_THREADSAFE=1;

		/*
			This option controls whether temporary files are stored on disk or in memory. The meanings for various settings of this compile-time option are as follows:

			SQLITE_TEMP_STORE	Meaning
			0	Always use temporary files
			1	Use files by default but allow the PRAGMA temp_store command to override
			2	Use memory by default but allow the PRAGMA temp_store command to override
			3	Always use memory
			The default setting is 1. Additional information can be found in tempfiles.html.
			
			<0..3>
		*/
		int SQLITE_TEMP_STORE=1;
    } //OperatingCharacteristics

    mandatory abstract feature OmitFeatures
    {
        feature SQLITE_OMIT_ALTERTABLE;
        feature SQLITE_OMIT_COMPOUND_SELECT;
        feature SQLITE_OMIT_COMPLETE;
        feature SQLITE_OMIT_COMPILEOPTION_DIAGS;
        feature SQLITE_OMIT_CHECK;
        feature SQLITE_OMIT_CAST;
        feature SQLITE_OMIT_BUILTIN_TEST;
        feature SQLITE_OMIT_BTREECOUNT;
        feature SQLITE_OMIT_BLOB_LITERAL;
        feature SQLITE_OMIT_BETWEEN_OPTIMIZATION;
        feature SQLITE_OMIT_AUTOVACUUM;
        feature SQLITE_OMIT_AUTOINIT;
        feature SQLITE_OMIT_AUTOMATIC_INDEX;
        feature SQLITE_OMIT_AUTOINCREMENT;
        feature SQLITE_OMIT_AUTHORIZATION;
        feature SQLITE_OMIT_ATTACH;
        feature SQLITE_OMIT_ANALYZE;
        feature SQLITE_OMIT_LOOKASIDE;
        feature SQLITE_OMIT_LOCALTIME;
        feature SQLITE_OMIT_LOAD_EXTENSION;
        feature SQLITE_OMIT_LIKE_OPTIMIZATION;
        feature SQLITE_OMIT_INTEGRITY_CHECK;
        feature SQLITE_OMIT_INCRBLOB;
        feature SQLITE_OMIT_GET_TABLE;
        feature SQLITE_OMIT_FOREIGN_KEY;
        feature SQLITE_OMIT_FLOATING_POINT;
        feature SQLITE_OMIT_FLAG_PRAGMAS;
        feature SQLITE_OMIT_EXPLAIN;
        feature SQLITE_OMIT_DISKIO;
        feature SQLITE_OMIT_DEPRECATED;
        feature SQLITE_OMIT_DECLTYPE;
        feature SQLITE_OMIT_DATETIME_FUNCS;
        feature SQLITE_OMIT_CONFLICT_CLAUSE;
        feature SQLITE_OMIT_TRUNCATE_OPTIMIZATION;
        feature SQLITE_OMIT_TRIGGER;
        feature SQLITE_OMIT_TRACE;
        feature SQLITE_OMIT_TEMPDB;
        feature SQLITE_OMIT_TCL_VARIABLE;
        feature SQLITE_OMIT_SUBQUERY;
        feature SQLITE_OMIT_SHARED_CACHE;
        feature SQLITE_OMIT_SCHEMA_VERSION_PRAGMAS;
        feature SQLITE_OMIT_SCHEMA_PRAGMAS;
        feature SQLITE_OMIT_REINDEX;
        feature SQLITE_OMIT_QUICKBALANCE;
        feature SQLITE_OMIT_PROGRESS_CALLBACK;
        feature SQLITE_OMIT_PRAGMA;
        feature SQLITE_OMIT_PAGER_PRAGMAS;
        feature SQLITE_OMIT_OR_OPTIMIZATION;
        feature SQLITE_OMIT_MEMORYDB;
        feature SQLITE_OMIT_XFER_OPT;
        feature SQLITE_OMIT_WSD;
        feature SQLITE_OMIT_WAL;
        feature SQLITE_OMIT_VIRTUALTABLE;
        feature SQLITE_OMIT_VIEW;
        feature SQLITE_OMIT_VACUUM;
        feature SQLITE_OMIT_UTF16;
    } //OmitFeatures

    mandatory abstract feature DisableFeatures
    {
        feature SQLITE_DISABLE_DIRSYNC;
        feature SQLITE_DISABLE_LFS;
    } //DisableFeatures

	mandatory abstract feature Debug
	{
		feature SQLITE_MEMDEBUG;
		feature SQLITE_DEBUG;
	}
} //SQLite

