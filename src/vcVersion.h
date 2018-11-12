#ifndef vcVersion_h__

// *_VAL have a specific requirement on windows to be in the format 0,1,2,3
// *_STR have no requirements

#define VCVERSION_BASE_VERSION_VAL 0,1,1
#define VCVERSION_BASE_VERSION_STR "0.1.1"

// These are needed to avoid having to add includes to this header- there is a dependency that it can be compiled into a Windows Resource header
#define VCNAMEASSTRING(s) #s
#define VCSTRINGIFY(s) VCNAMEASSTRING(s)

#if defined(GIT_TAG)
#  define VCVERSION_PRODUCT_VAL VCVERSION_BASE_VERSION_VAL,GIT_BUILD
#  define VCVERSION_PRODUCT_STR VCVERSION_BASE_VERSION_STR "." VCSTRINGIFY(GIT_BUILD)

#  define VCVERSION_FILEVERSION_VAL VCVERSION_BASE_VERSION_VAL,GIT_BUILD
#  define VCVERSION_FILEVERSION_STR VCVERSION_BASE_VERSION_STR "." VCSTRINGIFY(GIT_BUILD)
#elif defined(GIT_BUILD)
#  define VCVERSION_PRODUCT_VAL VCVERSION_BASE_VERSION_VAL,GIT_BUILD
#  define VCVERSION_PRODUCT_STR VCVERSION_BASE_VERSION_STR "." VCSTRINGIFY(GIT_BUILD) " (In Development / Do Not Distribute)"

#  define VCVERSION_FILEVERSION_VAL VCVERSION_BASE_VERSION_VAL,GIT_BUILD
#  define VCVERSION_FILEVERSION_STR VCVERSION_BASE_VERSION_STR "." VCSTRINGIFY(GIT_BUILD) " (In Development)"
#else
#  define VCVERSION_PRODUCT_VAL VCVERSION_BASE_VERSION_VAL,0
#  define VCVERSION_PRODUCT_STR VCVERSION_BASE_VERSION_STR " (Developer Build / Do Not Distribute)"

#  define VCVERSION_FILEVERSION_VAL VCVERSION_BASE_VERSION_VAL,0
#  define VCVERSION_FILEVERSION_STR VCVERSION_BASE_VERSION_STR ".0 (Developer Build)"
#endif //GIT_BUILD

#define VCVERSION_WINDOW_TITLE "Euclideon Vault Client " VCVERSION_PRODUCT_STR " - (Built: " __DATE__ ")"

#endif
