################################################
#  NB: This Makefile is designed to be called  #
#      from the main PRISM Makefile. It won't  #
#      work on its own because it needs        #
#      various options to be passed in         #
################################################

.SUFFIXES: .o .c .cc

# Reminder: $@ = target, $* = target without extension, $< = dependency

THIS_DIR = odd
PRISM_DIR_REL = ../..

INCLUDES = \
-I$(PRISM_DIR_REL)/$(CUDD_DIR)/include \
-I"$(JAVA_JNI_H_DIR)" \
-I"$(JAVA_JNI_MD_H_DIR)" \
-I$(PRISM_DIR_REL)/$(PRISM_INCLUDE_DIR)

LIBRARIES = \
-L$(PRISM_DIR_REL)/$(PRISM_LIB_DIR) \
-ldd

JNI_GEN_HEADER_DIR=$(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_INCLUDE_DIR)/jni

JAVA_FILES_ALL = $(wildcard *.java)
JAVA_FILES = $(subst package-info.java,,$(JAVA_FILES_ALL))
CLASS_FILES = $(JAVA_FILES:%.java=$(PRISM_DIR_REL)/$(PRISM_CLASSES_DIR)/$(THIS_DIR)/%.class)

CC_FILES = $(wildcard *.cc)
O_FILES = $(CC_FILES:%.cc=$(PRISM_DIR_REL)/$(PRISM_OBJ_DIR)/$(THIS_DIR)/%.o)

PRISM_CLASSPATH = "$(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_CLASSES_DIR)$(CLASSPATHSEP)$(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_LIB_DIR)/*"

default: all

all: checks $(CLASS_FILES) $(PRISM_DIR_REL)/$(PRISM_LIB_DIR)/$(LIBPREFIX)odd$(LIBSUFFIX)

# inhibit building in parallel (-j option)
.NOTPARALLEL:

# Try and prevent accidental makes (i.e. called manually, not from top-level Makefile)
checks:
	@if [ "$(PRISM_SRC_DIR)" = "" ]; then \
	  (echo "Error: This Makefile is designed to be called from the main PRISM Makefile"; exit 1) \
	fi; 

$(PRISM_DIR_REL)/$(PRISM_CLASSES_DIR)/$(THIS_DIR)/%.class: %.java
	(cd ..; $(JAVAC) $(JFLAGS) -sourcepath $(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_SRC_DIR) -classpath $(PRISM_CLASSPATH) -h $(JNI_GEN_HEADER_DIR) -d $(THIS_DIR)/$(PRISM_DIR_REL)/$(PRISM_CLASSES_DIR) $(THIS_DIR)/$<)

$(PRISM_DIR_REL)/$(PRISM_LIB_DIR)/$(LIBPREFIX)odd$(LIBSUFFIX): $(O_FILES)
	$(LD) $(SHARED) $(LDFLAGS) -o $@ $(O_FILES) $(LIBRARIES)

$(PRISM_DIR_REL)/$(PRISM_OBJ_DIR)/$(THIS_DIR)/%.o: %.cc
	$(CXX) $(CXXFLAGS) -c $< -o $@ $(INCLUDES)

clean: checks
	@rm -f $(CLASS_FILES) $(PRISM_DIR_REL)/$(PRISM_LIB_DIR)/$(LIBPREFIX)odd$(LIBSUFFIX) $(O_FILES)

celan: clean

#################################################
