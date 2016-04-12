//
//  main.h
//  Efficient Compression Tool
//
//  Created by Felix Hanau on 02.01.15.
//  Copyright (c) 2015 Felix Hanau.
//

#include <cstdio>
#include <cstdlib>
#include <string>
#include <cstring>
#include <vector>
#include <climits>

#include "gztools.h"

//Compile support for folder input. Requires linking of Boost::filesystem and Boost::system.
#ifdef BOOST_SUPPORTED
#include <boost/filesystem.hpp>
#endif

struct ECTOptions{
  unsigned  Mode;
  bool strip;
  bool Progressive;
  bool JPEG_ACTIVE;
  bool PNG_ACTIVE;
  bool SavingsCounter;
  bool Strict;
  bool Arithmetic;
  bool Gzip;
  bool Zip;
  bool Reuse;
  bool Allfilters;
#ifdef BOOST_SUPPORTED
  bool Recurse;
#endif
  unsigned DeflateMultithreading;
  unsigned Iterations;
  unsigned Stagnations;
};

int Optipng(unsigned filter, const char * Infile, bool force_no_palette, int nda);
int Zopflipng(bool strip, const char * Infile, bool strict, unsigned Mode, int filter, unsigned multithreading, unsigned iterations, unsigned stagnations);
int mozjpegtran (bool arithmetic, bool progressive, bool strip, const char * Infile, const char * Outfile);
int ZopfliGzip(const char* filename, const char* outname, unsigned mode, unsigned multithreading, unsigned ZIP, unsigned iterations, unsigned stagnations);
