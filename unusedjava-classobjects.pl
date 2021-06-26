#!/usr/bin/perl

$path = "./output";
use Cwd;
use File::Find;
Main();

sub Main
{
 OMParse();
}

sub OMParse()
{
  my @inputfiles = ();
  my $unusedvariableEnabled = 0;
  my $usedvariableEnabled = 0;
  my @ClsDomain = ();
  my $finalline = "";
  my @MethodInfo = ();
  my @ClassInfo = ();
  my @UsedInfo = ();
  my @ClsDomain = ();
  my @D = ();
  my @SusVar = ();
  OpenFiles();                            #Open Input and Temp files
  InitializeGlobalHashTables();           #Initialize Global Hash Tables for storage
  #@inputfiles  = ProcessCommandLineArgs(); # Process Command Line Arguments
  $jfile  = ProcessCommandLineArgs(); # Process Command Line Arguments
  #@chlines     = StripCmntsAndUpdateLineTags(@inputfiles);
  @chlines     = StripCmntsAndUpdateLineTags($jfile);
  @chlines1    = @chlines;
  @chlines     = MethodandClassRecg(@chlines);
  $finalline   = SupressNewlineTabsSpaces(@chlines);
  ($MethodInfo,$ClassInfo,  $UsedInfo)= MaintainMethodAndClassHashTables($finalline);
  @MethodInfo  = @{$MethodInfo};
  @ClassInfo   = @{$ClassInfo};
  @UsedInfo    = @{$UsedInfo};
  @Domains     = MaintianBraceHash($finalline);
  ($D,$ClsDomain) = ValidateDomain(\@Domains,\@MethodInfo,\@ClassInfo);
  @D              = @{$D};
  @ClsDomain      = @{$ClsDomain};
  @chlines    = CleanFileTransilationalUnit(@chlines1);
  @SusVar         = CleanLocalTransilationalUnit(@chlines);
  ExtractGlobalVariables(\@SusVar,\@ClsDomain,\@D);         # extract_Globalobjects
  @localmethods   = ExtractLocalVariables(\@D,\@ClsDomain);#Localscopevalidation
  MethodDomains(@localmethods);
 #checkinmethodhashtable(3,\@D);
  processLocalvariables ();
  ReferenceProcess(@localmethods);
#   print ">>Parsing Expression Semantics For References [$count1/$len], $ref...\n";
}
sub ProcessCommandLineArgs
{
 $opt = shift (@ARGV);
 $fileno = shift(@ARGV);
 $filecount = shift(@ARGV);
 $jfile = shift(@ARGV);
 $outputdirectory = shift(@ARGV);

 @opts = split(//,$opt);
 $unusedclassesEnabled = 0;
 $usedclasseEnabled = 0;
 foreach $o (@opts)
 {
   if($o eq "u")
   {
     $usedclasseEnabled = 1;
   }
   if($o eq "n")
   {
      $unusedclassesEnabled = 1;
   }
 }
 $outputdirectory =~ s/\\/\//g;
 $jfile =~ s/\\/\//g;

=b
  my @inputfiles = ();
  $opt = shift (@ARGV);
  @opts = split(//,$opt);
  foreach $o (@opts)
  {
    if($o eq "u")
   {
     $usedvariableEnabled = 1;
   }
   if($o eq "n")
     {
     $unusedvariableEnabled = 1;
   }
  }
  if($interfaceflag == 1)
  {
   $regflag = 0;
   $opt1 = shift (@ARGV);
   $opt2 = shift (@ARGV);
   $count = $opt1;
   $filecount = $opt2;
   $count = trim ($count);
   $filecount = trim ($filecount);
  }
 # if ($filecount eq $count)
 # {
  #  parsingobjcrossreferences();
 # }
  foreach $infile(@ARGV)
  {
    push(@inputfiles,$infile);
  }
  $outputdirectory = pop(@inputfiles);
return(@inputfiles);
=cut
return $jfile;
}
 $junkfile ="$path/junk.verbose";
 $inter_file ="$path/ver.i";
sub OpenFiles
{
  $junkfile ="$path/junk.verbose";
  $temp ="$path/Temp.verbose";# Globalrefs
 # open(I, "> $inter_file" ) or die "could not open $inter_file...\n ";
  open(JK, "> $junkfile" ) or die "could not open $junkfile...\n ";
  open(JKK, ">> $temp" ) or die "could not open $temp...\n ";
}

sub InitializeGlobalHashTables()
{
  %Object_declared = ();
  %Object_declaredlocal = ();
  %Function_var = ();
  %ClassVar = ();
}

sub StripCmntsAndUpdateLineTags(@)
{
  # my @inputfiles = @_;
  my $jfile = shift;
  my @chlines = ();
  # foreach my $jfile (@inputfiles)
  # {
  #   while($jfile =~ /\\/g)
  #    {
  #     $findstr = $1;
  #     $replacestr = "/";
  #     $jfile =~ s/$findstr/$replacestr/g;
  #    }
     #print "PRINT FILENAME :$jfile\n";
     open(CH, "< $jfile" ) or die "could not open $jfile...\n ";
     print(">>  processing $jfile [$filecount/$fileno]\n");
     $inter_file ="$path/ver.i";
     open(I,  "> $inter_file" ) or die "could not open $inter_file...\n ";
     @chlines = <CH>;
     close(CH);
     @chlines = strip_C_CPP_CHASH_JAVA_cmts(@chlines);
     foreach $line(@chlines)
     {
      $ln_inter++;
      print I "<$ln_inter> $line";
     }
     close(I);
     unlink(I);
     $tempfile = $jfile ;
 # }
     $jfile = $tempfile;
     return(@chlines);
}


# PASS 1 - Start Preprocessing - Remove Comments:

sub strip_C_CPP_CHASH_JAVA_cmts(@)
{

   my @tlines = @_;
   push(@tlines, "\n");
   my @chlines =();
   foreach my $l (@tlines)
   {
      # processing C and C++ Style comments
      if($l =~ /\/\*/g)
      {
         $l =~ s/\/\*/\/\* /g;
      }
      if($l =~ /\*\//g)
      {
         $l =~ s/\*\// \*\//g;
      }
      if($l =~ (/\/\/.*/))
      {
        $l =~ s/$1//g;
      }
      $l =~ s/\n/ <NEWLINE>/g;
      @lexicaltokens = split(/\s+/, $l);
      foreach my $token (@lexicaltokens)
      {
       if($token =~ /<NEWLINE>/)
        {
         $filelines = "$filelines"."\n";
         push(@chlines, $filelines);
         $filelines = "";
        }
        elsif($token =~ /\/\*/g)   # C, C++, JAVA, CSHARP
        {
         $start_C_CPP_JAVA_CHASH_cmt = 1;
         $filelines = "$filelines"."$token";
        }
        elsif($token =~ /\*\//g)
        {
         $start_C_CPP_JAVA_CHASH_cmt = 0;
         $filelines = "$filelines"."$token";
        }
        elsif($start_C_CPP_JAVA_CHASH_cmt eq 1)
        {
          $token = " ";
          $filelines = "$filelines"."$token ";
        }
        else
        {
          $filelines = "$filelines"."$token ";
        }
      }

   }
  return(@chlines);
}
sub MethodandClassRecg(@)
{
   my @clmt_lines = @_;
   $lineno_cl = 0;

   foreach my $line_cl (@clmt_lines)
   {
       $lineno_cl++;
     # Suspecious tag for Opens.
     while($line_cl =~ m/([a-zA-Z0-9_]+)\s*\(/g)
     {
      print;
      $function = $1;
      $replace = "<$lineno_cl>"."$function"."<METHOD>";
      $line_cl =~ s/\b$function\b/$replace/g;
     }
     while ( $line_cl =~ m/(class)/g)
     {
      $class_name    = $1;
      $replace_class = "<$lineno_cl> "."<CLASS>";
      $line_cl =~ s/$class_name/$replace_class/g;
     }
     #*****RegExp  is like this for identifying  (new).

     while ( $line_cl =~ m/(new)/g)
     {
      $new_name = $1;
      $replace_new = "<$lineno_cl> "."<NEW> ";
      $line_cl =~ s/\b$new_name\b/$replace_new/g;
     }
     #*****RegExp  is like this for identifying  (extends).
     while ( $line_cl =~ m/(extends)/g)
     {
      $extends_name = $1;
      $extends_name = trim($extends_name);
      $replace_extends = "<$lineno_cl> "."<EXTENDS> ";
      $line_cl =~ s/\b$extends_name\b/$replace_extends/g;
     }
     #*****RegExp  is like this for identifying  .forName ("Package.A")(Class.forName).
     while ( $line_cl =~ /(forName)/g)
     {
      $forname_name = $1;
      $forname_name = trim($forname_name);
      $replace_forname = "<$lineno_cl>"."<FORNAME>";
      $line_cl =~ s/\b$forname_name\b/$replace_forname/g;
     }
     #*****RegExp  is like this for identifying .loadClass("Package.A").
     while ( $line_cl =~ m/(loadClass)/g)
     {
      $loadclass_name = $1;
      $loadclass_name = trim($loadclass_name);
      $replace_loadclass = "<$lineno_cl>"."<LOADCLASS>";
      $line_cl =~ s/\b$loadclass_name\b/$replace_loadclass/g;
     }
     #*****RegExp  is like this for identifying { (openbrace).
     while($line_cl =~ /(\{)/g)
     {
      $OpenBrace = $1;
      $replaceOBrace = "<$lineno_cl>"."<OB> ";
      $line_cl =~ s/$OpenBrace/$replaceOBrace/g;
     }
     #*****RegExp  is like this for identifying } (closebrace).
     while($line_cl =~ /(\})/g)
     {
      $CloseBrace = $1;
      $replaceCBrace = "<$lineno_cl>"."<CB> ";
      $line_cl =~ s/$CloseBrace/$replaceCBrace/g;
     }
}
return(@clmt_lines);
}

sub SupressNewlineTabsSpaces(@)
{
  my  @singleline = @_;
   foreach $l (@singleline)
   {
    $fline_single = "$fline_single"."$l";
   }
   $finalline_single = $fline_single;
   $fline_single = "";
   $finalline_single =~ s/\n/ /g;
   $finalline_single =~ s/\t/ /g;
   $finalline_single =~ s/\s+/ /g;


   #MaintainMethodAndClassHashTables($finalline_single);

   #$finalline_single2 = $finalline_single1;

   #MaintianBraceHash($finalline_single1);
 return($finalline_single)
}

sub MaintainMethodAndClassHashTables($)
{
   my $finalline_single = shift;
   my @ClassDefs = ();
   my @UsedInfo = ();
   my @ClassInfo = ();
   while($finalline_single =~ /\(\s*\<[0-9]+\>\w+\<METHOD\>/g)
   {
    $finalline_single =~ s/\(\s*\<[0-9]+\>\w+\<METHOD\>/\(/g;
   }
   while(($finalline_single =~ /(\.\<[0-9]+\>\w+\<METHOD\>)/g) ||($finalline_single1 =~ /(\!\<[0-9]+\>\w+\<METHOD\>)/g))
   {
    $finalline_single =~ s/\!\<[0-9]+\>\w+\<METHOD\>//g;
    $finalline_single =~ s/\.\<[0-9]+\>\w+\<METHOD\>//g;
   }
   #while( $finalline_single =~ /\<([0-9]+)\>\s*([a-z-A-Z-0-9_]+)\s*(\<METHOD\>)\s*(\([a-zA-Z0-9_,\)\(\[\] ]*\))\s*([a-zA-Z0-9 ]*)\s*(\<[0-9]+\>)\s*(\<OB\>)/g)
   while($finalline_single =~ /(\<[0-9]+\>)\s*([\w]+)\s*(\<METHOD\>)\s*(\([a-zA-Z0-9_,\)\(\[\] ]*\))\s*(\<[0-9]+\>)\s*(\<OB\>)/g)
   {
    $MethodLine = $1;
    $MethodLine = trim($MethodLine);
    $MethodName = $2;
    $MethodName = trim($MethodName);
    $MethodParameters = $4;
    $MethodParameters = trim($MethodParameters);
    $OBMethodLine = $5;
    $OBMethodLine = trim($OBMethodLine);
    $MethodDetails = "$MethodLine"."#"."$MethodName"."#"."$MethodParameters"."#"."$OBMethodLine"."#"."OB";
    push(@MethodInfo , $MethodDetails);
   }
   while($finalline_single =~ /\<([0-9]+)\>\s*<CLASS>\s*(\w+)\s*(\<*)([0-9]*)(\>*)\s*(\w*)\s*(\<*)[a-zA-Z0-9_, ]*(\>*)\s*[a-zA-Z0-9_, ]*\s*(\<[0-9]+\>)\s*<OB>/g)
   {
    $ClassLine  = $1;
    $ClassLine  = trim($ClassLine );
    $ClassName = $2;
    $ClassName = trim($ClassName);
    $OBClassLine = $9;
    $OBClassLine = trim($OBClassLine);
    if($jfile =~ /(^.*\/)(.*)/)
     {
      $dirpath =$1;
      $dirpath = trim($dirpath);
      $filename = $2;
      $filename = trim($filename);
     }
     $currentfilename;
     $ClassDetails = "$ClassLine"."#"."$ClassName"."#"."$OBClassLine"."#"."OB";
     push(@ClassInfo , $ClassDetails);
     $ClassDef ="$ClassName"."#"."$ClassLine"."#"."$jfile"."#"."$currentfilename";
     $Classkey = "$ClassName"."#"."$ClassLine";
     push(@ClassDefs,$ClassDef);
     push( @{$ClassDefinitions{$Classkey}}, $ClassLine); # Add lineno and filenames into table.
     push( @{$ClassDefinitions{$Classkey}},$jfile );

   }
   while($finalline_single =~ /\<([0-9]+)\>\s*<CLASS>\s*([a-zA-Z0-9-,$._]+)\s*\<([0-9]+)\>\s*<EXTENDS>\s*([a-zA-Z0-9-,$._]+)/g)
   {
    $subclsname     = $2;
    $subclsname     = trim($subclsname);
    $extendsatlno   = $3;
    $extendsatlno   =  trim($extendsatlno);
    $superclsname   =  $4;
    $superclsname   =  trim($superclsname);
    $extendsDetails = "$subclsname"."#"."$extendsatlno"."#"."$superclsname"."#"."$jfile";
    push( @{$UsedClasses_extends{$extendsDetails}}, $jfile); # Add lineno and filenames into table.
    push( @{$UsedClasses_extends{$extendskey}},$jfile );
   }
   while($finalline_single =~ /([a-zA-Z0-9-,$._]+)\s*\=\s*\<([0-9]+)\>\s*<NEW>\s*\<([0-9]+)\>([a-zA-Z0-9-,$._]+)/g)
   {
    $objectname  = $1;
    $objectname  = trim($objectname);
    $newlno      = $2;
    $newlno      = trim($newlno);
    $clsname     = $4;
    $clsname     = trim($clsname);
    $newDetails = "$objectname"."#"."$newlno"."#"."$clsname"."#"."$jfile";
    push(@UsedInfo , $newDetails);
    push( @{$UsedClasses_new{$newkey}}, $newDetails); # Add lineno and filenames into table.
    push( @{$UsedClasses_new{$newDetails}},$jfile );
   }
   return(\@MethodInfo,\@ClassInfo,\@UsedInfo);
}

sub  MaintianBraceHash($)
{
  my $finalline = shift;
  my @Domains= ();
  my @tokens = split(/\s/,$finalline_single) ;
  foreach $token (@tokens)
   {
    if($token =~ /(\<[0-9]+\>)\<CB\>/)
     {
      push(@Close, $1);
      $CloseFlag = 1;
     }
     if($token =~ /(\<[0-9]+\>)\<OB\>/)
     {
      push(@Open, $1);
     }
     if($CloseFlag eq 1)
     {
      $Openlineno = pop(@Open);
      $Closelineno = pop(@Close);
      $CloseFlag = 0;
      if($jfile =~ /(^.*\/)(.*)/)
       {
        $dirpath =$1;
        $dirpath = trim($dirpath);
        $filename1 = $2;
        $filename1 = trim($filename1);
       }
      $Domain = "$Openlineno".":"."$Closelineno";
      push (@Domains, $Domain);
     }
   }
return(@Domains);
}

sub ValidateDomain (@Domains,@MethodInfo,@ClassInfo)
{
  my $Domains    = shift;
  my $MethodInfo = shift;
  my $ClassInfo  = shift;
 #  my $UsedInfo   = shift;
  my @Domains    = @{$Domains};
  my @MethodInfo = @{$MethodInfo};
  my @ClassInfo  = @{$ClassInfo};
  my  @ClsDomain =();
  my @D = ();
  foreach $testdomain (@Domains)
  {
   if($testdomain =~ /(\<[0-9]+\>)\:(\<[0-9]+\>)/)
   {
     $TestOpen = $1;

     foreach my $ml (@MethodInfo)
     {
      if($ml =~ /\<([0-9]+)\>\#(.*)\#(.*)\#(\<[0-9]+\>)\#(OB)/)
       {
         $f_name = $2;
         $x = $1;
         $OB = $4;
         if($OB eq $TestOpen)
         {
           push( @{$MethodHash{$ml}},$testdomain );
           push( @{$MethodHash{$ml}},$jfile );
           if($testdomain =~ /\<([0-9]+)\>\:\<([0-9]+)\>/)
           {
              $y = $2;
              $y = trim($y);
              $z ="$f_name:<$x:$y>";
              $z = trim($z);
              push(@D,$z);
           }
         }
       }
     }
     foreach my $cl (@ClassInfo)
     {
       if($cl =~ /(\w+)\#(\<[0-9]+\>)(\#)(OB)/)
        {
         $OBforclass = $2;
         $clname = $1;
         if($OBforclass eq $TestOpen)
         {
           $clsdmn =$clname."#"."$testdomain";
           push( @ClsDomain,$clsdmn);
           push( @{$ClassHash{$cl}},$testdomain );
           push( @{$ClassHash{$cl}},$jfile );
         }
       }
     }
   }
  }
return(\@D,\@ClsDomain);
}

sub ExtractLocalVariables(@)
{
   my $D = shift;
   my @D =@{$D};
   my @t =();
   my @lines_local   = ();
   my @file_funlines = ();
   my @templines_local =();
   my @V   = ();
   my @dec = ();
   my @multivar = ();
   my @dec_details = ();
   my $bk1 = "";
   my $dtype = "";
   my $localdata = "";
   my @Localvar = ();
   my @localmethods = ();
   my $bwparam= "";
   my $multiple_dec= "";
   my $ln = "";
   my $ln1 = "";
   my $dtype1 = "";
   my $var_m = "";
  # Colecting  Local  Variables:
  $localline = "$path/Localvariables.l" ;
  open(LOCAL ,">> $localline" )or die "could not open $localline...\n ";
  # Reading intermediate file:
  open(IF, "< $inter_file" ) or die "could not open $inter_file...\n ";
  @lines_local = <IF>;
  close(IF);
  unlink ($inter_file);
  foreach  my $r (@D)
  {
    @t = ();
    #Funname:<StartLineno : EndLineno>
    if($r =~ /(\w+)\:\<([0-9]+)\:([0-9]+)\>/ )
     {
      $currentfname = $1;
      if(($currentfname eq "if")||($currentfname eq "catch")||($currentfname eq "while")||($currentfname eq "for")||($currentfname eq "switch")||($currentfname eq "catch"))
      {
         next;
      }
      push(@localmethods,$r);
      $a_1          = $2;#startlno
      $a1           = "<$a_1>";
      $b_1          = $3;#endlno
      $c_1          = $b_1+1;
      $c1           = "<$c_1>";
     }
     foreach  my $t_lscope(@lines_local)
     {
       $ln_i++;
       $ln_i1 = "<$ln_i>";
       if($ln_i1 eq $a1)
       {
        $flag = 1;
       }
       if($ln_i1 eq $c1)
       {
        $flag = 0;
        $ln_i = 0 ;
        last;
       }
#       if($t_lscope =~ /(\".*\")/)
#       {
#         $findstr = $1;
#         $t_lscope =~ s/$findstr/\"\"/g;
#       }
       if( $flag == 1)
       {
        push(@t ,$t_lscope); # lines of a function  with lineno;
        print;
        push(@file_funlines,$t_lscope);
       }
     }# for @lines_local
    foreach my $t_line (@t)
    {
     if( $t_line =~ /\;/)
     {
      $repsem = " <SEM> ;";
      $t_line =~ s/;/$repsem/g ;
     }
     $fline_local = "$fline_local"."$t_line";
    } # for@t
    $finalline_local = $fline_local;
    $fline_local = "";
    $finalline_local =~ s/\n/ /g;
    $finalline_local =~ s/\t/ /g;
    @templines_local = split("\;",$finalline_local);
    
    foreach my $z(@templines_local)
    {
      $z =~ s/\".*\"//g;
      $z =~ s/\(/ \( /g ;
      $z =~ s/\,/ \, /g ;
      $z =~ s/\)/ \) /g ;
      while($z =~ /([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\s*([\=]*)\s*([A-Za-z0-9]*)/g)
      {
         $bk = $`;
         $dtype    = $1;
         $dtype    = trim ($dtype);
         $localvar = $2;
         $localvar = trim ($localvar);
         $inits    = $4;
         $inits    = trim ($inits);
         if($inits eq "")
         {
          $inits = "_";
         }
         $bk = reverse($bk);
         if($bk =~ /(>[0-9]+<)/)
         {
            $ln = $1;
            $ln = reverse($ln);
         }
         $localvar = trim($localvar);
         $dtype = trim($dtype);
         $localdata = trim($localdata);
         if($dtype =~ /public|private|protected|static|return|abstract|void|else|instanceof|new|case|final/)
         {
          next;
         }
         elsif($localvar =~ /instanceof|new/)
         {
          next;
         }
         else
         {
          $localdata ="$ln"."#"."$localvar"."#"."$dtype"."#"."$inits"."#".""."$currentfname"."#"."$jfile";
          # $prvele = "$ln"."#"."$ele"."#"."$dtype"."#"."$init"."#"."$cn"."#"."$jfile";
          $localdata = trim($localdata);
          printf LOCAL ("$localdata\n");
          push(@Localvar ,$localdata);
         }
      }# while$z
      while($z =~ /\(.*\)/g)
      {
        $bwparam = $1 ; # masking data b/w in paranth like ( inta ,int b);
        $z =~ s/$bwparam/ /;
        print;
      }# while$z
      while($z =~ /([a-zA-Z0-9_]+)\s+([a-zA-Z0-9_]+)\s*\,(.*)<SEM>/g)
      {
         $bk1 = $`;
         $dtype1 = $1;
         $multiple_dec = $3;
         $multiple_dec = trim($multiple_dec );
         @multivar  = split("\,",$multiple_dec);
         $bk1 = reverse($bk1);
         if($bk1 =~ /(>[0-9]+<)/)
         {
            $ln1 = $1;
            $ln1 = reverse($ln1);
         }
         $dtype1 = trim($dtype1);
         foreach $var_m(@multivar)
         {
           $var_m = trim ($var_m);
           if($dtype1 =~ /public|private|protected|static|return|abstract|void|else|instanceof|new|case|final/)
           {
            next;
           }
           elsif($var_m =~ /instanceof|new/)
           {
            next;
           }
           else
           {
            $localdata1 ="$ln1"."#"."$var_m"."#"."$dtype1"."#"."_"."#"."$currentfname"."#"."$jfile";
            $var_m = trim($var_m);
            printf LOCAL ("$localdata1\n");
            push(@Localvar ,$localdata1);
           }
         }#@multivar
      }#while $z
    } # for @templines_local
 }#for @D
 close(IF);
 close(LOCAL);
 return (@localmethods);
}# routine

# PASS 2 - Clean Packages and Imports

sub CleanFileTransilationalUnit(@)
{
  my @tmpcleanlines = @_;
  $findstr = "";
  $tmpcleanline = "";
  $obr = "";
  $replace_key1 = "";
  foreach $tmpcleanline (@tmpcleanlines)
  {
    $tmpcleanline =~ s/\".*\"/""/g;
    if($tmpcleanline =~ /(^import.*\;)/)
    {
       $findstr =  $1;
       $tmpcleanline =~ s/$findstr/ /;
    }
    if($tmpcleanline =~ /(^package.*\;)/)
    {
       $findstr =  $1;
       $tmpcleanline =~ s/$findstr/ /;
    }
    $tmpcleanline =~ s/case/case()/;
    $tmpcleanline =~ s/\[.*\]/ /;
    if($tmpcleanline =~ /try\s*([ \{]+)/)
    {
       $obr = $1;
       $replace_key1 = "( )"."{";
       $tmpcleanline =~ s/$obr/$replace_key1/;
    }
    if($tmpcleanline =~ /else\s*([\{]+)/)
    {
       $obr = $1;
       $replace_key1 = "( )"."{";
       $tmpcleanline =~ s/$obr/$replace_key1/;
    }
    if($tmpcleanline =~ /case\s*([\{]+)/)
    {
       $obr = $1;
       $replace_key1 = "( )"."{";
       $tmpcleanline =~ s/$obr/$replace_key1/;
    }

    if($tmpcleanline =~ /finally\s*([\{]+)/)
    {
       $obr = $1;
       $replace_key1 = "( )"."{";
       $tmpcleanline =~ s/$obr/$replace_key1/;
    }
    if($tmpcleanline =~ /class\s*([\w]+)/)
    {
    print;
    }
    while($tmpcleanline =~ /\b(public|abstract|private|implements|extends|protected|transient|volatile|void|static|final|finally|for|while|do|if|switch|else|catch|int|float|String|byte|char|double|long|boolean|class|try|throws|return|new|interface)\b\s+/gc)
    {
       $str = $1;
       $str1 = uc($str);
       $replace_key  = "___"."$str1 ";
       $tmpcleanline =~ s/$str/$replace_key/;
    }
  }
 return(@tmpcleanlines);
}

sub CleanLocalTransilationalUnit(@)
{
  @tmplocaltranslines = @_;
  @templines1 = ();
  @chlines1 = ();
  $classfound = 0;
  my $w_para = "";
  my $b_para = "";
  my $rep_para = "";
 foreach $l (@tmplocaltranslines)
 {
   $lno ++;
   if($l =~ /\{/g)
   {
    $l =~ s/\{/ \{ /g;
   }
   if($l =~ /\}/g)
   {
    $l =~ s/\}/ \} /g;
   }
   if($l =~ /\(/g)
   {
    $l =~ s/\(/ \(/g;
   }
   if($l =~ /\)/g)
   {
    $l =~ s/\)/ \)/g;
   }
   $l =~ s/\n/ <NEWLINE>/g;
   @lexicaltokens = split(/\s+/, $l);
   foreach my $token (@lexicaltokens)
   {
    if($token eq "___CLASS")
    {
      $currtoken = "";
    }

    if($OpenCount eq $CloseCount)
    {
      $SuspectMethod = 0;
    }
    if($token eq "<NEWLINE>")
    {
      $lookahead = $token;
      $filelines1 = "<$lno> "."$filelines1"."\n";
      push(@chlines1, $filelines1);
      $filelines1 = "";
    }
    if($token eq ")")
    {
      $currtoken = $token;
    }
    if($token eq "{")
    {
      $lookahead = $token;
    }
    if(($currtoken eq ")") && ($lookahead eq "{") )
    {
      $SuspectMethod = 1;
      $OpenCount++;
      $currtoken = "";
      $lookahead = "";
      if($token ne "<NEWLINE>")
       {
        $filelines1 = "$filelines1"."$token ";
       }
    }
    if(($token eq "}") && ($SuspectMethod == 1))
    {
      $CloseCount++;
      if($token ne "<NEWLINE>")
       {
        $filelines1 = "$filelines1"."$token ";
       }
    }
    if($SuspectMethod != 1)
    {

     if($token ne "<NEWLINE>")
      {
         $filelines1 = "$filelines1"."$token ";
      }
    }
    else
    {
      if($token =~ /<NEWLINE>/ )
       {
         $filelines2 = "$filelines2"."$token ";
       }
     }
    }
 }
 foreach $t(@chlines1)
 {
 }
 foreach $l (@chlines1)
 {
  if( $l =~ /\;/)
   {
    $repsem = " <SEM> ;";
    $l =~ s/;/$repsem/g ;
   }
   $fline = "$fline"."$l";
 }
 $finalline = $fline;
 $fline = "";
 $finalline =~ s/\n/ /g;
 $finalline =~ s/\t/ /g;
 $finalline =~ s/\s+/ /g;
 @templines1 = split("\;",$finalline);

  print;
 foreach $tl(@templines1)
 {
   if($tl =~ /(\w+)\s*([\(]+)/)
    {
     $w_para  = $1;
     $w_para  = trim($w_para);
     $b_para  = $2;
     $b_para  = trim($b_para);
     $rep_para = "$w_para"."$b_para";
     $tl   =~ s/(\w+)\s*([\(]+)/$rep_para/g;
   }
=b  if($tl =~ /(\w+)\s*([\{]+)/)
    {
     $w_para1  = $1;
     $w_para1  = trim($w_para1);
     $b_para1  = $2;
     $b_para1  = trim($b_para1);
     $rep_para1 = "$w_para1"."$b_para1";
     $tl   =~ s/(\w+)\s*([\{]+)/$rep_para1/g;
   }
=cut
   if($tl =~ /\<\SEM\>/)
   {
    if($tl =~ /\=\s*(\{)/)
     {
      $str = $1;
      $repstr = "<INIT>" ;
      $tl =~ s/$str/$repstr/g;
      if($tl =~ /\<[0-9]+\>.*\{(.*)/)
       {
        push(@SusVar,$1);
       }
       else
       {
        push(@SusVar,$tl);
       }
     }
     else
     {
       if($tl =~ /\<[0-9]+\>\s*\{(.*)/)
        {
         push(@SusVar,$1);
        }
        else
        {
         push(@SusVar,$tl);
        }
     }
   }
 }
return(@SusVar);
}

#  For Global Variable Declarations with AccessSpecifiers:

sub ExtractGlobalVariables(@SusVar,@ClsDomain,@D)
{
  my $SusVar    = shift;
  my $ClsDoamin = shift;
  my $D         = shift;
  my @SusVar    = @{$SusVar};
  my @ClsDoamin = @{$ClsDoamin};
  my @D         = @{$D};
  
  my $ln  = "";
  my $v   = "";
  my $q   = "";
  my $d   = "";
  my $var = "";
  my $eq  = "";
  $globalvar = "$path/Globalinfo.g";
  open(GLOBAL , ">> $globalvar")or die "could not open $globalvar...\n ";
  $prvar = "$path/Localvariables.l";
  open(PRVLOCAL , "> $prvar")or die "could not open $prvar...\n ";
  foreach my $v(@SusVar)
  {
   $v =~ s/\[.*\]/ /g;
   $v =~ s/\(.*\)/()/g;
   
   while($v =~ /(<[0-9]+>)/g)
   {
    $ln = $1;
    $v =~ s/$ln/ /g;
   }
   while($v =~/([PUBLIC|PRIVATE|STATIC|PROTECTED|___|\s*|FINAL]*)\s+([a-zA-Z0-9-_]+)\s+([a-zA-Z0-9-_,( ]+)\s*([\=]*)\s*([a-zA-Z0-9-_"\<\>INIT]*)/g)
   {
    $q    = $1;
    $q = trim ($q);
    $d = trim ($d);
    $d    = $2;
    $var  = $3;
    $var  = trim($var);
    $eq   = $6;
    $eq  = trim ($eq);
    $init = $5 ;
    $init  = trim ($init);
    if($init =~/\<SEM\>/)
    {
     $init = "";
    }
    if($d =~ /(CLASS|ABSTRACT|EXTENDS|IMPLEMENTS|NEW|PUBLIC|PRIVATE|PROTECTED|VOID|INTERFACE|THROWS)/ )
    {
       next;
    }
    if($var =~ /(CLASS|ABSTRACT|EXTENDS|IMPLEMENTS|INERFACE|THROWS)/ )
    {
       next;
    }
    if($var =~ /\(/ )
    {
       next;
    }
    
    if($q =~ /(PUBLIC|PRIVATE|PROTECTED)/)
    {
      $a = $1;  # accessspecifier
    }
    if($q =~ /(STATIC)/)
    {
      $b = $1;    # qualifier
    }
    if($q =~ /(FINAL)/)
    {
     $c = $1;
    }
    if($q =~ /(PUBLIC|PRIVATE|PROTECTED)/)
    {
      print;
    }
    else
    {
    $a = "_";
    }
    push( @var_objects , split(",",$var) );
    foreach $var_element ( @var_objects )
    {
     if($var_element =~/(\w+)/)
     {
        $ele = $var_element;
        $var_element = trim($var_element);
        $var_element = $var_element."#"."$ln";
        $ret1 = checkinclasshashtable($ln,\@ClsDoamin);
        $key_cls = $ret1;
        push( @{$ClassVar{$key_cls}},$var_element);
        push( @{$ClassVar{$key_cls}},$jfile);
        if($key_cls =~ /(.*)\:(.*)/)
        {
         $cn = $1;
         $dec_cls = $a." #".$cn."#"."$var_element";
         push (@dec_class,$dec_cls);
        }
        if($init =~ /\"\s*\"/)
        {
         $init =~ s/$eq/INIT/;
        }
        elsif($init eq "")
        {
         $init ="_";
        }
        $detail_compare = "$var_element"."#"."$a"."#"."$d"."#"."$jfile"."#"."$init"."#"."$cn";
        $details = "$a"."#"."$b"."#"."$c"."#"."$d"."#"."$jfile"."#"."$init"."#"."$key_cls";
        if($detail_compare =~ /PUBLIC|PROTECTED/)
        {
         #printf GLOBAL  (" $detail_compare\n");
         printf JKK ("$detail_compare\n");
         printf JK ("$ele\n");
         printf GLOBAL ("$ele\n");
         #printf STDERR  (" FROM IF COND PUBLIC and PROTECTED:$detail_compare\n");
         push(@publicStack,$detail_compare);
        }
        elsif($detail_compare =~ /PRIVATE/)
        {
          if($d =~ /_/)
          {
           $dtype = $d;
           $dtype =~ s/_//g;
           $dtype = lc($dtype);
          }
          else
          {
           $dtype = $d;
          }
           $cn_pvt  = $cn  ;
           $cn_pvt  = "PVT"."@"."$cn_pvt";
           
           $prvele = "$ln"."#"."$ele"."#"."$dtype"."#"."$init"."#"."$cn_pvt"."#"."$jfile";
           #printf STDERR ("FROM IF COND PRIVATE :$detail_compare\n");
           #print PRVLOCAL "$prvele#PRIVATE\n";
           print PRVLOCAL "$prvele\n";
           push(@privateStack,$detail_compare);
        }
        else
        {
         #printf STDERR ("FROM IF COND DEFAULT :$detail_compare\n");
         printf JKK ("$detail_compare\n");
         printf JK ("$ele\n");
         printf GLOBAL ("$ele\n");
         
         push(@publicStack,$detail_compare);
        }
        push( @{$Object_declared{$var_element}},$details); # Add lineno and filenames into table.
        push( @{$Object_declared{$var_element}},$jfile );
      }
     }
     $var_element = "";
     $a =""; $b = ""; $c ="";$d = "";
     @var_objects = ();
     print;
   }
 }
   close(GLOBAL);
   close(PRVLOCAL);
}# routine

sub checkinclasshashtable ($decllno,\@ClsDomain)
{
  my $decllno    = shift;
  my $ClsDomain  = shift;
  my @ClsDomain  = @{$ClsDomain};
  my $fclon = "";
  my $dlno  = "";
  my $fclon = "";
  my $fclo  = "";
  my $fclc  = "";
  my $strc  = "";
  if($decllno =~ /\<([0-9]+)\>/)
  {
    $dlno = $1;
  }
  @Clsdomain = reverse (sort {$a <=> $b}  @Clsdomain);

  foreach my $com( @ClsDomain)
  {
    if($com =~ /(\w+)\s*\#\s*\<([0-9]+)\>\s*\:\s*\<([0-9]+)\>/)
    {
      $fclon =  $1;
      $fclo  =  $2;
      $fclc  =  $3;
    }
    if(($dlno > $fclo) && ($dlno < $fclc))
    {
     $strc = "$fclon : $fclo";
     return $strc;
    }
  }
}
sub trim($)
{
    my $string = shift;
    $string =~ s/^\s+//;
    $string =~ s/\s+$//;
    return $string;
}

$finalline= "";
$finalline2= "";
$finalline1= "";
###############################3  functiondomains########################

sub MethodDomains (@)
{
  my @Domain_method =@_;
  #$methodfile_l = "$path/Domainslocal.method";
  $methodfile = "$path/Domains.method";
  open(METHOD, ">> $methodfile" ) or die "could not write $methodfile_l...\n ";
  #open(METHODLOCAL, "> $methodfile_l" ) or die "could not write $methodfile_l...\n ";
  printf METHOD ("<FILE>\n");
  foreach $met( @Domain_method)
  {
    $flag = 0;
   if($met =~ /(while|if|catch|for|switch)/)
   {
     $flag = 1;
   }
   if($flag == 0)
   {
      $met = "$met"."#"."$jfile";
      printf METHOD ("$met\n");
   }
  }
  printf METHOD ("<\FILE>\n  ");
  close(METHOD);
}

 sub processLocalvariables()
 {
  my $var_l = "";
  my $len = "";
  @localvars = ();
  $localvariables  = "$path/Localvariables.l";
  open (LOCALREF ,"< $localvariables" )||die ("could not read $localvariables");
  @localvars = <LOCALREF>;
  close(LOCALREF);
  unlink($localvariables);
  $writevar = "$path/LocalRefs.l";
  open (WRITEVAR ,">> $writevar" )||die ("could not write $localvariables");
  $len = scalar(@localvars);
  foreach my $lcv (@localvars)
  {
     $count++;

    if($lcv =~ /a/ )
    {
     print;
    }
  #  print ">>parsing an object [$count/$len], $varinfo...\n";
    $lcv  = trim ($lcv);
    if($lcv =~ /\<([0-9]+)\>\#([A-Za-z0-9_-]+)\#([A-Za-z0-9_-]+)\#([A-Za-z0-9_-]+)\#(.*)\#(.*)/)
    {
     $var_l        = $1;
     $var_l        = trim ($var_l);
     $var_n        = $2;
     $var_n        = trim ($var_n);
     if($var_l eq  "b")
     {
     print;
     }
     $var_d        = $3;
     $var_d        = trim ($var_d);
     $var_funname  = $4;
     $var_funname  = trim ($var_funname);
     $var_flname   = $5;
     $var_flname   = trim ($var_flname);
     $search_pattern= $var_n;
     $file_pattern  = "java";
     $varinfo = trim ($varinfo);
     $lcv = trim ($lcv);
     print WRITEVAR  " <Object>[$lcv]\n";
     find(\&d, $jfile);
    }
  }
   print WRITEVAR "<END>\n";
  close(WRITEVAR);
}

 sub d
 {
  $writerefs = "";
  $file_pattern  = "java";
  $jfile =~ s,/,\\,g;
  return unless -f $jfile;
  return  unless $jfile =~ /$file_pattern/;
  open F, $jfile or print "couldn't open $jfile\n" && return;
  while (<F>)
  {
   if (my $found = m/(\b$search_pattern\b)/o)
    {
     $line = $_;
     $str = trim($line);
     chomp($str);
     $jfile = trim ($jfile);
     #printf  WRITEREFS ("[$.\~ $jfile \~ $str]\n");
     print  WRITEVAR  "\t[$.\# $jfile \# $str]\n";
     #print  "\t[$.\# $jfile \# $str]\n";
    }
  }
 close F;
}

sub ReferenceProcess(@)
{
  @methoddomains   = @_;
  my  $varf        = "";
  my  $varinit     =  "";
  my  $varname        =  "";
  my  $varlno     =  "";
  my  $var_access1 =  "";
  my  $dtype  =   "";
  my  $initval     =  "";
  my $funcname  = "";
  $readrefs ="$path/LocalRefs.l";
  open (READLOCALREF ,"< $readrefs")|| die ("Could not read file $readrefs\n");
  @localrefs = <READLOCALREF>;
  close(READLOCALREF);
  unlink($readrefs);
  #$final_ref = "$path/Final.cgr";    #for writing private refs.
  $final_ref = "$path/unusedobjects.cgr";    #for writing private refs.
  open (LCRESULT ,">> $final_ref")|| die ("Could not read output file\n");
  $nullptrexp = "$path/nullpointer.cgr";  #for writing local object refs.
  open (NPTR ,">> $nullptrexp")|| die ("Could not read output file\n");
  $len = scalar(@localrefs);
  $useflag = 1;
  @Unuselocal = ();
  foreach my $ref(@localrefs)
  {
    $count1++;

    if($ref =~ /<Object>\s*\[\s*\<([0-9]+)\>\#([A-Za-z0-9_-]+)\#([A-Za-z0-9_-]+)\#(.*)\#(.*)\#(.*)\]/)
    {
      $flag = 0;
      if($useflag ne 1)
      {
      # print "UNUSE:$backref\n";
       push(@Unuselocal,$backref);
      }
      $backref = $ref;
      $varlno   = $1;
      $varlno   = trim ($varlno);
      $dtype    = $3;
      $dtype    = trim($dtype);
      $varname  = $2 ;
      $varname  = trim($varname);
      $initval  = $4;
      $funcname = $5;
      if($funcname =~ /([A-Za-z0-9_]+)\@([A-Za-z0-9_]+)/)
      {
       $flag = 1;
       $funcname = $2;
      }
      $funcname = trim($funcname);
      $filename = $6;
      $filename = trim ($filename);
      $jfile  =~ s/\\/\//g;
      if( ($initval eq "_" )&&($flag == 0))
       {
        $initval = "UNINIT";
        printf NPTR ("$varname [%s, %s, %s]\n","$varlno", "$funcname", "$jfile" );# "Object  $varname [$varlno,$funcname]\n";
       }
       #printf LCRESULT ("Object %s [%s, %s, %s]\n", "$varname", "$varlno", "$funcname", "$jfile" );# "Object  $varname [$varlno,$funcname]\n";
       printf LCRESULT ("$varname [%s, %s, %s]\n","$varlno", "$funcname", "$jfile" );# "Object  $varname [$varlno,$funcname]\n";
       printf LCRESULT ("    %-6s [%s]\n", "Type", $dtype);# "Object  $varname [$varlno,$funcname]\n";
       printf LCRESULT ("    %-6s [%s]\n", "Init", $initval);# "Object  $varname [$varlno,$funcname]\n";
       $useflag = 0;
    }
    elsif($ref =~ /\[(.*)\#(.*)\#(.*)\]/)
    {
      $From_ref = $1;
      $ref_fname = $2;
      $strform = $3;
      $ref_fname =~ s/\\/\//g;
      $ref_fname = trim ($ref_fname);
      if($varlno eq $From_ref)
      {
       next;
      }
      if($varlno >$From_ref )
      {
       next;
      }
      $ret = checkinmethodhashtable($From_ref,\@methoddomains);
      if($ret =~ /(.*)\:(.*)/ )
      {
       $referfuncname = $1;
       $referfuncname  =trim ($referfuncname);
       if($flag == 1)
        {
          if($strform =~ /([A-Za-z0-9._-]*)\s*\=\s*(.*)/)
          {
           $vars = $1;
           $varhs = $2;
            if($vars eq $varname)
            {
             $useflag =1;
             printf LCRESULT ("    %-6s [%s, %s, %s]\n", "Set",  "$From_ref", "$referfuncname", "$ref_fname");
             }
            while($varhs =~ /\b$varname\b/g)
            {
             $useflag =1;
             printf LCRESULT ("    %-6s [%s, %s, %s]\n", "Use",  "$From_ref", "$referfuncname", "$ref_fname");
#            print LCRESULT "            Use[$From_ref, $referfuncname, $ref_fname]\n";
            }
          }
          else
         {
          $useflag =1;
          printf LCRESULT ("    %-6s [%s, %s, %s]\n", "Use",  "$From_ref", "$referfuncname", "$ref_fname");
         }
        }
        elsif($referfuncname eq $funcname)
        {
         #$referfuncname = $1;
         if($strform =~ /([A-Za-z0-9._-]+)\s*\=\s*(.*)/)
         {
           $vars = $1;
           $varhs = $2;
           if($vars =~/\b$varname\b/)
           {
             $useflag =1;
             printf LCRESULT ("    %-6s [%s, %s, %s]\n", "Set",  "$From_ref", "$referfuncname", "$ref_fname");
           }
            while($varhs =~ /\b$varname\b/g)
           {
            $useflag =1;
            printf LCRESULT ("    %-6s [%s, %s, %s]\n", "Use",  "$From_ref", "$referfuncname", "$ref_fname");
           }
         }
         else
         {
          $useflag =1;
          printf LCRESULT ("    %-6s [%s, %s, %s]\n", "Use",  "$From_ref", "$referfuncname", "$ref_fname");
         }
        }# elsif
      }#ret
   }#ref
   elsif($ref =~/\<END\>/)
   {
    if ($useflag == 0)
    {
     push(@Unuselocal,$backref);
    }
   }
 }# foreach @refs
   foreach my $unuse(@Unuselocal)
   {
     if($unuse =~ /<Object>\s*\[\s*\<([0-9]+)\>\#([A-Za-z0-9_-]+)\#([A-Za-z0-9_-]+)\#(.*)\#(.*)\#(.*)\]/)
     {
       $varlno1   = $1;
       $varlno1   = trim ($varlno1);
       $dtype1    = $3;
       $dtype1    = trim($dtype1);
       $varname1  = $2 ;
       $varname1  = trim($varname1);
       $initval1  = $4;
       if($initval1 eq "_" )
       {
         $initval1 = "UNINIT";
       }
       $funcname1 = $5;
       if($funcname1 =~ /([A-Za-z0-9_]+)\@([A-Za-z0-9_]+)/)
       {
        $flag1 = 1;
        $funcname1 = $2;
       }
       $funcname1 = trim($funcname1);
       $filename1 = $6;
       $filename1 = trim ($filename1);
       $jfile  =~ s/\\/\//g;
       printf LCRESULT ("<U>$varname1 [%s, %s, %s]\n","$varlno1", "$funcname1", "$jfile" );# "Object  $varname [$varlno,$funcname]\n";
       #printf LCRESULT ("    %-6s [%s]\n", "Type", $dtype1);# "Object  $varname [$varlno,$funcname]\n";
       #printf LCRESULT ("    %-6s [%s]\n", "Init", $initval1);# "Object  $varname [$varlno,$funcname]\n";
     }
   }
 close(NPTR);
 close(LCRESULT);
}#routine

sub checkinmethodhashtable($decllno1,\@D)
{
  my $decllno1 = shift;
  my $D       = shift;
  my @D       = @{$D};
  my $fomn    = "";
  my $foml    = "";
  my $fcml    = "";
  my $strm    = "";
  $decllno1 = trim($decllno1);
  #print"LNO:$decllno1\n";
  if( $decllno1 =~ /([0-9]+)/)
  {
      $decllno = $1;
      $decllno = trim($decllno);
  }
  foreach my $fom(@D)
  {
    if($fom =~ /(\w+)\:\<([0-9]+)\:([0-9]+)\>/ )
     {
       $fomn = $1;
       $foml = $2;
       $fcml = $3;
    }
    if(($decllno > $foml)     &&
       ($decllno < $fcml)
       )
    {
      #$inmethod = 1;
      $strm = "$fomn : $foml";
      return $strm;
    }
  }
}




 printf JK ("                     CLASS-VARIABLES                            \n");
 printf JK ("%-120s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
 printf JK ("\n");

 printf JK ("%-30s%-15s%-40s%-30s%-30s%-30s%-40s%-40s%-150s\n", "VariableName ","LineNo ","DataType ","AccsessSpecfier ","StorageSpecfier ","TypeSpecfier"," Value ","ClassName","FileName");
 printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");

  foreach $key( keys %Object_declared )
  {
   if($key =~ /(\w+)\#\<([0-9]+)\>/)
    {
     $key_var = $1;
    # print"$key_var\n";
     printf JK ("%-30s", $key_var);
     $key_lno = $2;
     printf JK ("%-15s", $key_lno);             #Defined classname as key entity.
    }
    @information = ();
    @information = @{$Object_declared{$key}};
    foreach $entity (@information)
    {
      if($entity =~ /(.*)\#(.*)\#(.*)\#(.*)\#(.*)\#(.*)\#(.*)/)
      {
        $as   = $1;
        $ssp  = $2;
        $tp   = $3;
        $dt   = $4;
        $eq   = $6;
        $fn   = $5;
        $clsn = $7;
       if($dt =~ /([\___]*)\s*(\w+)/ )
       {
        $oneles = $2;
       # print"$oneles\n";
        printf JK ("%-40s", $oneles);
       }
       else
       {
        printf JK ("%-40s", "__");
       }
        if($as =~ /(\w+)/ )
       {
        $onele = $1;
       # print"$onele\n";
        printf JK ("%-30s", $onele);
       }
       else
       {
        printf JK ("%-30s", "__");
       }
       if($ssp =~ /(\w+)/ )
       {
        $onel = $1;
       # print"$onele\n";
        printf JK ("%-30s", $onel);
       }
       else
       {
        printf JK ("%-30s", "__");
       }
       if($tp =~ /(\w+)/ )
       {
        $onel = $1;
       # print"$onel\n";
        printf JK ("%-30s", $onel);
       }
       else
       {
        printf JK ("%-30s", "__");
       }
       if($eq =~ /([a-zA-Z0-9-_ -]+)/ )
       {
        $one = $1;
       # print"$one\n";
        printf JK ("%-40s", $one);
       }
       else
       {
        printf JK ("%-40s", "UNINIT");
       }
       printf JK ("%-40s", $clsn);
       #if($endli =~ /(\w+)/ ){ $one = $1;  print"$one\n"; printf JK  ("%-20s%", $one);   }
       printf JK ("%-150s", $fn);             #Defined classname as key entity.
      }
    }
    printf JK "\n";
   $finalline2= "";
   $finalline1= "";
  }#%Object_declared
  printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
  printf JK ("\n");
  printf JK ("\n");

   printf JK ("                     FUNCTION-VARIABLES                            \n");
   printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
   printf JK ("\n");

   printf JK ("%-40s%-15s%-40s%-40s%-100s\n", "VariableName ","LineNo ","DataType","FunctionName","FileName");
    printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
      foreach $key( keys %Object_declaredlocal )
      {
         if($key =~ /(\w+)\s*\#\s*\<([0-9]+)\>/)
          {
           $key_var = $1;
           $key_lno = $2;
           printf JK ("%-40s", $key_var);
           printf JK ("%-15s", $key_lno);
          }
          @information = ();
          @information = @{$Object_declaredlocal{$key}};
          $i=0;
          foreach $entity (@information)
          {
            $i++;
            if($i == 1)
            {
             printf JK ("%-40s",  @information[0]);
            }
            if($i == 2)
            {
             printf JK ("%-40s", @information[1]);
            }
            if($i == 3)
            {
             printf JK ("%-100s", @information[2]);
            }
          }
           printf JK "\n";
           @information = ();
      }
      printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
      printf JK "\n";
      printf JK "\n";

#      printf JK ("%-40s%-15s%-40s%-100s\n", "VariableName ","LineNo ","DataType","FileName");
#      printf JK ("%-120s\n", "--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
       printf JK ("                               GLOBAL VARIBLES   \n");
       printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
       printf JK "\n";
       printf JK "\n";

      foreach $key( keys %ClassVar )
      {
         if($key =~ /(\w+)\s*\:\s*([0-9]+)/)
          {
           $key_var = $1;
           $key_lno = $2;
           printf JK ("ClassName:LineNo- $key_var : $key_lno\n");
           #printf JK ("$key_lno\n");
          }
          @information = @{$ClassVar{$key}};
          foreach $entity (@information)
          {
           printf JK ("           $entity\n");
          # printf JK ("$entity\n");
          }
           printf JK "\n";
      }
      printf JK ("%-120s\n", "-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
      printf JK "\n";
      printf JK "\n";

      printf JK ("                     OBJECTS& ITS CLASS                           \n");
      printf JK ("%-120s\n", "--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
      printf JK ("\n");

printf JK ("%-40s%-15s%-40s%-200s\n", "Instance Name","Atline No","NameoftheClass","FileName");
printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");

foreach $key_new( keys %UsedClasses_new)
{
 if($key_new =~ /([a-zA-Z0-9-,$._]+)\#([0-9]+)\#([a-zA-Z0-9-,$._]+)\#(.*)/)
  {
    $objname_new   = $1;
    $clslno_new    = $2;
    $clsname_new   = $3;
    $fname_new     = $4;
    printf JK ("%-40s",$objname_new);
    printf JK ("%-15d",$clslno_new);
    printf JK ("%-40s",$clsname_new);
    printf JK ("%-200s",$fname_new);

  }
   printf JK "\n";
}

printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
printf JK ("\n");
printf JK ("\n");


printf JK ("                       Extends:  A Class extended by which  Class                        \n");
printf JK ("%-120s\n", "--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
printf JK ("\n");


printf JK ("%-40s%-15s%-40s%-200s\n", "subClass Name","Atline No","superClass Name","FileName");
printf JK ("%-135s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");

foreach $key_extends( keys %UsedClasses_extends)
{
 if($key_extends =~ /([a-zA-Z0-9-,$._]+)\#([0-9]+)\#([a-zA-Z0-9-,$._]+)\#(.*)/)
  {
    $subclsname    = $1;
    $clslno        = $2;
    $supclsname    = $3;
    $fname_extends = $4;
    printf JK ("%-40s",$subclsname);
    printf JK ("%-15d",$clslno);
    printf JK ("%-40s",$supclsname);
    printf JK ("%-200s",$fname_extends);

  }
   printf JK "\n";
}
printf JK ("%-120s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
printf JK ("\n");
printf JK ("\n");

print JK ("                                  LOCAL VARAIBLES\n");
printf JK ("%-120s\n", "----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------");
printf JK ("\n");

 foreach $key( keys %Function_var)
      {
        if($key =~ /(\w+)\:\<(.*)\:(.*)\>/ )
        {
         $key_var = $1;
        }
        print JK "FunctionName : $key_var\n";
        printf JK "\n";
        @information = ();
        @information = @{$Function_var{$key}};
        foreach $entity (@information)
        {
          if($entity =~ /(.*)\#(.*)\#(.*)\#(.*)/)
          {
             $var = $1;
             #$n   = $2;
             $dy  = $3;
             $fn = $4;
            if($n =~ /\<([0-9]+)\>/ )
            {
             $ln = $1;
            }
            print JK " VarName         : $var\n";
            print JK " DataType        : $dy\n";
            print JK " FName           : $fn\n";
          }
        }
        printf JK "\n";
      }
close(JK);
unlink($junkfile);
#unlink($globalvar);
close(JKK);
#unlink(LOCAL);
#unlink(METHOD);
