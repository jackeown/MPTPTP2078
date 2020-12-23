%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:29 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 358 expanded)
%              Number of leaves         :   43 ( 134 expanded)
%              Depth                    :   16
%              Number of atoms          :  200 ( 767 expanded)
%              Number of equality atoms :   81 ( 329 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_116,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_194,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_202,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_194])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_42,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_212,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_202,c_42])).

tff(c_214,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_641,plain,(
    ! [B_142,A_143] :
      ( k1_tarski(k1_funct_1(B_142,A_143)) = k2_relat_1(B_142)
      | k1_tarski(A_143) != k1_relat_1(B_142)
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_536,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_544,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_536])).

tff(c_66,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_554,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_66])).

tff(c_647,plain,
    ( k1_tarski('#skF_3') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_554])).

tff(c_660,plain,(
    k1_tarski('#skF_3') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_647])).

tff(c_287,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_295,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_287])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(B_22),A_21)
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_297,plain,(
    ! [B_88,A_89] :
      ( k1_tarski(B_88) = A_89
      | k1_xboole_0 = A_89
      | ~ r1_tarski(A_89,k1_tarski(B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_875,plain,(
    ! [B_169,B_170] :
      ( k1_tarski(B_169) = k1_relat_1(B_170)
      | k1_relat_1(B_170) = k1_xboole_0
      | ~ v4_relat_1(B_170,k1_tarski(B_169))
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_34,c_297])).

tff(c_897,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_295,c_875])).

tff(c_912,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_897])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_660,c_912])).

tff(c_915,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_926,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_915,c_36])).

tff(c_40,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_211,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_202,c_40])).

tff(c_213,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_917,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_213])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_917])).

tff(c_958,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_969,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_958,c_38])).

tff(c_959,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_978,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_959])).

tff(c_1337,plain,(
    ! [B_236,A_237] :
      ( k1_tarski(k1_funct_1(B_236,A_237)) = k2_relat_1(B_236)
      | k1_tarski(A_237) != k1_relat_1(B_236)
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_966,plain,(
    ! [A_17] : m1_subset_1('#skF_5',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_28])).

tff(c_1316,plain,(
    ! [A_229,B_230,C_231] :
      ( k2_relset_1(A_229,B_230,C_231) = k2_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1320,plain,(
    ! [A_229,B_230] : k2_relset_1(A_229,B_230,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_966,c_1316])).

tff(c_1322,plain,(
    ! [A_229,B_230] : k2_relset_1(A_229,B_230,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_1320])).

tff(c_1323,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1322,c_66])).

tff(c_1343,plain,
    ( k2_relat_1('#skF_5') != '#skF_5'
    | k1_tarski('#skF_3') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1337,c_1323])).

tff(c_1355,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_969,c_978,c_1343])).

tff(c_1149,plain,(
    ! [C_199,A_200,B_201] :
      ( v4_relat_1(C_199,A_200)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1154,plain,(
    ! [A_200] : v4_relat_1('#skF_5',A_200) ),
    inference(resolution,[status(thm)],[c_966,c_1149])).

tff(c_58,plain,(
    ! [A_37] : k1_relat_1('#skF_2'(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_62,plain,(
    ! [A_37] : v1_relat_1('#skF_2'(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_110,plain,(
    ! [A_56] :
      ( k1_relat_1(A_56) != k1_xboole_0
      | k1_xboole_0 = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,(
    ! [A_37] :
      ( k1_relat_1('#skF_2'(A_37)) != k1_xboole_0
      | '#skF_2'(A_37) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_62,c_110])).

tff(c_115,plain,(
    ! [A_37] :
      ( k1_xboole_0 != A_37
      | '#skF_2'(A_37) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_113])).

tff(c_964,plain,(
    ! [A_37] :
      ( A_37 != '#skF_5'
      | '#skF_2'(A_37) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_958,c_115])).

tff(c_1053,plain,(
    ! [B_181,A_182] :
      ( r1_tarski(k1_relat_1(B_181),A_182)
      | ~ v4_relat_1(B_181,A_182)
      | ~ v1_relat_1(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1065,plain,(
    ! [A_37,A_182] :
      ( r1_tarski(A_37,A_182)
      | ~ v4_relat_1('#skF_2'(A_37),A_182)
      | ~ v1_relat_1('#skF_2'(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1053])).

tff(c_1072,plain,(
    ! [A_183,A_184] :
      ( r1_tarski(A_183,A_184)
      | ~ v4_relat_1('#skF_2'(A_183),A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1065])).

tff(c_1075,plain,(
    ! [A_37,A_184] :
      ( r1_tarski(A_37,A_184)
      | ~ v4_relat_1('#skF_5',A_184)
      | A_37 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_1072])).

tff(c_1165,plain,(
    ! [A_184] : r1_tarski('#skF_5',A_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_1075])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_970,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_68])).

tff(c_72,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [D_46,C_45,A_43,B_44] :
      ( r2_hidden(k1_funct_1(D_46,C_45),k2_relset_1(A_43,B_44,D_46))
      | k1_xboole_0 = B_44
      | ~ r2_hidden(C_45,A_43)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(D_46,A_43,B_44)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1437,plain,(
    ! [D_249,C_250,A_251,B_252] :
      ( r2_hidden(k1_funct_1(D_249,C_250),k2_relset_1(A_251,B_252,D_249))
      | B_252 = '#skF_5'
      | ~ r2_hidden(C_250,A_251)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ v1_funct_2(D_249,A_251,B_252)
      | ~ v1_funct_1(D_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_64])).

tff(c_1448,plain,(
    ! [C_250,B_230,A_229] :
      ( r2_hidden(k1_funct_1('#skF_5',C_250),'#skF_5')
      | B_230 = '#skF_5'
      | ~ r2_hidden(C_250,A_229)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_2('#skF_5',A_229,B_230)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_1437])).

tff(c_2483,plain,(
    ! [C_356,B_357,A_358] :
      ( r2_hidden(k1_funct_1('#skF_5',C_356),'#skF_5')
      | B_357 = '#skF_5'
      | ~ r2_hidden(C_356,A_358)
      | ~ v1_funct_2('#skF_5',A_358,B_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_966,c_1448])).

tff(c_2981,plain,(
    ! [A_410,B_411,B_412] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(A_410,B_411)),'#skF_5')
      | B_412 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_410,B_412)
      | r1_tarski(A_410,B_411) ) ),
    inference(resolution,[status(thm)],[c_6,c_2483])).

tff(c_2983,plain,(
    ! [B_411] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_tarski('#skF_3'),B_411)),'#skF_5')
      | '#skF_5' = '#skF_4'
      | r1_tarski(k1_tarski('#skF_3'),B_411) ) ),
    inference(resolution,[status(thm)],[c_72,c_2981])).

tff(c_2987,plain,(
    ! [B_413] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_tarski('#skF_3'),B_413)),'#skF_5')
      | r1_tarski(k1_tarski('#skF_3'),B_413) ) ),
    inference(negUnitSimplification,[status(thm)],[c_970,c_2983])).

tff(c_46,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3001,plain,(
    ! [B_413] :
      ( ~ r1_tarski('#skF_5',k1_funct_1('#skF_5','#skF_1'(k1_tarski('#skF_3'),B_413)))
      | r1_tarski(k1_tarski('#skF_3'),B_413) ) ),
    inference(resolution,[status(thm)],[c_2987,c_46])).

tff(c_3014,plain,(
    ! [B_414] : r1_tarski(k1_tarski('#skF_3'),B_414) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1165,c_3001])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_967,plain,(
    ! [A_8] : r1_tarski('#skF_5',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_14])).

tff(c_997,plain,(
    ! [B_176,A_177] :
      ( B_176 = A_177
      | ~ r1_tarski(B_176,A_177)
      | ~ r1_tarski(A_177,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1002,plain,(
    ! [A_8] :
      ( A_8 = '#skF_5'
      | ~ r1_tarski(A_8,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_967,c_997])).

tff(c_3086,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3014,c_1002])).

tff(c_3129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1355,c_3086])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.92  
% 5.05/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.93  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.05/1.93  
% 5.05/1.93  %Foreground sorts:
% 5.05/1.93  
% 5.05/1.93  
% 5.05/1.93  %Background operators:
% 5.05/1.93  
% 5.05/1.93  
% 5.05/1.93  %Foreground operators:
% 5.05/1.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.05/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.05/1.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.05/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.05/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.05/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.05/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/1.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.05/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.05/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.05/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.05/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.05/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.05/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.05/1.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.05/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.05/1.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.05/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.05/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.05/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.05/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/1.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.05/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.05/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.05/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.05/1.93  
% 5.05/1.95  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 5.05/1.95  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.05/1.95  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.05/1.95  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.05/1.95  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.05/1.95  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.05/1.95  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.05/1.95  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.05/1.95  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.05/1.95  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.05/1.95  tff(f_116, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_tarski(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e15_31__wellord2)).
% 5.05/1.95  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.05/1.95  tff(f_128, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 5.05/1.95  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.05/1.95  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.05/1.95  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.05/1.95  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.05/1.95  tff(c_194, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.05/1.95  tff(c_202, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_194])).
% 5.05/1.95  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.05/1.95  tff(c_42, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.05/1.95  tff(c_212, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_202, c_42])).
% 5.05/1.95  tff(c_214, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_212])).
% 5.05/1.95  tff(c_641, plain, (![B_142, A_143]: (k1_tarski(k1_funct_1(B_142, A_143))=k2_relat_1(B_142) | k1_tarski(A_143)!=k1_relat_1(B_142) | ~v1_funct_1(B_142) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.05/1.95  tff(c_536, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.95  tff(c_544, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_536])).
% 5.05/1.95  tff(c_66, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.05/1.95  tff(c_554, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_544, c_66])).
% 5.05/1.95  tff(c_647, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_641, c_554])).
% 5.05/1.95  tff(c_660, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_647])).
% 5.05/1.95  tff(c_287, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.05/1.95  tff(c_295, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_287])).
% 5.05/1.95  tff(c_34, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(B_22), A_21) | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.05/1.95  tff(c_297, plain, (![B_88, A_89]: (k1_tarski(B_88)=A_89 | k1_xboole_0=A_89 | ~r1_tarski(A_89, k1_tarski(B_88)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.05/1.95  tff(c_875, plain, (![B_169, B_170]: (k1_tarski(B_169)=k1_relat_1(B_170) | k1_relat_1(B_170)=k1_xboole_0 | ~v4_relat_1(B_170, k1_tarski(B_169)) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_34, c_297])).
% 5.05/1.95  tff(c_897, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_295, c_875])).
% 5.05/1.95  tff(c_912, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_202, c_897])).
% 5.05/1.95  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_660, c_912])).
% 5.05/1.95  tff(c_915, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_212])).
% 5.05/1.95  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.05/1.95  tff(c_926, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_915, c_36])).
% 5.05/1.95  tff(c_40, plain, (![A_23]: (k2_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.05/1.95  tff(c_211, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_202, c_40])).
% 5.05/1.95  tff(c_213, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211])).
% 5.05/1.95  tff(c_917, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_213])).
% 5.05/1.95  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_926, c_917])).
% 5.05/1.95  tff(c_958, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_211])).
% 5.05/1.95  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.05/1.95  tff(c_969, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_958, c_958, c_38])).
% 5.05/1.95  tff(c_959, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_211])).
% 5.05/1.95  tff(c_978, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_958, c_959])).
% 5.05/1.95  tff(c_1337, plain, (![B_236, A_237]: (k1_tarski(k1_funct_1(B_236, A_237))=k2_relat_1(B_236) | k1_tarski(A_237)!=k1_relat_1(B_236) | ~v1_funct_1(B_236) | ~v1_relat_1(B_236))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.05/1.95  tff(c_28, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.05/1.95  tff(c_966, plain, (![A_17]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_28])).
% 5.05/1.95  tff(c_1316, plain, (![A_229, B_230, C_231]: (k2_relset_1(A_229, B_230, C_231)=k2_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.05/1.95  tff(c_1320, plain, (![A_229, B_230]: (k2_relset_1(A_229, B_230, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_966, c_1316])).
% 5.05/1.95  tff(c_1322, plain, (![A_229, B_230]: (k2_relset_1(A_229, B_230, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_978, c_1320])).
% 5.05/1.95  tff(c_1323, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1322, c_66])).
% 5.05/1.95  tff(c_1343, plain, (k2_relat_1('#skF_5')!='#skF_5' | k1_tarski('#skF_3')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1337, c_1323])).
% 5.05/1.95  tff(c_1355, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_969, c_978, c_1343])).
% 5.05/1.95  tff(c_1149, plain, (![C_199, A_200, B_201]: (v4_relat_1(C_199, A_200) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.05/1.95  tff(c_1154, plain, (![A_200]: (v4_relat_1('#skF_5', A_200))), inference(resolution, [status(thm)], [c_966, c_1149])).
% 5.05/1.95  tff(c_58, plain, (![A_37]: (k1_relat_1('#skF_2'(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.05/1.95  tff(c_62, plain, (![A_37]: (v1_relat_1('#skF_2'(A_37)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.05/1.95  tff(c_110, plain, (![A_56]: (k1_relat_1(A_56)!=k1_xboole_0 | k1_xboole_0=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.05/1.95  tff(c_113, plain, (![A_37]: (k1_relat_1('#skF_2'(A_37))!=k1_xboole_0 | '#skF_2'(A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_110])).
% 5.05/1.95  tff(c_115, plain, (![A_37]: (k1_xboole_0!=A_37 | '#skF_2'(A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_113])).
% 5.05/1.95  tff(c_964, plain, (![A_37]: (A_37!='#skF_5' | '#skF_2'(A_37)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_958, c_958, c_115])).
% 5.05/1.95  tff(c_1053, plain, (![B_181, A_182]: (r1_tarski(k1_relat_1(B_181), A_182) | ~v4_relat_1(B_181, A_182) | ~v1_relat_1(B_181))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.05/1.95  tff(c_1065, plain, (![A_37, A_182]: (r1_tarski(A_37, A_182) | ~v4_relat_1('#skF_2'(A_37), A_182) | ~v1_relat_1('#skF_2'(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1053])).
% 5.05/1.95  tff(c_1072, plain, (![A_183, A_184]: (r1_tarski(A_183, A_184) | ~v4_relat_1('#skF_2'(A_183), A_184))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1065])).
% 5.05/1.95  tff(c_1075, plain, (![A_37, A_184]: (r1_tarski(A_37, A_184) | ~v4_relat_1('#skF_5', A_184) | A_37!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_964, c_1072])).
% 5.05/1.95  tff(c_1165, plain, (![A_184]: (r1_tarski('#skF_5', A_184))), inference(demodulation, [status(thm), theory('equality')], [c_1154, c_1075])).
% 5.05/1.95  tff(c_68, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.05/1.95  tff(c_970, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_958, c_68])).
% 5.05/1.95  tff(c_72, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.05/1.95  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/1.95  tff(c_64, plain, (![D_46, C_45, A_43, B_44]: (r2_hidden(k1_funct_1(D_46, C_45), k2_relset_1(A_43, B_44, D_46)) | k1_xboole_0=B_44 | ~r2_hidden(C_45, A_43) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(D_46, A_43, B_44) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.05/1.95  tff(c_1437, plain, (![D_249, C_250, A_251, B_252]: (r2_hidden(k1_funct_1(D_249, C_250), k2_relset_1(A_251, B_252, D_249)) | B_252='#skF_5' | ~r2_hidden(C_250, A_251) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~v1_funct_2(D_249, A_251, B_252) | ~v1_funct_1(D_249))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_64])).
% 5.05/1.95  tff(c_1448, plain, (![C_250, B_230, A_229]: (r2_hidden(k1_funct_1('#skF_5', C_250), '#skF_5') | B_230='#skF_5' | ~r2_hidden(C_250, A_229) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~v1_funct_2('#skF_5', A_229, B_230) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_1437])).
% 5.05/1.95  tff(c_2483, plain, (![C_356, B_357, A_358]: (r2_hidden(k1_funct_1('#skF_5', C_356), '#skF_5') | B_357='#skF_5' | ~r2_hidden(C_356, A_358) | ~v1_funct_2('#skF_5', A_358, B_357))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_966, c_1448])).
% 5.05/1.95  tff(c_2981, plain, (![A_410, B_411, B_412]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(A_410, B_411)), '#skF_5') | B_412='#skF_5' | ~v1_funct_2('#skF_5', A_410, B_412) | r1_tarski(A_410, B_411))), inference(resolution, [status(thm)], [c_6, c_2483])).
% 5.05/1.95  tff(c_2983, plain, (![B_411]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_tarski('#skF_3'), B_411)), '#skF_5') | '#skF_5'='#skF_4' | r1_tarski(k1_tarski('#skF_3'), B_411))), inference(resolution, [status(thm)], [c_72, c_2981])).
% 5.05/1.95  tff(c_2987, plain, (![B_413]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_tarski('#skF_3'), B_413)), '#skF_5') | r1_tarski(k1_tarski('#skF_3'), B_413))), inference(negUnitSimplification, [status(thm)], [c_970, c_2983])).
% 5.05/1.95  tff(c_46, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.05/1.95  tff(c_3001, plain, (![B_413]: (~r1_tarski('#skF_5', k1_funct_1('#skF_5', '#skF_1'(k1_tarski('#skF_3'), B_413))) | r1_tarski(k1_tarski('#skF_3'), B_413))), inference(resolution, [status(thm)], [c_2987, c_46])).
% 5.05/1.95  tff(c_3014, plain, (![B_414]: (r1_tarski(k1_tarski('#skF_3'), B_414))), inference(demodulation, [status(thm), theory('equality')], [c_1165, c_3001])).
% 5.05/1.95  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.05/1.95  tff(c_967, plain, (![A_8]: (r1_tarski('#skF_5', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_14])).
% 5.05/1.95  tff(c_997, plain, (![B_176, A_177]: (B_176=A_177 | ~r1_tarski(B_176, A_177) | ~r1_tarski(A_177, B_176))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.05/1.95  tff(c_1002, plain, (![A_8]: (A_8='#skF_5' | ~r1_tarski(A_8, '#skF_5'))), inference(resolution, [status(thm)], [c_967, c_997])).
% 5.05/1.95  tff(c_3086, plain, (k1_tarski('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_3014, c_1002])).
% 5.05/1.95  tff(c_3129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1355, c_3086])).
% 5.05/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.95  
% 5.05/1.95  Inference rules
% 5.05/1.95  ----------------------
% 5.05/1.95  #Ref     : 4
% 5.05/1.95  #Sup     : 613
% 5.05/1.95  #Fact    : 0
% 5.05/1.95  #Define  : 0
% 5.05/1.95  #Split   : 5
% 5.05/1.95  #Chain   : 0
% 5.05/1.95  #Close   : 0
% 5.05/1.95  
% 5.05/1.95  Ordering : KBO
% 5.05/1.95  
% 5.05/1.95  Simplification rules
% 5.05/1.95  ----------------------
% 5.05/1.95  #Subsume      : 251
% 5.05/1.95  #Demod        : 477
% 5.05/1.95  #Tautology    : 184
% 5.05/1.95  #SimpNegUnit  : 15
% 5.05/1.95  #BackRed      : 31
% 5.05/1.95  
% 5.05/1.95  #Partial instantiations: 0
% 5.05/1.95  #Strategies tried      : 1
% 5.05/1.95  
% 5.05/1.95  Timing (in seconds)
% 5.05/1.95  ----------------------
% 5.05/1.95  Preprocessing        : 0.36
% 5.05/1.95  Parsing              : 0.19
% 5.05/1.95  CNF conversion       : 0.02
% 5.05/1.95  Main loop            : 0.82
% 5.05/1.95  Inferencing          : 0.27
% 5.05/1.95  Reduction            : 0.26
% 5.05/1.95  Demodulation         : 0.19
% 5.05/1.95  BG Simplification    : 0.03
% 5.05/1.95  Subsumption          : 0.20
% 5.05/1.95  Abstraction          : 0.04
% 5.05/1.95  MUC search           : 0.00
% 5.05/1.95  Cooper               : 0.00
% 5.05/1.95  Total                : 1.22
% 5.05/1.95  Index Insertion      : 0.00
% 5.05/1.95  Index Deletion       : 0.00
% 5.05/1.95  Index Matching       : 0.00
% 5.05/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
