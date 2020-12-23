%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:36 EST 2020

% Result     : Theorem 9.65s
% Output     : CNFRefutation 9.91s
% Verified   : 
% Statistics : Number of formulae       :  267 (1285 expanded)
%              Number of leaves         :   49 ( 433 expanded)
%              Depth                    :   21
%              Number of atoms          :  492 (3425 expanded)
%              Number of equality atoms :  128 ( 861 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_155,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_145,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_102,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_15444,plain,(
    ! [C_814,A_815,B_816] :
      ( v1_relat_1(C_814)
      | ~ m1_subset_1(C_814,k1_zfmisc_1(k2_zfmisc_1(A_815,B_816))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_15466,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_15444])).

tff(c_48,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_15486,plain,
    ( k2_relat_1('#skF_8') != k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_15466,c_48])).

tff(c_15496,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_15486])).

tff(c_106,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_100,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_98,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_16390,plain,(
    ! [A_892,B_893,C_894] :
      ( k2_relset_1(A_892,B_893,C_894) = k2_relat_1(C_894)
      | ~ m1_subset_1(C_894,k1_zfmisc_1(k2_zfmisc_1(A_892,B_893))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16418,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_16390])).

tff(c_16433,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_16418])).

tff(c_58,plain,(
    ! [A_27] :
      ( k1_relat_1(k2_funct_1(A_27)) = k2_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_190,plain,(
    ! [A_68] :
      ( v1_funct_1(k2_funct_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_96,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6')))
    | ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_160,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_193,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_190,c_160])).

tff(c_196,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_193])).

tff(c_289,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_303,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_289])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_303])).

tff(c_316,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_334,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_404,plain,(
    ! [C_115,A_116,B_117] :
      ( v1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_422,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_404])).

tff(c_1245,plain,(
    ! [A_191,B_192,C_193] :
      ( k2_relset_1(A_191,B_192,C_193) = k2_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1270,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_1245])).

tff(c_1284,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1270])).

tff(c_429,plain,
    ( k2_relat_1('#skF_8') != k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_422,c_48])).

tff(c_443,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_1285,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_443])).

tff(c_104,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1038,plain,(
    ! [A_180,B_181,C_182] :
      ( k1_relset_1(A_180,B_181,C_182) = k1_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1071,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_1038])).

tff(c_1848,plain,(
    ! [B_230,A_231,C_232] :
      ( k1_xboole_0 = B_230
      | k1_relset_1(A_231,B_230,C_232) = A_231
      | ~ v1_funct_2(C_232,A_231,B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1876,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_1848])).

tff(c_1897,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1071,c_1876])).

tff(c_1898,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1285,c_1897])).

tff(c_56,plain,(
    ! [A_27] :
      ( k2_relat_1(k2_funct_1(A_27)) = k1_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_317,plain,(
    v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_812,plain,(
    ! [A_158] :
      ( k2_relat_1(k2_funct_1(A_158)) = k1_relat_1(A_158)
      | ~ v2_funct_1(A_158)
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_92,plain,(
    ! [A_43] :
      ( v1_funct_2(A_43,k1_relat_1(A_43),k2_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_7736,plain,(
    ! [A_454] :
      ( v1_funct_2(k2_funct_1(A_454),k1_relat_1(k2_funct_1(A_454)),k1_relat_1(A_454))
      | ~ v1_funct_1(k2_funct_1(A_454))
      | ~ v1_relat_1(k2_funct_1(A_454))
      | ~ v2_funct_1(A_454)
      | ~ v1_funct_1(A_454)
      | ~ v1_relat_1(A_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_92])).

tff(c_7745,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_7736])).

tff(c_7758,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_106,c_100,c_317,c_7745])).

tff(c_7761,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_7758])).

tff(c_7764,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_7761])).

tff(c_7768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_106,c_7764])).

tff(c_7770,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7758])).

tff(c_972,plain,(
    ! [A_174] :
      ( m1_subset_1(A_174,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_174),k2_relat_1(A_174))))
      | ~ v1_funct_1(A_174)
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_8409,plain,(
    ! [A_475] :
      ( m1_subset_1(k2_funct_1(A_475),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_475),k2_relat_1(k2_funct_1(A_475)))))
      | ~ v1_funct_1(k2_funct_1(A_475))
      | ~ v1_relat_1(k2_funct_1(A_475))
      | ~ v2_funct_1(A_475)
      | ~ v1_funct_1(A_475)
      | ~ v1_relat_1(A_475) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_972])).

tff(c_8445,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1(k2_funct_1('#skF_8')))))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_8409])).

tff(c_8467,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k2_relat_1(k2_funct_1('#skF_8'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_106,c_100,c_7770,c_317,c_8445])).

tff(c_8491,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_relat_1('#skF_8'))))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_8467])).

tff(c_8507,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_106,c_100,c_1898,c_8491])).

tff(c_8509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_8507])).

tff(c_8510,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8519,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8510,c_12])).

tff(c_385,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_2'(A_111,B_112),A_111)
      | r1_tarski(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_396,plain,(
    ! [A_12,B_112] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(A_12),B_112),A_12)
      | r1_tarski(k1_zfmisc_1(A_12),B_112) ) ),
    inference(resolution,[status(thm)],[c_385,c_20])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_318,plain,(
    ! [A_95] :
      ( v1_xboole_0(A_95)
      | r2_hidden('#skF_1'(A_95),A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_325,plain,(
    ! [A_95] :
      ( m1_subset_1('#skF_1'(A_95),A_95)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_318,c_40])).

tff(c_8650,plain,(
    ! [B_488,A_489] :
      ( v1_xboole_0(B_488)
      | ~ m1_subset_1(B_488,k1_zfmisc_1(A_489))
      | ~ v1_xboole_0(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9394,plain,(
    ! [A_554] :
      ( v1_xboole_0('#skF_1'(k1_zfmisc_1(A_554)))
      | ~ v1_xboole_0(A_554)
      | v1_xboole_0(k1_zfmisc_1(A_554)) ) ),
    inference(resolution,[status(thm)],[c_325,c_8650])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_398,plain,(
    ! [A_111,B_112] :
      ( ~ v1_xboole_0(A_111)
      | r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_385,c_2])).

tff(c_8618,plain,(
    ! [B_483,A_484] :
      ( B_483 = A_484
      | ~ r1_tarski(B_483,A_484)
      | ~ r1_tarski(A_484,B_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8770,plain,(
    ! [B_504,A_505] :
      ( B_504 = A_505
      | ~ r1_tarski(B_504,A_505)
      | ~ v1_xboole_0(A_505) ) ),
    inference(resolution,[status(thm)],[c_398,c_8618])).

tff(c_8780,plain,(
    ! [B_506,A_507] :
      ( B_506 = A_507
      | ~ v1_xboole_0(B_506)
      | ~ v1_xboole_0(A_507) ) ),
    inference(resolution,[status(thm)],[c_398,c_8770])).

tff(c_8791,plain,(
    ! [A_507] :
      ( A_507 = '#skF_8'
      | ~ v1_xboole_0(A_507) ) ),
    inference(resolution,[status(thm)],[c_8519,c_8780])).

tff(c_9989,plain,(
    ! [A_594] :
      ( '#skF_1'(k1_zfmisc_1(A_594)) = '#skF_8'
      | ~ v1_xboole_0(A_594)
      | v1_xboole_0(k1_zfmisc_1(A_594)) ) ),
    inference(resolution,[status(thm)],[c_9394,c_8791])).

tff(c_340,plain,(
    ! [C_100,A_101] :
      ( r2_hidden(C_100,k1_zfmisc_1(A_101))
      | ~ r1_tarski(C_100,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_352,plain,(
    ! [A_101,C_100] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_101))
      | ~ r1_tarski(C_100,A_101) ) ),
    inference(resolution,[status(thm)],[c_340,c_2])).

tff(c_10192,plain,(
    ! [C_604,A_605] :
      ( ~ r1_tarski(C_604,A_605)
      | '#skF_1'(k1_zfmisc_1(A_605)) = '#skF_8'
      | ~ v1_xboole_0(A_605) ) ),
    inference(resolution,[status(thm)],[c_9989,c_352])).

tff(c_10211,plain,(
    ! [B_606] :
      ( '#skF_1'(k1_zfmisc_1(B_606)) = '#skF_8'
      | ~ v1_xboole_0(B_606) ) ),
    inference(resolution,[status(thm)],[c_18,c_10192])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_328,plain,(
    ! [C_97,A_98] :
      ( r1_tarski(C_97,A_98)
      | ~ r2_hidden(C_97,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_333,plain,(
    ! [A_98] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_98)),A_98)
      | v1_xboole_0(k1_zfmisc_1(A_98)) ) ),
    inference(resolution,[status(thm)],[c_4,c_328])).

tff(c_10270,plain,(
    ! [B_610] :
      ( r1_tarski('#skF_8',B_610)
      | v1_xboole_0(k1_zfmisc_1(B_610))
      | ~ v1_xboole_0(B_610) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10211,c_333])).

tff(c_10336,plain,(
    ! [C_612,B_613] :
      ( ~ r1_tarski(C_612,B_613)
      | r1_tarski('#skF_8',B_613)
      | ~ v1_xboole_0(B_613) ) ),
    inference(resolution,[status(thm)],[c_10270,c_352])).

tff(c_10357,plain,(
    ! [B_11] :
      ( r1_tarski('#skF_8',B_11)
      | ~ v1_xboole_0(B_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_10336])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8693,plain,(
    ! [C_492,B_493,A_494] :
      ( r2_hidden(C_492,B_493)
      | ~ r2_hidden(C_492,A_494)
      | ~ r1_tarski(A_494,B_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11172,plain,(
    ! [A_669,B_670,B_671] :
      ( r2_hidden('#skF_2'(A_669,B_670),B_671)
      | ~ r1_tarski(A_669,B_671)
      | r1_tarski(A_669,B_670) ) ),
    inference(resolution,[status(thm)],[c_10,c_8693])).

tff(c_11194,plain,(
    ! [B_672,A_673,B_674] :
      ( ~ v1_xboole_0(B_672)
      | ~ r1_tarski(A_673,B_672)
      | r1_tarski(A_673,B_674) ) ),
    inference(resolution,[status(thm)],[c_11172,c_2])).

tff(c_11215,plain,(
    ! [B_674,B_11] :
      ( r1_tarski('#skF_8',B_674)
      | ~ v1_xboole_0(B_11) ) ),
    inference(resolution,[status(thm)],[c_10357,c_11194])).

tff(c_11222,plain,(
    ! [B_11] : ~ v1_xboole_0(B_11) ),
    inference(splitLeft,[status(thm)],[c_11215])).

tff(c_11242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11222,c_8519])).

tff(c_11281,plain,(
    ! [B_677] : r1_tarski('#skF_8',B_677) ),
    inference(splitRight,[status(thm)],[c_11215])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11336,plain,(
    ! [B_678] :
      ( B_678 = '#skF_8'
      | ~ r1_tarski(B_678,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_11281,c_14])).

tff(c_11432,plain,(
    ! [B_680] :
      ( '#skF_2'(k1_zfmisc_1('#skF_8'),B_680) = '#skF_8'
      | r1_tarski(k1_zfmisc_1('#skF_8'),B_680) ) ),
    inference(resolution,[status(thm)],[c_396,c_11336])).

tff(c_34,plain,(
    ! [A_17] : k2_zfmisc_1(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_419,plain,(
    ! [C_115] :
      ( v1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_404])).

tff(c_8585,plain,(
    ! [C_480] :
      ( v1_relat_1(C_480)
      | ~ m1_subset_1(C_480,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8510,c_419])).

tff(c_8595,plain,
    ( v1_relat_1('#skF_1'(k1_zfmisc_1('#skF_8')))
    | v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_325,c_8585])).

tff(c_9071,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_8595])).

tff(c_9090,plain,(
    ! [C_524] : ~ r1_tarski(C_524,'#skF_8') ),
    inference(resolution,[status(thm)],[c_9071,c_352])).

tff(c_9099,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_9090])).

tff(c_9101,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_8595])).

tff(c_9216,plain,(
    ! [A_535] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_535)),A_535)
      | v1_xboole_0(k1_zfmisc_1(A_535)) ) ),
    inference(resolution,[status(thm)],[c_4,c_328])).

tff(c_8623,plain,(
    ! [B_112,A_111] :
      ( B_112 = A_111
      | ~ r1_tarski(B_112,A_111)
      | ~ v1_xboole_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_398,c_8618])).

tff(c_9448,plain,(
    ! [A_559] :
      ( '#skF_1'(k1_zfmisc_1(A_559)) = A_559
      | ~ v1_xboole_0(A_559)
      | v1_xboole_0(k1_zfmisc_1(A_559)) ) ),
    inference(resolution,[status(thm)],[c_9216,c_8623])).

tff(c_9455,plain,
    ( '#skF_1'(k1_zfmisc_1('#skF_8')) = '#skF_8'
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_9448,c_9101])).

tff(c_9473,plain,(
    '#skF_1'(k1_zfmisc_1('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8519,c_9455])).

tff(c_9318,plain,(
    ! [A_546,B_547] :
      ( r2_hidden('#skF_1'(A_546),B_547)
      | ~ r1_tarski(A_546,B_547)
      | v1_xboole_0(A_546) ) ),
    inference(resolution,[status(thm)],[c_4,c_8693])).

tff(c_9333,plain,(
    ! [A_546,B_547] :
      ( m1_subset_1('#skF_1'(A_546),B_547)
      | ~ r1_tarski(A_546,B_547)
      | v1_xboole_0(A_546) ) ),
    inference(resolution,[status(thm)],[c_9318,c_40])).

tff(c_9484,plain,(
    ! [B_547] :
      ( m1_subset_1('#skF_8',B_547)
      | ~ r1_tarski(k1_zfmisc_1('#skF_8'),B_547)
      | v1_xboole_0(k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9473,c_9333])).

tff(c_9502,plain,(
    ! [B_547] :
      ( m1_subset_1('#skF_8',B_547)
      | ~ r1_tarski(k1_zfmisc_1('#skF_8'),B_547) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9101,c_9484])).

tff(c_11834,plain,(
    ! [B_686] :
      ( m1_subset_1('#skF_8',B_686)
      | '#skF_2'(k1_zfmisc_1('#skF_8'),B_686) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_11432,c_9502])).

tff(c_22,plain,(
    ! [C_16,A_12] :
      ( r2_hidden(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8572,plain,(
    ! [A_478,B_479] :
      ( ~ r2_hidden('#skF_2'(A_478,B_479),B_479)
      | r1_tarski(A_478,B_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10455,plain,(
    ! [A_617,A_618] :
      ( r1_tarski(A_617,k1_zfmisc_1(A_618))
      | ~ r1_tarski('#skF_2'(A_617,k1_zfmisc_1(A_618)),A_618) ) ),
    inference(resolution,[status(thm)],[c_22,c_8572])).

tff(c_10460,plain,(
    ! [A_617,B_112] :
      ( r1_tarski(A_617,k1_zfmisc_1(B_112))
      | ~ v1_xboole_0('#skF_2'(A_617,k1_zfmisc_1(B_112))) ) ),
    inference(resolution,[status(thm)],[c_398,c_10455])).

tff(c_11856,plain,(
    ! [B_112] :
      ( r1_tarski(k1_zfmisc_1('#skF_8'),k1_zfmisc_1(B_112))
      | ~ v1_xboole_0('#skF_8')
      | m1_subset_1('#skF_8',k1_zfmisc_1(B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11834,c_10460])).

tff(c_13818,plain,(
    ! [B_745] :
      ( r1_tarski(k1_zfmisc_1('#skF_8'),k1_zfmisc_1(B_745))
      | m1_subset_1('#skF_8',k1_zfmisc_1(B_745)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8519,c_11856])).

tff(c_13866,plain,(
    ! [B_745] : m1_subset_1('#skF_8',k1_zfmisc_1(B_745)) ),
    inference(resolution,[status(thm)],[c_13818,c_9502])).

tff(c_8511,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_8525,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8510,c_8511])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8518,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8510,c_8510,c_46])).

tff(c_8862,plain,(
    ! [A_512] :
      ( k2_relat_1(k2_funct_1(A_512)) = k1_relat_1(A_512)
      | ~ v2_funct_1(A_512)
      | ~ v1_funct_1(A_512)
      | ~ v1_relat_1(A_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15248,plain,(
    ! [A_800] :
      ( v1_funct_2(k2_funct_1(A_800),k1_relat_1(k2_funct_1(A_800)),k1_relat_1(A_800))
      | ~ v1_funct_1(k2_funct_1(A_800))
      | ~ v1_relat_1(k2_funct_1(A_800))
      | ~ v2_funct_1(A_800)
      | ~ v1_funct_1(A_800)
      | ~ v1_relat_1(A_800) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8862,c_92])).

tff(c_15260,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_8')
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_8518,c_15248])).

tff(c_15264,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_8')
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_106,c_100,c_317,c_15260])).

tff(c_15265,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_15264])).

tff(c_15268,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_15265])).

tff(c_15272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_106,c_15268])).

tff(c_15274,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_15264])).

tff(c_50,plain,(
    ! [A_25] :
      ( k1_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8514,plain,(
    ! [A_25] :
      ( k1_relat_1(A_25) != '#skF_8'
      | A_25 = '#skF_8'
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8510,c_8510,c_50])).

tff(c_15281,plain,
    ( k1_relat_1(k2_funct_1('#skF_8')) != '#skF_8'
    | k2_funct_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_15274,c_8514])).

tff(c_15385,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_15281])).

tff(c_15388,plain,
    ( k2_relat_1('#skF_8') != '#skF_8'
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_15385])).

tff(c_15391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_106,c_100,c_8525,c_15388])).

tff(c_15392,plain,(
    k2_funct_1('#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_15281])).

tff(c_36,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8515,plain,(
    ! [B_18] : k2_zfmisc_1('#skF_8',B_18) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8510,c_8510,c_36])).

tff(c_9144,plain,(
    ! [A_528,B_529,C_530] :
      ( k2_relset_1(A_528,B_529,C_530) = k2_relat_1(C_530)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_528,B_529))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_9167,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_9144])).

tff(c_9173,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8525,c_9167])).

tff(c_9176,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9173,c_334])).

tff(c_9181,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8515,c_9176])).

tff(c_15397,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15392,c_9181])).

tff(c_15406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13866,c_15397])).

tff(c_15407,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_15408,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_16459,plain,(
    ! [A_895,B_896,C_897] :
      ( k1_relset_1(A_895,B_896,C_897) = k1_relat_1(C_897)
      | ~ m1_subset_1(C_897,k1_zfmisc_1(k2_zfmisc_1(A_895,B_896))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16499,plain,(
    k1_relset_1('#skF_7','#skF_6',k2_funct_1('#skF_8')) = k1_relat_1(k2_funct_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_15408,c_16459])).

tff(c_16860,plain,(
    ! [B_923,C_924,A_925] :
      ( k1_xboole_0 = B_923
      | v1_funct_2(C_924,A_925,B_923)
      | k1_relset_1(A_925,B_923,C_924) != A_925
      | ~ m1_subset_1(C_924,k1_zfmisc_1(k2_zfmisc_1(A_925,B_923))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_16884,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | k1_relset_1('#skF_7','#skF_6',k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_15408,c_16860])).

tff(c_16909,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16499,c_16884])).

tff(c_16910,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_15407,c_16909])).

tff(c_16916,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_16910])).

tff(c_16919,plain,
    ( k2_relat_1('#skF_8') != '#skF_7'
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_16916])).

tff(c_16922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15466,c_106,c_100,c_16433,c_16919])).

tff(c_16923,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16910])).

tff(c_16964,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16923,c_12])).

tff(c_16960,plain,(
    ! [B_18] : k2_zfmisc_1('#skF_6',B_18) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16923,c_16923,c_36])).

tff(c_15705,plain,(
    ! [B_845,A_846] :
      ( v1_xboole_0(B_845)
      | ~ m1_subset_1(B_845,k1_zfmisc_1(A_846))
      | ~ v1_xboole_0(A_846) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_15738,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_102,c_15705])).

tff(c_15808,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_15738])).

tff(c_17054,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16960,c_15808])).

tff(c_17058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16964,c_17054])).

tff(c_17059,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_15738])).

tff(c_42,plain,(
    ! [A_24] :
      ( v1_xboole_0(k2_relat_1(A_24))
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_15528,plain,(
    ! [A_821,B_822] :
      ( r2_hidden('#skF_2'(A_821,B_822),A_821)
      | r1_tarski(A_821,B_822) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15541,plain,(
    ! [A_821,B_822] :
      ( ~ v1_xboole_0(A_821)
      | r1_tarski(A_821,B_822) ) ),
    inference(resolution,[status(thm)],[c_15528,c_2])).

tff(c_15600,plain,(
    ! [B_832,A_833] :
      ( B_832 = A_833
      | ~ r1_tarski(B_832,A_833)
      | ~ r1_tarski(A_833,B_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_15638,plain,(
    ! [B_838,A_839] :
      ( B_838 = A_839
      | ~ r1_tarski(B_838,A_839)
      | ~ v1_xboole_0(A_839) ) ),
    inference(resolution,[status(thm)],[c_15541,c_15600])).

tff(c_15648,plain,(
    ! [B_840,A_841] :
      ( B_840 = A_841
      | ~ v1_xboole_0(B_840)
      | ~ v1_xboole_0(A_841) ) ),
    inference(resolution,[status(thm)],[c_15541,c_15638])).

tff(c_15655,plain,(
    ! [A_842] :
      ( k1_xboole_0 = A_842
      | ~ v1_xboole_0(A_842) ) ),
    inference(resolution,[status(thm)],[c_12,c_15648])).

tff(c_15662,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) = k1_xboole_0
      | ~ v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_42,c_15655])).

tff(c_17063,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17059,c_15662])).

tff(c_17075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15496,c_17063])).

tff(c_17076,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_15486])).

tff(c_17083,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17076,c_17076,c_46])).

tff(c_15485,plain,
    ( k1_relat_1('#skF_8') != k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_15466,c_50])).

tff(c_15495,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_15485])).

tff(c_17105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17083,c_17076,c_15495])).

tff(c_17106,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_15485])).

tff(c_17136,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17106,c_12])).

tff(c_15467,plain,(
    ! [A_817,B_818] : m1_subset_1('#skF_5'(A_817,B_818),k1_zfmisc_1(k2_zfmisc_1(A_817,B_818))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_15473,plain,(
    ! [B_18] : m1_subset_1('#skF_5'(k1_xboole_0,B_18),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_15467])).

tff(c_17204,plain,(
    ! [B_938] : m1_subset_1('#skF_5'('#skF_8',B_938),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17106,c_17106,c_15473])).

tff(c_38,plain,(
    ! [B_21,A_19] :
      ( v1_xboole_0(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_19))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_17207,plain,(
    ! [B_938] :
      ( v1_xboole_0('#skF_5'('#skF_8',B_938))
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_17204,c_38])).

tff(c_17210,plain,(
    ! [B_938] : v1_xboole_0('#skF_5'('#skF_8',B_938)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17136,c_17207])).

tff(c_17668,plain,(
    ! [A_981,B_982] :
      ( r2_hidden('#skF_2'(A_981,B_982),A_981)
      | r1_tarski(A_981,B_982) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_17681,plain,(
    ! [A_981,B_982] :
      ( ~ v1_xboole_0(A_981)
      | r1_tarski(A_981,B_982) ) ),
    inference(resolution,[status(thm)],[c_17668,c_2])).

tff(c_17682,plain,(
    ! [A_983,B_984] :
      ( ~ v1_xboole_0(A_983)
      | r1_tarski(A_983,B_984) ) ),
    inference(resolution,[status(thm)],[c_17668,c_2])).

tff(c_17748,plain,(
    ! [B_990,A_991] :
      ( B_990 = A_991
      | ~ r1_tarski(B_990,A_991)
      | ~ v1_xboole_0(A_991) ) ),
    inference(resolution,[status(thm)],[c_17682,c_14])).

tff(c_17758,plain,(
    ! [B_992,A_993] :
      ( B_992 = A_993
      | ~ v1_xboole_0(B_992)
      | ~ v1_xboole_0(A_993) ) ),
    inference(resolution,[status(thm)],[c_17681,c_17748])).

tff(c_17771,plain,(
    ! [A_994] :
      ( A_994 = '#skF_8'
      | ~ v1_xboole_0(A_994) ) ),
    inference(resolution,[status(thm)],[c_17136,c_17758])).

tff(c_17851,plain,(
    ! [B_1002] : '#skF_5'('#skF_8',B_1002) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_17210,c_17771])).

tff(c_78,plain,(
    ! [A_40,B_41] : v1_funct_2('#skF_5'(A_40,B_41),A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_17862,plain,(
    ! [B_1002] : v1_funct_2('#skF_8','#skF_8',B_1002) ),
    inference(superposition,[status(thm),theory(equality)],[c_17851,c_78])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_17134,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17106,c_17106,c_44])).

tff(c_18141,plain,(
    ! [A_1023,B_1024,C_1025] :
      ( k2_relset_1(A_1023,B_1024,C_1025) = k2_relat_1(C_1025)
      | ~ m1_subset_1(C_1025,k1_zfmisc_1(k2_zfmisc_1(A_1023,B_1024))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18164,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_18141])).

tff(c_18171,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_17134,c_18164])).

tff(c_17617,plain,(
    ! [A_980] :
      ( k1_relat_1(k2_funct_1(A_980)) = k2_relat_1(A_980)
      | ~ v2_funct_1(A_980)
      | ~ v1_funct_1(A_980)
      | ~ v1_relat_1(A_980) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15464,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_15408,c_15444])).

tff(c_15493,plain,
    ( k1_relat_1(k2_funct_1('#skF_8')) != k1_xboole_0
    | k2_funct_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15464,c_50])).

tff(c_17260,plain,
    ( k1_relat_1(k2_funct_1('#skF_8')) != '#skF_8'
    | k2_funct_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17106,c_17106,c_15493])).

tff(c_17261,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_17260])).

tff(c_17626,plain,
    ( k2_relat_1('#skF_8') != '#skF_8'
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_17617,c_17261])).

tff(c_17633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15466,c_106,c_100,c_17134,c_17626])).

tff(c_17634,plain,(
    k2_funct_1('#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_17260])).

tff(c_17638,plain,(
    ~ v1_funct_2('#skF_8','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17634,c_15407])).

tff(c_18175,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18171,c_17638])).

tff(c_18183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17862,c_18175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.65/3.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.65/3.61  
% 9.65/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.65/3.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 9.65/3.61  
% 9.65/3.61  %Foreground sorts:
% 9.65/3.61  
% 9.65/3.61  
% 9.65/3.61  %Background operators:
% 9.65/3.61  
% 9.65/3.61  
% 9.65/3.61  %Foreground operators:
% 9.65/3.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.65/3.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.65/3.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.65/3.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.65/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.65/3.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.65/3.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.65/3.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.65/3.61  tff('#skF_7', type, '#skF_7': $i).
% 9.65/3.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.65/3.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.65/3.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.65/3.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.65/3.61  tff('#skF_6', type, '#skF_6': $i).
% 9.65/3.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.65/3.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.65/3.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.65/3.61  tff('#skF_8', type, '#skF_8': $i).
% 9.65/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.65/3.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.65/3.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.65/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.65/3.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.65/3.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.65/3.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.65/3.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.65/3.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.65/3.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.65/3.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.65/3.61  
% 9.91/3.64  tff(f_172, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.91/3.64  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.91/3.64  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 9.91/3.64  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.91/3.64  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.91/3.64  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.91/3.64  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.91/3.64  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.91/3.64  tff(f_155, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 9.91/3.64  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.91/3.64  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.91/3.64  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.91/3.64  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.91/3.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.91/3.64  tff(f_69, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 9.91/3.64  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.91/3.64  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.91/3.64  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 9.91/3.64  tff(f_73, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 9.91/3.64  tff(f_145, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 9.91/3.64  tff(c_102, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.91/3.64  tff(c_15444, plain, (![C_814, A_815, B_816]: (v1_relat_1(C_814) | ~m1_subset_1(C_814, k1_zfmisc_1(k2_zfmisc_1(A_815, B_816))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.91/3.64  tff(c_15466, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_15444])).
% 9.91/3.64  tff(c_48, plain, (![A_25]: (k2_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.91/3.64  tff(c_15486, plain, (k2_relat_1('#skF_8')!=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_15466, c_48])).
% 9.91/3.64  tff(c_15496, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_15486])).
% 9.91/3.64  tff(c_106, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.91/3.64  tff(c_100, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.91/3.64  tff(c_98, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.91/3.64  tff(c_16390, plain, (![A_892, B_893, C_894]: (k2_relset_1(A_892, B_893, C_894)=k2_relat_1(C_894) | ~m1_subset_1(C_894, k1_zfmisc_1(k2_zfmisc_1(A_892, B_893))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.91/3.64  tff(c_16418, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_16390])).
% 9.91/3.64  tff(c_16433, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_16418])).
% 9.91/3.64  tff(c_58, plain, (![A_27]: (k1_relat_1(k2_funct_1(A_27))=k2_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.91/3.64  tff(c_190, plain, (![A_68]: (v1_funct_1(k2_funct_1(A_68)) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.91/3.64  tff(c_96, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.91/3.64  tff(c_160, plain, (~v1_funct_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_96])).
% 9.91/3.64  tff(c_193, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_190, c_160])).
% 9.91/3.64  tff(c_196, plain, (~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_193])).
% 9.91/3.64  tff(c_289, plain, (![C_92, A_93, B_94]: (v1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.91/3.64  tff(c_303, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_289])).
% 9.91/3.64  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_303])).
% 9.91/3.64  tff(c_316, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | ~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_96])).
% 9.91/3.64  tff(c_334, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_316])).
% 9.91/3.64  tff(c_404, plain, (![C_115, A_116, B_117]: (v1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.91/3.64  tff(c_422, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_404])).
% 9.91/3.64  tff(c_1245, plain, (![A_191, B_192, C_193]: (k2_relset_1(A_191, B_192, C_193)=k2_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.91/3.64  tff(c_1270, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_1245])).
% 9.91/3.64  tff(c_1284, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1270])).
% 9.91/3.64  tff(c_429, plain, (k2_relat_1('#skF_8')!=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_422, c_48])).
% 9.91/3.64  tff(c_443, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_429])).
% 9.91/3.64  tff(c_1285, plain, (k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_443])).
% 9.91/3.64  tff(c_104, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.91/3.64  tff(c_1038, plain, (![A_180, B_181, C_182]: (k1_relset_1(A_180, B_181, C_182)=k1_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.91/3.64  tff(c_1071, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_1038])).
% 9.91/3.64  tff(c_1848, plain, (![B_230, A_231, C_232]: (k1_xboole_0=B_230 | k1_relset_1(A_231, B_230, C_232)=A_231 | ~v1_funct_2(C_232, A_231, B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.91/3.64  tff(c_1876, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_102, c_1848])).
% 9.91/3.64  tff(c_1897, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1071, c_1876])).
% 9.91/3.64  tff(c_1898, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1285, c_1897])).
% 9.91/3.64  tff(c_56, plain, (![A_27]: (k2_relat_1(k2_funct_1(A_27))=k1_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.91/3.64  tff(c_54, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.91/3.64  tff(c_317, plain, (v1_funct_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_96])).
% 9.91/3.64  tff(c_812, plain, (![A_158]: (k2_relat_1(k2_funct_1(A_158))=k1_relat_1(A_158) | ~v2_funct_1(A_158) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.91/3.64  tff(c_92, plain, (![A_43]: (v1_funct_2(A_43, k1_relat_1(A_43), k2_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.91/3.64  tff(c_7736, plain, (![A_454]: (v1_funct_2(k2_funct_1(A_454), k1_relat_1(k2_funct_1(A_454)), k1_relat_1(A_454)) | ~v1_funct_1(k2_funct_1(A_454)) | ~v1_relat_1(k2_funct_1(A_454)) | ~v2_funct_1(A_454) | ~v1_funct_1(A_454) | ~v1_relat_1(A_454))), inference(superposition, [status(thm), theory('equality')], [c_812, c_92])).
% 9.91/3.64  tff(c_7745, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1898, c_7736])).
% 9.91/3.64  tff(c_7758, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_6') | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_106, c_100, c_317, c_7745])).
% 9.91/3.64  tff(c_7761, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_7758])).
% 9.91/3.64  tff(c_7764, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_7761])).
% 9.91/3.64  tff(c_7768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_106, c_7764])).
% 9.91/3.64  tff(c_7770, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_7758])).
% 9.91/3.64  tff(c_972, plain, (![A_174]: (m1_subset_1(A_174, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_174), k2_relat_1(A_174)))) | ~v1_funct_1(A_174) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.91/3.64  tff(c_8409, plain, (![A_475]: (m1_subset_1(k2_funct_1(A_475), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_475), k2_relat_1(k2_funct_1(A_475))))) | ~v1_funct_1(k2_funct_1(A_475)) | ~v1_relat_1(k2_funct_1(A_475)) | ~v2_funct_1(A_475) | ~v1_funct_1(A_475) | ~v1_relat_1(A_475))), inference(superposition, [status(thm), theory('equality')], [c_58, c_972])).
% 9.91/3.64  tff(c_8445, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1(k2_funct_1('#skF_8'))))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1284, c_8409])).
% 9.91/3.64  tff(c_8467, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k2_relat_1(k2_funct_1('#skF_8')))))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_106, c_100, c_7770, c_317, c_8445])).
% 9.91/3.64  tff(c_8491, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_relat_1('#skF_8')))) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_56, c_8467])).
% 9.91/3.64  tff(c_8507, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_106, c_100, c_1898, c_8491])).
% 9.91/3.64  tff(c_8509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_8507])).
% 9.91/3.64  tff(c_8510, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_429])).
% 9.91/3.64  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.91/3.64  tff(c_8519, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8510, c_12])).
% 9.91/3.64  tff(c_385, plain, (![A_111, B_112]: (r2_hidden('#skF_2'(A_111, B_112), A_111) | r1_tarski(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.91/3.64  tff(c_20, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.91/3.64  tff(c_396, plain, (![A_12, B_112]: (r1_tarski('#skF_2'(k1_zfmisc_1(A_12), B_112), A_12) | r1_tarski(k1_zfmisc_1(A_12), B_112))), inference(resolution, [status(thm)], [c_385, c_20])).
% 9.91/3.64  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.91/3.64  tff(c_318, plain, (![A_95]: (v1_xboole_0(A_95) | r2_hidden('#skF_1'(A_95), A_95))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.91/3.64  tff(c_40, plain, (![A_22, B_23]: (m1_subset_1(A_22, B_23) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.91/3.64  tff(c_325, plain, (![A_95]: (m1_subset_1('#skF_1'(A_95), A_95) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_318, c_40])).
% 9.91/3.64  tff(c_8650, plain, (![B_488, A_489]: (v1_xboole_0(B_488) | ~m1_subset_1(B_488, k1_zfmisc_1(A_489)) | ~v1_xboole_0(A_489))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.91/3.64  tff(c_9394, plain, (![A_554]: (v1_xboole_0('#skF_1'(k1_zfmisc_1(A_554))) | ~v1_xboole_0(A_554) | v1_xboole_0(k1_zfmisc_1(A_554)))), inference(resolution, [status(thm)], [c_325, c_8650])).
% 9.91/3.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.91/3.64  tff(c_398, plain, (![A_111, B_112]: (~v1_xboole_0(A_111) | r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_385, c_2])).
% 9.91/3.64  tff(c_8618, plain, (![B_483, A_484]: (B_483=A_484 | ~r1_tarski(B_483, A_484) | ~r1_tarski(A_484, B_483))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.91/3.64  tff(c_8770, plain, (![B_504, A_505]: (B_504=A_505 | ~r1_tarski(B_504, A_505) | ~v1_xboole_0(A_505))), inference(resolution, [status(thm)], [c_398, c_8618])).
% 9.91/3.64  tff(c_8780, plain, (![B_506, A_507]: (B_506=A_507 | ~v1_xboole_0(B_506) | ~v1_xboole_0(A_507))), inference(resolution, [status(thm)], [c_398, c_8770])).
% 9.91/3.64  tff(c_8791, plain, (![A_507]: (A_507='#skF_8' | ~v1_xboole_0(A_507))), inference(resolution, [status(thm)], [c_8519, c_8780])).
% 9.91/3.64  tff(c_9989, plain, (![A_594]: ('#skF_1'(k1_zfmisc_1(A_594))='#skF_8' | ~v1_xboole_0(A_594) | v1_xboole_0(k1_zfmisc_1(A_594)))), inference(resolution, [status(thm)], [c_9394, c_8791])).
% 9.91/3.64  tff(c_340, plain, (![C_100, A_101]: (r2_hidden(C_100, k1_zfmisc_1(A_101)) | ~r1_tarski(C_100, A_101))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.91/3.64  tff(c_352, plain, (![A_101, C_100]: (~v1_xboole_0(k1_zfmisc_1(A_101)) | ~r1_tarski(C_100, A_101))), inference(resolution, [status(thm)], [c_340, c_2])).
% 9.91/3.64  tff(c_10192, plain, (![C_604, A_605]: (~r1_tarski(C_604, A_605) | '#skF_1'(k1_zfmisc_1(A_605))='#skF_8' | ~v1_xboole_0(A_605))), inference(resolution, [status(thm)], [c_9989, c_352])).
% 9.91/3.64  tff(c_10211, plain, (![B_606]: ('#skF_1'(k1_zfmisc_1(B_606))='#skF_8' | ~v1_xboole_0(B_606))), inference(resolution, [status(thm)], [c_18, c_10192])).
% 9.91/3.64  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.91/3.64  tff(c_328, plain, (![C_97, A_98]: (r1_tarski(C_97, A_98) | ~r2_hidden(C_97, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.91/3.64  tff(c_333, plain, (![A_98]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_98)), A_98) | v1_xboole_0(k1_zfmisc_1(A_98)))), inference(resolution, [status(thm)], [c_4, c_328])).
% 9.91/3.64  tff(c_10270, plain, (![B_610]: (r1_tarski('#skF_8', B_610) | v1_xboole_0(k1_zfmisc_1(B_610)) | ~v1_xboole_0(B_610))), inference(superposition, [status(thm), theory('equality')], [c_10211, c_333])).
% 9.91/3.64  tff(c_10336, plain, (![C_612, B_613]: (~r1_tarski(C_612, B_613) | r1_tarski('#skF_8', B_613) | ~v1_xboole_0(B_613))), inference(resolution, [status(thm)], [c_10270, c_352])).
% 9.91/3.64  tff(c_10357, plain, (![B_11]: (r1_tarski('#skF_8', B_11) | ~v1_xboole_0(B_11))), inference(resolution, [status(thm)], [c_18, c_10336])).
% 9.91/3.64  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.91/3.64  tff(c_8693, plain, (![C_492, B_493, A_494]: (r2_hidden(C_492, B_493) | ~r2_hidden(C_492, A_494) | ~r1_tarski(A_494, B_493))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.91/3.64  tff(c_11172, plain, (![A_669, B_670, B_671]: (r2_hidden('#skF_2'(A_669, B_670), B_671) | ~r1_tarski(A_669, B_671) | r1_tarski(A_669, B_670))), inference(resolution, [status(thm)], [c_10, c_8693])).
% 9.91/3.64  tff(c_11194, plain, (![B_672, A_673, B_674]: (~v1_xboole_0(B_672) | ~r1_tarski(A_673, B_672) | r1_tarski(A_673, B_674))), inference(resolution, [status(thm)], [c_11172, c_2])).
% 9.91/3.64  tff(c_11215, plain, (![B_674, B_11]: (r1_tarski('#skF_8', B_674) | ~v1_xboole_0(B_11))), inference(resolution, [status(thm)], [c_10357, c_11194])).
% 9.91/3.64  tff(c_11222, plain, (![B_11]: (~v1_xboole_0(B_11))), inference(splitLeft, [status(thm)], [c_11215])).
% 9.91/3.64  tff(c_11242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11222, c_8519])).
% 9.91/3.64  tff(c_11281, plain, (![B_677]: (r1_tarski('#skF_8', B_677))), inference(splitRight, [status(thm)], [c_11215])).
% 9.91/3.64  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.91/3.64  tff(c_11336, plain, (![B_678]: (B_678='#skF_8' | ~r1_tarski(B_678, '#skF_8'))), inference(resolution, [status(thm)], [c_11281, c_14])).
% 9.91/3.64  tff(c_11432, plain, (![B_680]: ('#skF_2'(k1_zfmisc_1('#skF_8'), B_680)='#skF_8' | r1_tarski(k1_zfmisc_1('#skF_8'), B_680))), inference(resolution, [status(thm)], [c_396, c_11336])).
% 9.91/3.64  tff(c_34, plain, (![A_17]: (k2_zfmisc_1(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.91/3.64  tff(c_419, plain, (![C_115]: (v1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_404])).
% 9.91/3.64  tff(c_8585, plain, (![C_480]: (v1_relat_1(C_480) | ~m1_subset_1(C_480, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_8510, c_419])).
% 9.91/3.64  tff(c_8595, plain, (v1_relat_1('#skF_1'(k1_zfmisc_1('#skF_8'))) | v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_325, c_8585])).
% 9.91/3.64  tff(c_9071, plain, (v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_8595])).
% 9.91/3.64  tff(c_9090, plain, (![C_524]: (~r1_tarski(C_524, '#skF_8'))), inference(resolution, [status(thm)], [c_9071, c_352])).
% 9.91/3.64  tff(c_9099, plain, $false, inference(resolution, [status(thm)], [c_18, c_9090])).
% 9.91/3.64  tff(c_9101, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitRight, [status(thm)], [c_8595])).
% 9.91/3.64  tff(c_9216, plain, (![A_535]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_535)), A_535) | v1_xboole_0(k1_zfmisc_1(A_535)))), inference(resolution, [status(thm)], [c_4, c_328])).
% 9.91/3.64  tff(c_8623, plain, (![B_112, A_111]: (B_112=A_111 | ~r1_tarski(B_112, A_111) | ~v1_xboole_0(A_111))), inference(resolution, [status(thm)], [c_398, c_8618])).
% 9.91/3.64  tff(c_9448, plain, (![A_559]: ('#skF_1'(k1_zfmisc_1(A_559))=A_559 | ~v1_xboole_0(A_559) | v1_xboole_0(k1_zfmisc_1(A_559)))), inference(resolution, [status(thm)], [c_9216, c_8623])).
% 9.91/3.64  tff(c_9455, plain, ('#skF_1'(k1_zfmisc_1('#skF_8'))='#skF_8' | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_9448, c_9101])).
% 9.91/3.64  tff(c_9473, plain, ('#skF_1'(k1_zfmisc_1('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8519, c_9455])).
% 9.91/3.64  tff(c_9318, plain, (![A_546, B_547]: (r2_hidden('#skF_1'(A_546), B_547) | ~r1_tarski(A_546, B_547) | v1_xboole_0(A_546))), inference(resolution, [status(thm)], [c_4, c_8693])).
% 9.91/3.64  tff(c_9333, plain, (![A_546, B_547]: (m1_subset_1('#skF_1'(A_546), B_547) | ~r1_tarski(A_546, B_547) | v1_xboole_0(A_546))), inference(resolution, [status(thm)], [c_9318, c_40])).
% 9.91/3.64  tff(c_9484, plain, (![B_547]: (m1_subset_1('#skF_8', B_547) | ~r1_tarski(k1_zfmisc_1('#skF_8'), B_547) | v1_xboole_0(k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_9473, c_9333])).
% 9.91/3.64  tff(c_9502, plain, (![B_547]: (m1_subset_1('#skF_8', B_547) | ~r1_tarski(k1_zfmisc_1('#skF_8'), B_547))), inference(negUnitSimplification, [status(thm)], [c_9101, c_9484])).
% 9.91/3.64  tff(c_11834, plain, (![B_686]: (m1_subset_1('#skF_8', B_686) | '#skF_2'(k1_zfmisc_1('#skF_8'), B_686)='#skF_8')), inference(resolution, [status(thm)], [c_11432, c_9502])).
% 9.91/3.64  tff(c_22, plain, (![C_16, A_12]: (r2_hidden(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.91/3.64  tff(c_8572, plain, (![A_478, B_479]: (~r2_hidden('#skF_2'(A_478, B_479), B_479) | r1_tarski(A_478, B_479))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.91/3.64  tff(c_10455, plain, (![A_617, A_618]: (r1_tarski(A_617, k1_zfmisc_1(A_618)) | ~r1_tarski('#skF_2'(A_617, k1_zfmisc_1(A_618)), A_618))), inference(resolution, [status(thm)], [c_22, c_8572])).
% 9.91/3.64  tff(c_10460, plain, (![A_617, B_112]: (r1_tarski(A_617, k1_zfmisc_1(B_112)) | ~v1_xboole_0('#skF_2'(A_617, k1_zfmisc_1(B_112))))), inference(resolution, [status(thm)], [c_398, c_10455])).
% 9.91/3.64  tff(c_11856, plain, (![B_112]: (r1_tarski(k1_zfmisc_1('#skF_8'), k1_zfmisc_1(B_112)) | ~v1_xboole_0('#skF_8') | m1_subset_1('#skF_8', k1_zfmisc_1(B_112)))), inference(superposition, [status(thm), theory('equality')], [c_11834, c_10460])).
% 9.91/3.64  tff(c_13818, plain, (![B_745]: (r1_tarski(k1_zfmisc_1('#skF_8'), k1_zfmisc_1(B_745)) | m1_subset_1('#skF_8', k1_zfmisc_1(B_745)))), inference(demodulation, [status(thm), theory('equality')], [c_8519, c_11856])).
% 9.91/3.64  tff(c_13866, plain, (![B_745]: (m1_subset_1('#skF_8', k1_zfmisc_1(B_745)))), inference(resolution, [status(thm)], [c_13818, c_9502])).
% 9.91/3.64  tff(c_8511, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_429])).
% 9.91/3.64  tff(c_8525, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8510, c_8511])).
% 9.91/3.64  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.91/3.64  tff(c_8518, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8510, c_8510, c_46])).
% 9.91/3.64  tff(c_8862, plain, (![A_512]: (k2_relat_1(k2_funct_1(A_512))=k1_relat_1(A_512) | ~v2_funct_1(A_512) | ~v1_funct_1(A_512) | ~v1_relat_1(A_512))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.91/3.64  tff(c_15248, plain, (![A_800]: (v1_funct_2(k2_funct_1(A_800), k1_relat_1(k2_funct_1(A_800)), k1_relat_1(A_800)) | ~v1_funct_1(k2_funct_1(A_800)) | ~v1_relat_1(k2_funct_1(A_800)) | ~v2_funct_1(A_800) | ~v1_funct_1(A_800) | ~v1_relat_1(A_800))), inference(superposition, [status(thm), theory('equality')], [c_8862, c_92])).
% 9.91/3.64  tff(c_15260, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_8') | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_8518, c_15248])).
% 9.91/3.64  tff(c_15264, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_8') | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_106, c_100, c_317, c_15260])).
% 9.91/3.64  tff(c_15265, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_15264])).
% 9.91/3.64  tff(c_15268, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_15265])).
% 9.91/3.64  tff(c_15272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_106, c_15268])).
% 9.91/3.64  tff(c_15274, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_15264])).
% 9.91/3.64  tff(c_50, plain, (![A_25]: (k1_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.91/3.64  tff(c_8514, plain, (![A_25]: (k1_relat_1(A_25)!='#skF_8' | A_25='#skF_8' | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_8510, c_8510, c_50])).
% 9.91/3.64  tff(c_15281, plain, (k1_relat_1(k2_funct_1('#skF_8'))!='#skF_8' | k2_funct_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_15274, c_8514])).
% 9.91/3.64  tff(c_15385, plain, (k1_relat_1(k2_funct_1('#skF_8'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_15281])).
% 9.91/3.64  tff(c_15388, plain, (k2_relat_1('#skF_8')!='#skF_8' | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_58, c_15385])).
% 9.91/3.64  tff(c_15391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_106, c_100, c_8525, c_15388])).
% 9.91/3.64  tff(c_15392, plain, (k2_funct_1('#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_15281])).
% 9.91/3.64  tff(c_36, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.91/3.64  tff(c_8515, plain, (![B_18]: (k2_zfmisc_1('#skF_8', B_18)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8510, c_8510, c_36])).
% 9.91/3.64  tff(c_9144, plain, (![A_528, B_529, C_530]: (k2_relset_1(A_528, B_529, C_530)=k2_relat_1(C_530) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_528, B_529))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.91/3.64  tff(c_9167, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_9144])).
% 9.91/3.64  tff(c_9173, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8525, c_9167])).
% 9.91/3.64  tff(c_9176, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_9173, c_334])).
% 9.91/3.64  tff(c_9181, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_8515, c_9176])).
% 9.91/3.64  tff(c_15397, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_15392, c_9181])).
% 9.91/3.64  tff(c_15406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13866, c_15397])).
% 9.91/3.64  tff(c_15407, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_316])).
% 9.91/3.64  tff(c_15408, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_316])).
% 9.91/3.64  tff(c_16459, plain, (![A_895, B_896, C_897]: (k1_relset_1(A_895, B_896, C_897)=k1_relat_1(C_897) | ~m1_subset_1(C_897, k1_zfmisc_1(k2_zfmisc_1(A_895, B_896))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.91/3.64  tff(c_16499, plain, (k1_relset_1('#skF_7', '#skF_6', k2_funct_1('#skF_8'))=k1_relat_1(k2_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_15408, c_16459])).
% 9.91/3.64  tff(c_16860, plain, (![B_923, C_924, A_925]: (k1_xboole_0=B_923 | v1_funct_2(C_924, A_925, B_923) | k1_relset_1(A_925, B_923, C_924)!=A_925 | ~m1_subset_1(C_924, k1_zfmisc_1(k2_zfmisc_1(A_925, B_923))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.91/3.64  tff(c_16884, plain, (k1_xboole_0='#skF_6' | v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | k1_relset_1('#skF_7', '#skF_6', k2_funct_1('#skF_8'))!='#skF_7'), inference(resolution, [status(thm)], [c_15408, c_16860])).
% 9.91/3.64  tff(c_16909, plain, (k1_xboole_0='#skF_6' | v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_16499, c_16884])).
% 9.91/3.64  tff(c_16910, plain, (k1_xboole_0='#skF_6' | k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_15407, c_16909])).
% 9.91/3.64  tff(c_16916, plain, (k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_16910])).
% 9.91/3.64  tff(c_16919, plain, (k2_relat_1('#skF_8')!='#skF_7' | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_58, c_16916])).
% 9.91/3.64  tff(c_16922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15466, c_106, c_100, c_16433, c_16919])).
% 9.91/3.64  tff(c_16923, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_16910])).
% 9.91/3.64  tff(c_16964, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16923, c_12])).
% 9.91/3.64  tff(c_16960, plain, (![B_18]: (k2_zfmisc_1('#skF_6', B_18)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16923, c_16923, c_36])).
% 9.91/3.64  tff(c_15705, plain, (![B_845, A_846]: (v1_xboole_0(B_845) | ~m1_subset_1(B_845, k1_zfmisc_1(A_846)) | ~v1_xboole_0(A_846))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.91/3.64  tff(c_15738, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_102, c_15705])).
% 9.91/3.64  tff(c_15808, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_15738])).
% 9.91/3.64  tff(c_17054, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16960, c_15808])).
% 9.91/3.64  tff(c_17058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16964, c_17054])).
% 9.91/3.64  tff(c_17059, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_15738])).
% 9.91/3.64  tff(c_42, plain, (![A_24]: (v1_xboole_0(k2_relat_1(A_24)) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.91/3.64  tff(c_15528, plain, (![A_821, B_822]: (r2_hidden('#skF_2'(A_821, B_822), A_821) | r1_tarski(A_821, B_822))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.91/3.64  tff(c_15541, plain, (![A_821, B_822]: (~v1_xboole_0(A_821) | r1_tarski(A_821, B_822))), inference(resolution, [status(thm)], [c_15528, c_2])).
% 9.91/3.64  tff(c_15600, plain, (![B_832, A_833]: (B_832=A_833 | ~r1_tarski(B_832, A_833) | ~r1_tarski(A_833, B_832))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.91/3.64  tff(c_15638, plain, (![B_838, A_839]: (B_838=A_839 | ~r1_tarski(B_838, A_839) | ~v1_xboole_0(A_839))), inference(resolution, [status(thm)], [c_15541, c_15600])).
% 9.91/3.64  tff(c_15648, plain, (![B_840, A_841]: (B_840=A_841 | ~v1_xboole_0(B_840) | ~v1_xboole_0(A_841))), inference(resolution, [status(thm)], [c_15541, c_15638])).
% 9.91/3.64  tff(c_15655, plain, (![A_842]: (k1_xboole_0=A_842 | ~v1_xboole_0(A_842))), inference(resolution, [status(thm)], [c_12, c_15648])).
% 9.91/3.64  tff(c_15662, plain, (![A_24]: (k2_relat_1(A_24)=k1_xboole_0 | ~v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_42, c_15655])).
% 9.91/3.64  tff(c_17063, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_17059, c_15662])).
% 9.91/3.64  tff(c_17075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15496, c_17063])).
% 9.91/3.64  tff(c_17076, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_15486])).
% 9.91/3.64  tff(c_17083, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_17076, c_17076, c_46])).
% 9.91/3.64  tff(c_15485, plain, (k1_relat_1('#skF_8')!=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_15466, c_50])).
% 9.91/3.64  tff(c_15495, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_15485])).
% 9.91/3.64  tff(c_17105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17083, c_17076, c_15495])).
% 9.91/3.64  tff(c_17106, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_15485])).
% 9.91/3.64  tff(c_17136, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17106, c_12])).
% 9.91/3.64  tff(c_15467, plain, (![A_817, B_818]: (m1_subset_1('#skF_5'(A_817, B_818), k1_zfmisc_1(k2_zfmisc_1(A_817, B_818))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.91/3.64  tff(c_15473, plain, (![B_18]: (m1_subset_1('#skF_5'(k1_xboole_0, B_18), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_15467])).
% 9.91/3.64  tff(c_17204, plain, (![B_938]: (m1_subset_1('#skF_5'('#skF_8', B_938), k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_17106, c_17106, c_15473])).
% 9.91/3.64  tff(c_38, plain, (![B_21, A_19]: (v1_xboole_0(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_19)) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.91/3.64  tff(c_17207, plain, (![B_938]: (v1_xboole_0('#skF_5'('#skF_8', B_938)) | ~v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_17204, c_38])).
% 9.91/3.64  tff(c_17210, plain, (![B_938]: (v1_xboole_0('#skF_5'('#skF_8', B_938)))), inference(demodulation, [status(thm), theory('equality')], [c_17136, c_17207])).
% 9.91/3.64  tff(c_17668, plain, (![A_981, B_982]: (r2_hidden('#skF_2'(A_981, B_982), A_981) | r1_tarski(A_981, B_982))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.91/3.64  tff(c_17681, plain, (![A_981, B_982]: (~v1_xboole_0(A_981) | r1_tarski(A_981, B_982))), inference(resolution, [status(thm)], [c_17668, c_2])).
% 9.91/3.64  tff(c_17682, plain, (![A_983, B_984]: (~v1_xboole_0(A_983) | r1_tarski(A_983, B_984))), inference(resolution, [status(thm)], [c_17668, c_2])).
% 9.91/3.64  tff(c_17748, plain, (![B_990, A_991]: (B_990=A_991 | ~r1_tarski(B_990, A_991) | ~v1_xboole_0(A_991))), inference(resolution, [status(thm)], [c_17682, c_14])).
% 9.91/3.64  tff(c_17758, plain, (![B_992, A_993]: (B_992=A_993 | ~v1_xboole_0(B_992) | ~v1_xboole_0(A_993))), inference(resolution, [status(thm)], [c_17681, c_17748])).
% 9.91/3.64  tff(c_17771, plain, (![A_994]: (A_994='#skF_8' | ~v1_xboole_0(A_994))), inference(resolution, [status(thm)], [c_17136, c_17758])).
% 9.91/3.64  tff(c_17851, plain, (![B_1002]: ('#skF_5'('#skF_8', B_1002)='#skF_8')), inference(resolution, [status(thm)], [c_17210, c_17771])).
% 9.91/3.64  tff(c_78, plain, (![A_40, B_41]: (v1_funct_2('#skF_5'(A_40, B_41), A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.91/3.64  tff(c_17862, plain, (![B_1002]: (v1_funct_2('#skF_8', '#skF_8', B_1002))), inference(superposition, [status(thm), theory('equality')], [c_17851, c_78])).
% 9.91/3.64  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.91/3.64  tff(c_17134, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_17106, c_17106, c_44])).
% 9.91/3.64  tff(c_18141, plain, (![A_1023, B_1024, C_1025]: (k2_relset_1(A_1023, B_1024, C_1025)=k2_relat_1(C_1025) | ~m1_subset_1(C_1025, k1_zfmisc_1(k2_zfmisc_1(A_1023, B_1024))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.91/3.64  tff(c_18164, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_18141])).
% 9.91/3.64  tff(c_18171, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_17134, c_18164])).
% 9.91/3.64  tff(c_17617, plain, (![A_980]: (k1_relat_1(k2_funct_1(A_980))=k2_relat_1(A_980) | ~v2_funct_1(A_980) | ~v1_funct_1(A_980) | ~v1_relat_1(A_980))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.91/3.64  tff(c_15464, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_15408, c_15444])).
% 9.91/3.64  tff(c_15493, plain, (k1_relat_1(k2_funct_1('#skF_8'))!=k1_xboole_0 | k2_funct_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_15464, c_50])).
% 9.91/3.64  tff(c_17260, plain, (k1_relat_1(k2_funct_1('#skF_8'))!='#skF_8' | k2_funct_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_17106, c_17106, c_15493])).
% 9.91/3.64  tff(c_17261, plain, (k1_relat_1(k2_funct_1('#skF_8'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_17260])).
% 9.91/3.64  tff(c_17626, plain, (k2_relat_1('#skF_8')!='#skF_8' | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_17617, c_17261])).
% 9.91/3.64  tff(c_17633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15466, c_106, c_100, c_17134, c_17626])).
% 9.91/3.64  tff(c_17634, plain, (k2_funct_1('#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_17260])).
% 9.91/3.64  tff(c_17638, plain, (~v1_funct_2('#skF_8', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17634, c_15407])).
% 9.91/3.64  tff(c_18175, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18171, c_17638])).
% 9.91/3.64  tff(c_18183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17862, c_18175])).
% 9.91/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.64  
% 9.91/3.64  Inference rules
% 9.91/3.64  ----------------------
% 9.91/3.64  #Ref     : 0
% 9.91/3.64  #Sup     : 4133
% 9.91/3.64  #Fact    : 0
% 9.91/3.64  #Define  : 0
% 9.91/3.64  #Split   : 45
% 9.91/3.64  #Chain   : 0
% 9.91/3.64  #Close   : 0
% 9.91/3.64  
% 9.91/3.64  Ordering : KBO
% 9.91/3.64  
% 9.91/3.64  Simplification rules
% 9.91/3.64  ----------------------
% 9.91/3.64  #Subsume      : 1334
% 9.91/3.64  #Demod        : 2501
% 9.91/3.64  #Tautology    : 1447
% 9.91/3.64  #SimpNegUnit  : 325
% 9.91/3.64  #BackRed      : 240
% 9.91/3.64  
% 9.91/3.64  #Partial instantiations: 0
% 9.91/3.64  #Strategies tried      : 1
% 9.91/3.64  
% 9.91/3.64  Timing (in seconds)
% 9.91/3.64  ----------------------
% 9.91/3.64  Preprocessing        : 0.46
% 9.91/3.64  Parsing              : 0.25
% 9.91/3.64  CNF conversion       : 0.03
% 9.91/3.64  Main loop            : 2.33
% 9.91/3.65  Inferencing          : 0.71
% 9.91/3.65  Reduction            : 0.74
% 9.91/3.65  Demodulation         : 0.51
% 9.91/3.65  BG Simplification    : 0.08
% 9.91/3.65  Subsumption          : 0.59
% 9.91/3.65  Abstraction          : 0.10
% 9.91/3.65  MUC search           : 0.00
% 9.91/3.65  Cooper               : 0.00
% 9.91/3.65  Total                : 2.85
% 9.91/3.65  Index Insertion      : 0.00
% 9.91/3.65  Index Deletion       : 0.00
% 9.91/3.65  Index Matching       : 0.00
% 9.91/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
