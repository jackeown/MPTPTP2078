%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:40 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 485 expanded)
%              Number of leaves         :   45 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  264 (1149 expanded)
%              Number of equality atoms :   23 ( 128 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_151,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(c_102,plain,(
    r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_821,plain,(
    ! [A_251,B_252,D_253] :
      ( '#skF_6'(A_251,B_252,k1_funct_2(A_251,B_252),D_253) = D_253
      | ~ r2_hidden(D_253,k1_funct_2(A_251,B_252)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_836,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_102,c_821])).

tff(c_965,plain,(
    ! [A_274,B_275,D_276] :
      ( v1_relat_1('#skF_6'(A_274,B_275,k1_funct_2(A_274,B_275),D_276))
      | ~ r2_hidden(D_276,k1_funct_2(A_274,B_275)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_968,plain,
    ( v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_965])).

tff(c_970,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_968])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1071,plain,(
    ! [A_293,B_294,D_295] :
      ( k1_relat_1('#skF_6'(A_293,B_294,k1_funct_2(A_293,B_294),D_295)) = A_293
      | ~ r2_hidden(D_295,k1_funct_2(A_293,B_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1109,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_1071])).

tff(c_1113,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1109])).

tff(c_1485,plain,(
    ! [A_316,B_317,D_318] :
      ( r1_tarski(k2_relat_1('#skF_6'(A_316,B_317,k1_funct_2(A_316,B_317),D_318)),B_317)
      | ~ r2_hidden(D_318,k1_funct_2(A_316,B_317)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1521,plain,
    ( r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_1485])).

tff(c_1533,plain,(
    r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1521])).

tff(c_2139,plain,(
    ! [C_384,A_385,B_386] :
      ( m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386)))
      | ~ r1_tarski(k2_relat_1(C_384),B_386)
      | ~ r1_tarski(k1_relat_1(C_384),A_385)
      | ~ v1_relat_1(C_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_100,plain,
    ( ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_126,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_420,plain,(
    ! [A_150,B_151,D_152] :
      ( '#skF_6'(A_150,B_151,k1_funct_2(A_150,B_151),D_152) = D_152
      | ~ r2_hidden(D_152,k1_funct_2(A_150,B_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_435,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_102,c_420])).

tff(c_494,plain,(
    ! [A_168,B_169,D_170] :
      ( v1_funct_1('#skF_6'(A_168,B_169,k1_funct_2(A_168,B_169),D_170))
      | ~ r2_hidden(D_170,k1_funct_2(A_168,B_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_497,plain,
    ( v1_funct_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_494])).

tff(c_499,plain,(
    v1_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_497])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_499])).

tff(c_502,plain,
    ( ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_557,plain,(
    ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_2151,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_8')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2139,c_557])).

tff(c_2164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_16,c_1113,c_1533,c_2151])).

tff(c_2166,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_28,plain,(
    ! [C_20,A_18,B_19] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2173,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2166,c_28])).

tff(c_2235,plain,(
    ! [C_397,A_398,B_399] :
      ( v4_relat_1(C_397,A_398)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2243,plain,(
    v4_relat_1('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_2166,c_2235])).

tff(c_2212,plain,(
    ! [B_395,A_396] :
      ( r1_tarski(k1_relat_1(B_395),A_396)
      | ~ v4_relat_1(B_395,A_396)
      | ~ v1_relat_1(B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_522,plain,(
    ! [A_181,B_182] :
      ( r2_hidden('#skF_2'(A_181,B_182),A_181)
      | r1_tarski(A_181,B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_530,plain,(
    ! [A_181,B_182] :
      ( ~ v1_xboole_0(A_181)
      | r1_tarski(A_181,B_182) ) ),
    inference(resolution,[status(thm)],[c_522,c_2])).

tff(c_547,plain,(
    ! [B_186,A_187] :
      ( B_186 = A_187
      | ~ r1_tarski(B_186,A_187)
      | ~ r1_tarski(A_187,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_552,plain,(
    ! [B_182,A_181] :
      ( B_182 = A_181
      | ~ r1_tarski(B_182,A_181)
      | ~ v1_xboole_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_530,c_547])).

tff(c_2505,plain,(
    ! [B_461,A_462] :
      ( k1_relat_1(B_461) = A_462
      | ~ v1_xboole_0(A_462)
      | ~ v4_relat_1(B_461,A_462)
      | ~ v1_relat_1(B_461) ) ),
    inference(resolution,[status(thm)],[c_2212,c_552])).

tff(c_2517,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2243,c_2505])).

tff(c_2526,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_2517])).

tff(c_2543,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2526])).

tff(c_2527,plain,(
    ! [A_463,B_464,D_465] :
      ( '#skF_6'(A_463,B_464,k1_funct_2(A_463,B_464),D_465) = D_465
      | ~ r2_hidden(D_465,k1_funct_2(A_463,B_464)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2542,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_102,c_2527])).

tff(c_2821,plain,(
    ! [A_499,B_500,D_501] :
      ( k1_relat_1('#skF_6'(A_499,B_500,k1_funct_2(A_499,B_500),D_501)) = A_499
      | ~ r2_hidden(D_501,k1_funct_2(A_499,B_500)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2862,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2542,c_2821])).

tff(c_2866,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2862])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2250,plain,(
    ! [A_400,A_401,B_402] :
      ( v4_relat_1(A_400,A_401)
      | ~ r1_tarski(A_400,k2_zfmisc_1(A_401,B_402)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2235])).

tff(c_2269,plain,(
    ! [A_181,A_401] :
      ( v4_relat_1(A_181,A_401)
      | ~ v1_xboole_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_530,c_2250])).

tff(c_115,plain,(
    ! [A_68] :
      ( v1_xboole_0(A_68)
      | r2_hidden('#skF_1'(A_68),A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_122,plain,(
    ! [A_68] :
      ( ~ r1_tarski(A_68,'#skF_1'(A_68))
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_115,c_26])).

tff(c_2478,plain,(
    ! [B_457] :
      ( v1_xboole_0(k1_relat_1(B_457))
      | ~ v4_relat_1(B_457,'#skF_1'(k1_relat_1(B_457)))
      | ~ v1_relat_1(B_457) ) ),
    inference(resolution,[status(thm)],[c_2212,c_122])).

tff(c_2483,plain,(
    ! [A_181] :
      ( v1_xboole_0(k1_relat_1(A_181))
      | ~ v1_relat_1(A_181)
      | ~ v1_xboole_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_2269,c_2478])).

tff(c_2876,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_xboole_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_2483])).

tff(c_2907,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_2876])).

tff(c_2908,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_2543,c_2907])).

tff(c_503,plain,(
    v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_2452,plain,(
    ! [A_447] :
      ( m1_subset_1(A_447,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_447),k2_relat_1(A_447))))
      | ~ v1_funct_1(A_447)
      | ~ v1_relat_1(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2472,plain,(
    ! [A_447] :
      ( r1_tarski(A_447,k2_zfmisc_1(k1_relat_1(A_447),k2_relat_1(A_447)))
      | ~ v1_funct_1(A_447)
      | ~ v1_relat_1(A_447) ) ),
    inference(resolution,[status(thm)],[c_2452,c_18])).

tff(c_2870,plain,
    ( r1_tarski('#skF_10',k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_2472])).

tff(c_2903,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_503,c_2870])).

tff(c_2357,plain,(
    ! [C_428,B_429,A_430] :
      ( v1_xboole_0(C_428)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(B_429,A_430)))
      | ~ v1_xboole_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2366,plain,(
    ! [A_12,A_430,B_429] :
      ( v1_xboole_0(A_12)
      | ~ v1_xboole_0(A_430)
      | ~ r1_tarski(A_12,k2_zfmisc_1(B_429,A_430)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2357])).

tff(c_3080,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2903,c_2366])).

tff(c_3101,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_2908,c_3080])).

tff(c_2165,plain,(
    ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_3216,plain,(
    ! [C_521,A_522,B_523] :
      ( v1_funct_2(C_521,A_522,B_523)
      | ~ v1_partfun1(C_521,A_522)
      | ~ v1_funct_1(C_521)
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_zfmisc_1(A_522,B_523))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3225,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2166,c_3216])).

tff(c_3236,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_3225])).

tff(c_3237,plain,(
    ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2165,c_3236])).

tff(c_84,plain,(
    ! [A_58] :
      ( v1_funct_2(A_58,k1_relat_1(A_58),k2_relat_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2888,plain,
    ( v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_84])).

tff(c_2917,plain,(
    v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_503,c_2888])).

tff(c_82,plain,(
    ! [A_58] :
      ( m1_subset_1(A_58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_58),k2_relat_1(A_58))))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2885,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_82])).

tff(c_2915,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_503,c_2885])).

tff(c_5442,plain,(
    ! [C_736,A_737,B_738] :
      ( v1_partfun1(C_736,A_737)
      | ~ v1_funct_2(C_736,A_737,B_738)
      | ~ v1_funct_1(C_736)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(A_737,B_738)))
      | v1_xboole_0(B_738) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5448,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_2915,c_5442])).

tff(c_5462,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_2917,c_5448])).

tff(c_5464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3101,c_3237,c_5462])).

tff(c_5466,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2526])).

tff(c_5465,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2526])).

tff(c_2283,plain,(
    ! [B_410,A_411] :
      ( v4_relat_1(B_410,A_411)
      | ~ r1_tarski(k1_relat_1(B_410),A_411)
      | ~ v1_relat_1(B_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2296,plain,(
    ! [B_410,B_182] :
      ( v4_relat_1(B_410,B_182)
      | ~ v1_relat_1(B_410)
      | ~ v1_xboole_0(k1_relat_1(B_410)) ) ),
    inference(resolution,[status(thm)],[c_530,c_2283])).

tff(c_5497,plain,(
    ! [B_182] :
      ( v4_relat_1('#skF_10',B_182)
      | ~ v1_relat_1('#skF_10')
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5465,c_2296])).

tff(c_5520,plain,(
    ! [B_182] : v4_relat_1('#skF_10',B_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5466,c_2173,c_5497])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5506,plain,(
    ! [A_14] :
      ( r1_tarski('#skF_8',A_14)
      | ~ v4_relat_1('#skF_10',A_14)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5465,c_24])).

tff(c_5526,plain,(
    ! [A_14] :
      ( r1_tarski('#skF_8',A_14)
      | ~ v4_relat_1('#skF_10',A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_5506])).

tff(c_5574,plain,(
    ! [A_14] : r1_tarski('#skF_8',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5520,c_5526])).

tff(c_8328,plain,(
    ! [C_863,B_864] :
      ( r2_hidden('#skF_7'(k1_relat_1(C_863),B_864,C_863),k1_relat_1(C_863))
      | v1_funct_2(C_863,k1_relat_1(C_863),B_864)
      | ~ v1_funct_1(C_863)
      | ~ v1_relat_1(C_863) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_8375,plain,(
    ! [B_864] :
      ( r2_hidden('#skF_7'('#skF_8',B_864,'#skF_10'),k1_relat_1('#skF_10'))
      | v1_funct_2('#skF_10',k1_relat_1('#skF_10'),B_864)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5465,c_8328])).

tff(c_8432,plain,(
    ! [B_868] :
      ( r2_hidden('#skF_7'('#skF_8',B_868,'#skF_10'),'#skF_8')
      | v1_funct_2('#skF_10','#skF_8',B_868) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_503,c_5465,c_5465,c_8375])).

tff(c_8437,plain,(
    ! [B_868] :
      ( ~ r1_tarski('#skF_8','#skF_7'('#skF_8',B_868,'#skF_10'))
      | v1_funct_2('#skF_10','#skF_8',B_868) ) ),
    inference(resolution,[status(thm)],[c_8432,c_26])).

tff(c_8446,plain,(
    ! [B_868] : v1_funct_2('#skF_10','#skF_8',B_868) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5574,c_8437])).

tff(c_8454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8446,c_2165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.52  
% 7.58/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2
% 7.58/2.52  
% 7.58/2.52  %Foreground sorts:
% 7.58/2.52  
% 7.58/2.52  
% 7.58/2.52  %Background operators:
% 7.58/2.52  
% 7.58/2.52  
% 7.58/2.52  %Foreground operators:
% 7.58/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.58/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.58/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.58/2.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.58/2.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.58/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.58/2.52  tff('#skF_10', type, '#skF_10': $i).
% 7.58/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.58/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.58/2.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.58/2.52  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.58/2.52  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.58/2.52  tff('#skF_9', type, '#skF_9': $i).
% 7.58/2.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.58/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.58/2.52  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.58/2.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.58/2.52  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 7.58/2.52  tff('#skF_8', type, '#skF_8': $i).
% 7.58/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.58/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.58/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.58/2.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.58/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.58/2.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.58/2.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.58/2.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.58/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.58/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.58/2.52  
% 7.58/2.54  tff(f_160, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 7.58/2.54  tff(f_124, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 7.58/2.54  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.58/2.54  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.58/2.54  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.58/2.54  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.58/2.54  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.58/2.54  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.58/2.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.58/2.54  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.58/2.54  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.58/2.54  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.58/2.54  tff(f_76, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.58/2.54  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.58/2.54  tff(f_108, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.58/2.54  tff(f_151, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 7.58/2.54  tff(c_102, plain, (r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.58/2.54  tff(c_821, plain, (![A_251, B_252, D_253]: ('#skF_6'(A_251, B_252, k1_funct_2(A_251, B_252), D_253)=D_253 | ~r2_hidden(D_253, k1_funct_2(A_251, B_252)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.54  tff(c_836, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_102, c_821])).
% 7.58/2.54  tff(c_965, plain, (![A_274, B_275, D_276]: (v1_relat_1('#skF_6'(A_274, B_275, k1_funct_2(A_274, B_275), D_276)) | ~r2_hidden(D_276, k1_funct_2(A_274, B_275)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.54  tff(c_968, plain, (v1_relat_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_836, c_965])).
% 7.58/2.54  tff(c_970, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_968])).
% 7.58/2.54  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.58/2.54  tff(c_1071, plain, (![A_293, B_294, D_295]: (k1_relat_1('#skF_6'(A_293, B_294, k1_funct_2(A_293, B_294), D_295))=A_293 | ~r2_hidden(D_295, k1_funct_2(A_293, B_294)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.54  tff(c_1109, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_836, c_1071])).
% 7.58/2.54  tff(c_1113, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1109])).
% 7.58/2.54  tff(c_1485, plain, (![A_316, B_317, D_318]: (r1_tarski(k2_relat_1('#skF_6'(A_316, B_317, k1_funct_2(A_316, B_317), D_318)), B_317) | ~r2_hidden(D_318, k1_funct_2(A_316, B_317)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.54  tff(c_1521, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_836, c_1485])).
% 7.58/2.54  tff(c_1533, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1521])).
% 7.58/2.54  tff(c_2139, plain, (![C_384, A_385, B_386]: (m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))) | ~r1_tarski(k2_relat_1(C_384), B_386) | ~r1_tarski(k1_relat_1(C_384), A_385) | ~v1_relat_1(C_384))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.58/2.54  tff(c_100, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.58/2.54  tff(c_126, plain, (~v1_funct_1('#skF_10')), inference(splitLeft, [status(thm)], [c_100])).
% 7.58/2.54  tff(c_420, plain, (![A_150, B_151, D_152]: ('#skF_6'(A_150, B_151, k1_funct_2(A_150, B_151), D_152)=D_152 | ~r2_hidden(D_152, k1_funct_2(A_150, B_151)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.54  tff(c_435, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_102, c_420])).
% 7.58/2.54  tff(c_494, plain, (![A_168, B_169, D_170]: (v1_funct_1('#skF_6'(A_168, B_169, k1_funct_2(A_168, B_169), D_170)) | ~r2_hidden(D_170, k1_funct_2(A_168, B_169)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.54  tff(c_497, plain, (v1_funct_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_435, c_494])).
% 7.58/2.54  tff(c_499, plain, (v1_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_497])).
% 7.58/2.54  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_499])).
% 7.58/2.54  tff(c_502, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_100])).
% 7.58/2.54  tff(c_557, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitLeft, [status(thm)], [c_502])).
% 7.58/2.54  tff(c_2151, plain, (~r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_8') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2139, c_557])).
% 7.58/2.54  tff(c_2164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_970, c_16, c_1113, c_1533, c_2151])).
% 7.58/2.54  tff(c_2166, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_502])).
% 7.58/2.54  tff(c_28, plain, (![C_20, A_18, B_19]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.58/2.54  tff(c_2173, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2166, c_28])).
% 7.58/2.54  tff(c_2235, plain, (![C_397, A_398, B_399]: (v4_relat_1(C_397, A_398) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.58/2.54  tff(c_2243, plain, (v4_relat_1('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_2166, c_2235])).
% 7.58/2.54  tff(c_2212, plain, (![B_395, A_396]: (r1_tarski(k1_relat_1(B_395), A_396) | ~v4_relat_1(B_395, A_396) | ~v1_relat_1(B_395))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.58/2.54  tff(c_522, plain, (![A_181, B_182]: (r2_hidden('#skF_2'(A_181, B_182), A_181) | r1_tarski(A_181, B_182))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.58/2.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.58/2.54  tff(c_530, plain, (![A_181, B_182]: (~v1_xboole_0(A_181) | r1_tarski(A_181, B_182))), inference(resolution, [status(thm)], [c_522, c_2])).
% 7.58/2.54  tff(c_547, plain, (![B_186, A_187]: (B_186=A_187 | ~r1_tarski(B_186, A_187) | ~r1_tarski(A_187, B_186))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.58/2.54  tff(c_552, plain, (![B_182, A_181]: (B_182=A_181 | ~r1_tarski(B_182, A_181) | ~v1_xboole_0(A_181))), inference(resolution, [status(thm)], [c_530, c_547])).
% 7.58/2.54  tff(c_2505, plain, (![B_461, A_462]: (k1_relat_1(B_461)=A_462 | ~v1_xboole_0(A_462) | ~v4_relat_1(B_461, A_462) | ~v1_relat_1(B_461))), inference(resolution, [status(thm)], [c_2212, c_552])).
% 7.58/2.54  tff(c_2517, plain, (k1_relat_1('#skF_10')='#skF_8' | ~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2243, c_2505])).
% 7.58/2.54  tff(c_2526, plain, (k1_relat_1('#skF_10')='#skF_8' | ~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_2517])).
% 7.58/2.54  tff(c_2543, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_2526])).
% 7.58/2.54  tff(c_2527, plain, (![A_463, B_464, D_465]: ('#skF_6'(A_463, B_464, k1_funct_2(A_463, B_464), D_465)=D_465 | ~r2_hidden(D_465, k1_funct_2(A_463, B_464)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.54  tff(c_2542, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_102, c_2527])).
% 7.58/2.54  tff(c_2821, plain, (![A_499, B_500, D_501]: (k1_relat_1('#skF_6'(A_499, B_500, k1_funct_2(A_499, B_500), D_501))=A_499 | ~r2_hidden(D_501, k1_funct_2(A_499, B_500)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.58/2.54  tff(c_2862, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2542, c_2821])).
% 7.58/2.54  tff(c_2866, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2862])).
% 7.58/2.54  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.58/2.54  tff(c_2250, plain, (![A_400, A_401, B_402]: (v4_relat_1(A_400, A_401) | ~r1_tarski(A_400, k2_zfmisc_1(A_401, B_402)))), inference(resolution, [status(thm)], [c_20, c_2235])).
% 7.58/2.54  tff(c_2269, plain, (![A_181, A_401]: (v4_relat_1(A_181, A_401) | ~v1_xboole_0(A_181))), inference(resolution, [status(thm)], [c_530, c_2250])).
% 7.58/2.54  tff(c_115, plain, (![A_68]: (v1_xboole_0(A_68) | r2_hidden('#skF_1'(A_68), A_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.58/2.54  tff(c_26, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.58/2.54  tff(c_122, plain, (![A_68]: (~r1_tarski(A_68, '#skF_1'(A_68)) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_115, c_26])).
% 7.58/2.54  tff(c_2478, plain, (![B_457]: (v1_xboole_0(k1_relat_1(B_457)) | ~v4_relat_1(B_457, '#skF_1'(k1_relat_1(B_457))) | ~v1_relat_1(B_457))), inference(resolution, [status(thm)], [c_2212, c_122])).
% 7.58/2.54  tff(c_2483, plain, (![A_181]: (v1_xboole_0(k1_relat_1(A_181)) | ~v1_relat_1(A_181) | ~v1_xboole_0(A_181))), inference(resolution, [status(thm)], [c_2269, c_2478])).
% 7.58/2.54  tff(c_2876, plain, (v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_10') | ~v1_xboole_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2866, c_2483])).
% 7.58/2.54  tff(c_2907, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_2876])).
% 7.58/2.54  tff(c_2908, plain, (~v1_xboole_0('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_2543, c_2907])).
% 7.58/2.54  tff(c_503, plain, (v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_100])).
% 7.58/2.54  tff(c_2452, plain, (![A_447]: (m1_subset_1(A_447, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_447), k2_relat_1(A_447)))) | ~v1_funct_1(A_447) | ~v1_relat_1(A_447))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.58/2.54  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.58/2.54  tff(c_2472, plain, (![A_447]: (r1_tarski(A_447, k2_zfmisc_1(k1_relat_1(A_447), k2_relat_1(A_447))) | ~v1_funct_1(A_447) | ~v1_relat_1(A_447))), inference(resolution, [status(thm)], [c_2452, c_18])).
% 7.58/2.54  tff(c_2870, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2866, c_2472])).
% 7.58/2.54  tff(c_2903, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_503, c_2870])).
% 7.58/2.54  tff(c_2357, plain, (![C_428, B_429, A_430]: (v1_xboole_0(C_428) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(B_429, A_430))) | ~v1_xboole_0(A_430))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.58/2.54  tff(c_2366, plain, (![A_12, A_430, B_429]: (v1_xboole_0(A_12) | ~v1_xboole_0(A_430) | ~r1_tarski(A_12, k2_zfmisc_1(B_429, A_430)))), inference(resolution, [status(thm)], [c_20, c_2357])).
% 7.58/2.54  tff(c_3080, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_2903, c_2366])).
% 7.58/2.54  tff(c_3101, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_2908, c_3080])).
% 7.58/2.54  tff(c_2165, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_502])).
% 7.58/2.54  tff(c_3216, plain, (![C_521, A_522, B_523]: (v1_funct_2(C_521, A_522, B_523) | ~v1_partfun1(C_521, A_522) | ~v1_funct_1(C_521) | ~m1_subset_1(C_521, k1_zfmisc_1(k2_zfmisc_1(A_522, B_523))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.58/2.54  tff(c_3225, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_2166, c_3216])).
% 7.58/2.54  tff(c_3236, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_3225])).
% 7.58/2.54  tff(c_3237, plain, (~v1_partfun1('#skF_10', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2165, c_3236])).
% 7.58/2.54  tff(c_84, plain, (![A_58]: (v1_funct_2(A_58, k1_relat_1(A_58), k2_relat_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.58/2.54  tff(c_2888, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2866, c_84])).
% 7.58/2.54  tff(c_2917, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_503, c_2888])).
% 7.58/2.54  tff(c_82, plain, (![A_58]: (m1_subset_1(A_58, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_58), k2_relat_1(A_58)))) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.58/2.54  tff(c_2885, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2866, c_82])).
% 7.58/2.54  tff(c_2915, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_503, c_2885])).
% 7.58/2.54  tff(c_5442, plain, (![C_736, A_737, B_738]: (v1_partfun1(C_736, A_737) | ~v1_funct_2(C_736, A_737, B_738) | ~v1_funct_1(C_736) | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(A_737, B_738))) | v1_xboole_0(B_738))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.58/2.54  tff(c_5448, plain, (v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_2915, c_5442])).
% 7.58/2.54  tff(c_5462, plain, (v1_partfun1('#skF_10', '#skF_8') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_2917, c_5448])).
% 7.58/2.54  tff(c_5464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3101, c_3237, c_5462])).
% 7.58/2.54  tff(c_5466, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_2526])).
% 7.58/2.54  tff(c_5465, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitRight, [status(thm)], [c_2526])).
% 7.58/2.54  tff(c_2283, plain, (![B_410, A_411]: (v4_relat_1(B_410, A_411) | ~r1_tarski(k1_relat_1(B_410), A_411) | ~v1_relat_1(B_410))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.58/2.54  tff(c_2296, plain, (![B_410, B_182]: (v4_relat_1(B_410, B_182) | ~v1_relat_1(B_410) | ~v1_xboole_0(k1_relat_1(B_410)))), inference(resolution, [status(thm)], [c_530, c_2283])).
% 7.58/2.54  tff(c_5497, plain, (![B_182]: (v4_relat_1('#skF_10', B_182) | ~v1_relat_1('#skF_10') | ~v1_xboole_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5465, c_2296])).
% 7.58/2.54  tff(c_5520, plain, (![B_182]: (v4_relat_1('#skF_10', B_182))), inference(demodulation, [status(thm), theory('equality')], [c_5466, c_2173, c_5497])).
% 7.58/2.54  tff(c_24, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.58/2.54  tff(c_5506, plain, (![A_14]: (r1_tarski('#skF_8', A_14) | ~v4_relat_1('#skF_10', A_14) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5465, c_24])).
% 7.58/2.54  tff(c_5526, plain, (![A_14]: (r1_tarski('#skF_8', A_14) | ~v4_relat_1('#skF_10', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_5506])).
% 7.58/2.54  tff(c_5574, plain, (![A_14]: (r1_tarski('#skF_8', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_5520, c_5526])).
% 7.58/2.54  tff(c_8328, plain, (![C_863, B_864]: (r2_hidden('#skF_7'(k1_relat_1(C_863), B_864, C_863), k1_relat_1(C_863)) | v1_funct_2(C_863, k1_relat_1(C_863), B_864) | ~v1_funct_1(C_863) | ~v1_relat_1(C_863))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.58/2.54  tff(c_8375, plain, (![B_864]: (r2_hidden('#skF_7'('#skF_8', B_864, '#skF_10'), k1_relat_1('#skF_10')) | v1_funct_2('#skF_10', k1_relat_1('#skF_10'), B_864) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5465, c_8328])).
% 7.58/2.54  tff(c_8432, plain, (![B_868]: (r2_hidden('#skF_7'('#skF_8', B_868, '#skF_10'), '#skF_8') | v1_funct_2('#skF_10', '#skF_8', B_868))), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_503, c_5465, c_5465, c_8375])).
% 7.58/2.54  tff(c_8437, plain, (![B_868]: (~r1_tarski('#skF_8', '#skF_7'('#skF_8', B_868, '#skF_10')) | v1_funct_2('#skF_10', '#skF_8', B_868))), inference(resolution, [status(thm)], [c_8432, c_26])).
% 7.58/2.54  tff(c_8446, plain, (![B_868]: (v1_funct_2('#skF_10', '#skF_8', B_868))), inference(demodulation, [status(thm), theory('equality')], [c_5574, c_8437])).
% 7.58/2.54  tff(c_8454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8446, c_2165])).
% 7.58/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.54  
% 7.58/2.54  Inference rules
% 7.58/2.54  ----------------------
% 7.58/2.54  #Ref     : 0
% 7.58/2.54  #Sup     : 1870
% 7.58/2.54  #Fact    : 0
% 7.58/2.54  #Define  : 0
% 7.58/2.54  #Split   : 23
% 7.58/2.54  #Chain   : 0
% 7.58/2.54  #Close   : 0
% 7.58/2.54  
% 7.58/2.54  Ordering : KBO
% 7.58/2.54  
% 7.58/2.54  Simplification rules
% 7.58/2.54  ----------------------
% 7.58/2.54  #Subsume      : 559
% 7.58/2.54  #Demod        : 975
% 7.58/2.54  #Tautology    : 480
% 7.58/2.54  #SimpNegUnit  : 52
% 7.58/2.54  #BackRed      : 14
% 7.58/2.54  
% 7.58/2.54  #Partial instantiations: 0
% 7.58/2.54  #Strategies tried      : 1
% 7.58/2.54  
% 7.58/2.54  Timing (in seconds)
% 7.58/2.54  ----------------------
% 7.58/2.55  Preprocessing        : 0.36
% 7.58/2.55  Parsing              : 0.18
% 7.58/2.55  CNF conversion       : 0.03
% 7.58/2.55  Main loop            : 1.40
% 7.58/2.55  Inferencing          : 0.48
% 7.58/2.55  Reduction            : 0.43
% 7.58/2.55  Demodulation         : 0.29
% 7.58/2.55  BG Simplification    : 0.05
% 7.58/2.55  Subsumption          : 0.32
% 7.58/2.55  Abstraction          : 0.06
% 7.58/2.55  MUC search           : 0.00
% 7.58/2.55  Cooper               : 0.00
% 7.58/2.55  Total                : 1.81
% 7.58/2.55  Index Insertion      : 0.00
% 7.58/2.55  Index Deletion       : 0.00
% 7.58/2.55  Index Matching       : 0.00
% 7.58/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
