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
% DateTime   : Thu Dec  3 10:12:45 EST 2020

% Result     : Theorem 5.79s
% Output     : CNFRefutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :  176 (2135 expanded)
%              Number of leaves         :   32 ( 748 expanded)
%              Depth                    :   22
%              Number of atoms          :  357 (7335 expanded)
%              Number of equality atoms :   72 (2274 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
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

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4294,plain,(
    ! [A_402,B_403,C_404] :
      ( k1_relset_1(A_402,B_403,C_404) = k1_relat_1(C_404)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4307,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4294])).

tff(c_4440,plain,(
    ! [A_412,B_413,C_414] :
      ( m1_subset_1(k1_relset_1(A_412,B_413,C_414),k1_zfmisc_1(A_412))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4467,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4307,c_4440])).

tff(c_4477,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4467])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4481,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4477,c_8])).

tff(c_4161,plain,(
    ! [C_376,A_377,B_378] :
      ( v1_relat_1(C_376)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4174,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4161])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_18,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_92])).

tff(c_115,plain,(
    ! [A_41] :
      ( v1_funct_1(k2_funct_1(A_41))
      | ~ v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_81,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_118,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_81])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_64,c_58,c_118])).

tff(c_123,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_125,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_140,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_149,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_140])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_225,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_232,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_225])).

tff(c_235,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_232])).

tff(c_20,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_191,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_200,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_191])).

tff(c_371,plain,(
    ! [A_78,B_79,C_80] :
      ( m1_subset_1(k1_relset_1(A_78,B_79,C_80),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_395,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_371])).

tff(c_403,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_395])).

tff(c_407,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_403,c_8])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_741,plain,(
    ! [B_126,A_127,C_128] :
      ( k1_xboole_0 = B_126
      | k1_relset_1(A_127,B_126,C_128) = A_127
      | ~ v1_funct_2(C_128,A_127,B_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_761,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_741])).

tff(c_771,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_200,c_761])).

tff(c_772,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_410,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_407,c_2])).

tff(c_416,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_773,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_416])).

tff(c_786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_773])).

tff(c_788,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_71,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_71])).

tff(c_787,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_543,plain,(
    ! [C_98,A_99] :
      ( k1_xboole_0 = C_98
      | ~ v1_funct_2(C_98,A_99,k1_xboole_0)
      | k1_xboole_0 = A_99
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_553,plain,(
    ! [A_3,A_99] :
      ( k1_xboole_0 = A_3
      | ~ v1_funct_2(A_3,A_99,k1_xboole_0)
      | k1_xboole_0 = A_99
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_99,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_10,c_543])).

tff(c_866,plain,(
    ! [A_137,A_138] :
      ( A_137 = '#skF_2'
      | ~ v1_funct_2(A_137,A_138,'#skF_2')
      | A_138 = '#skF_2'
      | ~ r1_tarski(A_137,k2_zfmisc_1(A_138,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_787,c_787,c_787,c_553])).

tff(c_884,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_75,c_866])).

tff(c_897,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_884])).

tff(c_899,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_922,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_62])).

tff(c_919,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_75])).

tff(c_645,plain,(
    ! [B_113,C_114] :
      ( k1_relset_1(k1_xboole_0,B_113,C_114) = k1_xboole_0
      | ~ v1_funct_2(C_114,k1_xboole_0,B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_655,plain,(
    ! [B_113,A_3] :
      ( k1_relset_1(k1_xboole_0,B_113,A_3) = k1_xboole_0
      | ~ v1_funct_2(A_3,k1_xboole_0,B_113)
      | ~ r1_tarski(A_3,k2_zfmisc_1(k1_xboole_0,B_113)) ) ),
    inference(resolution,[status(thm)],[c_10,c_645])).

tff(c_791,plain,(
    ! [B_113,A_3] :
      ( k1_relset_1('#skF_2',B_113,A_3) = '#skF_2'
      | ~ v1_funct_2(A_3,'#skF_2',B_113)
      | ~ r1_tarski(A_3,k2_zfmisc_1('#skF_2',B_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_787,c_787,c_787,c_655])).

tff(c_987,plain,(
    ! [B_139,A_140] :
      ( k1_relset_1('#skF_1',B_139,A_140) = '#skF_1'
      | ~ v1_funct_2(A_140,'#skF_1',B_139)
      | ~ r1_tarski(A_140,k2_zfmisc_1('#skF_1',B_139)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_899,c_899,c_899,c_791])).

tff(c_990,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_919,c_987])).

tff(c_1005,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_990])).

tff(c_920,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_60])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1030,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_920,c_26])).

tff(c_1042,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_1030])).

tff(c_1044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_1042])).

tff(c_1045,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_1061,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_235])).

tff(c_179,plain,(
    ! [A_57] :
      ( k1_relat_1(k2_funct_1(A_57)) = k2_relat_1(A_57)
      | ~ v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [A_22] :
      ( v1_funct_2(A_22,k1_relat_1(A_22),k2_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2164,plain,(
    ! [A_229] :
      ( v1_funct_2(k2_funct_1(A_229),k2_relat_1(A_229),k2_relat_1(k2_funct_1(A_229)))
      | ~ v1_funct_1(k2_funct_1(A_229))
      | ~ v1_relat_1(k2_funct_1(A_229))
      | ~ v2_funct_1(A_229)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_44])).

tff(c_2167,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_2164])).

tff(c_2175,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_64,c_58,c_124,c_2167])).

tff(c_2176,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2175])).

tff(c_2179,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_2176])).

tff(c_2183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_64,c_58,c_2179])).

tff(c_2185,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2175])).

tff(c_2184,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2175])).

tff(c_270,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_75),k2_relat_1(A_75))))
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2283,plain,(
    ! [A_240] :
      ( m1_subset_1(k2_funct_1(A_240),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_240),k2_relat_1(k2_funct_1(A_240)))))
      | ~ v1_funct_1(k2_funct_1(A_240))
      | ~ v1_relat_1(k2_funct_1(A_240))
      | ~ v2_funct_1(A_240)
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_270])).

tff(c_2306,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_2283])).

tff(c_2321,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_64,c_58,c_2185,c_124,c_2306])).

tff(c_38,plain,(
    ! [B_20,C_21] :
      ( k1_relset_1(k1_xboole_0,B_20,C_21) = k1_xboole_0
      | ~ v1_funct_2(C_21,k1_xboole_0,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_792,plain,(
    ! [B_20,C_21] :
      ( k1_relset_1('#skF_2',B_20,C_21) = '#skF_2'
      | ~ v1_funct_2(C_21,'#skF_2',B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_20))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_787,c_787,c_787,c_38])).

tff(c_1534,plain,(
    ! [B_20,C_21] :
      ( k1_relset_1('#skF_3',B_20,C_21) = '#skF_3'
      | ~ v1_funct_2(C_21,'#skF_3',B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_20))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_1045,c_1045,c_1045,c_792])).

tff(c_2355,plain,
    ( k1_relset_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2321,c_1534])).

tff(c_2382,plain,(
    k1_relset_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2184,c_2355])).

tff(c_2388,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_2321,c_8])).

tff(c_199,plain,(
    ! [A_58,B_59,A_3] :
      ( k1_relset_1(A_58,B_59,A_3) = k1_relat_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_10,c_191])).

tff(c_2446,plain,(
    k1_relset_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2388,c_199])).

tff(c_2469,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2382,c_2446])).

tff(c_679,plain,(
    ! [B_122,A_123] :
      ( m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_122),A_123)))
      | ~ r1_tarski(k2_relat_1(B_122),A_123)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_711,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(B_122,k2_zfmisc_1(k1_relat_1(B_122),A_123))
      | ~ r1_tarski(k2_relat_1(B_122),A_123)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_679,c_8])).

tff(c_2509,plain,(
    ! [A_123] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',A_123))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_123)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2469,c_711])).

tff(c_2766,plain,(
    ! [A_244] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',A_244))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2185,c_124,c_2509])).

tff(c_2777,plain,(
    ! [A_244] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',A_244))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_244)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2766])).

tff(c_2788,plain,(
    ! [A_245] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',A_245))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_64,c_58,c_2777])).

tff(c_129,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_1064,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_129])).

tff(c_2804,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2788,c_1064])).

tff(c_2827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_2804])).

tff(c_2828,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_167,plain,(
    ! [A_56] :
      ( k2_relat_1(k2_funct_1(A_56)) = k1_relat_1(A_56)
      | ~ v2_funct_1(A_56)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3915,plain,(
    ! [A_360] :
      ( v1_funct_2(k2_funct_1(A_360),k1_relat_1(k2_funct_1(A_360)),k1_relat_1(A_360))
      | ~ v1_funct_1(k2_funct_1(A_360))
      | ~ v1_relat_1(k2_funct_1(A_360))
      | ~ v2_funct_1(A_360)
      | ~ v1_funct_1(A_360)
      | ~ v1_relat_1(A_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_44])).

tff(c_3918,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2828,c_3915])).

tff(c_3926,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_64,c_58,c_124,c_3918])).

tff(c_3927,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3926])).

tff(c_3930,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_3927])).

tff(c_3934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_64,c_58,c_3930])).

tff(c_3936,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3926])).

tff(c_4078,plain,(
    ! [A_375] :
      ( m1_subset_1(k2_funct_1(A_375),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_375)),k1_relat_1(A_375))))
      | ~ v1_funct_1(k2_funct_1(A_375))
      | ~ v1_relat_1(k2_funct_1(A_375))
      | ~ v2_funct_1(A_375)
      | ~ v1_funct_1(A_375)
      | ~ v1_relat_1(A_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_270])).

tff(c_4101,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2828,c_4078])).

tff(c_4116,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_64,c_58,c_3936,c_124,c_4101])).

tff(c_4139,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4116])).

tff(c_4152,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_64,c_58,c_235,c_4139])).

tff(c_4154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_4152])).

tff(c_4156,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_4172,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4156,c_4161])).

tff(c_4235,plain,(
    ! [A_392,B_393,C_394] :
      ( k2_relset_1(A_392,B_393,C_394) = k2_relat_1(C_394)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4245,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4235])).

tff(c_4249,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4245])).

tff(c_4305,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4156,c_4294])).

tff(c_4464,plain,
    ( m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4305,c_4440])).

tff(c_4475,plain,(
    m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4156,c_4464])).

tff(c_4491,plain,(
    r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4475,c_8])).

tff(c_4505,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_4491,c_2])).

tff(c_4513,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4505])).

tff(c_4520,plain,
    ( ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4513])).

tff(c_4523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4174,c_64,c_58,c_6,c_4249,c_4520])).

tff(c_4524,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4505])).

tff(c_4622,plain,(
    ! [B_417,A_418] :
      ( v1_funct_2(B_417,k1_relat_1(B_417),A_418)
      | ~ r1_tarski(k2_relat_1(B_417),A_418)
      | ~ v1_funct_1(B_417)
      | ~ v1_relat_1(B_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4625,plain,(
    ! [A_418] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_418)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_418)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4524,c_4622])).

tff(c_4693,plain,(
    ! [A_419] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_419)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4172,c_124,c_4625])).

tff(c_4700,plain,(
    ! [A_419] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_419)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_419)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4693])).

tff(c_4710,plain,(
    ! [A_420] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_420)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_420) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4174,c_64,c_58,c_4700])).

tff(c_4155,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_4713,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4710,c_4155])).

tff(c_4717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4481,c_4713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 13:36:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.79/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.10  
% 5.79/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.11  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.79/2.11  
% 5.79/2.11  %Foreground sorts:
% 5.79/2.11  
% 5.79/2.11  
% 5.79/2.11  %Background operators:
% 5.79/2.11  
% 5.79/2.11  
% 5.79/2.11  %Foreground operators:
% 5.79/2.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.79/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.79/2.11  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.79/2.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.79/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.79/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.79/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.79/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.79/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.79/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.79/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.79/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.79/2.11  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.79/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.79/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.79/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.79/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.79/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.79/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.79/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.79/2.11  
% 6.03/2.13  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.03/2.13  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.03/2.13  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 6.03/2.13  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.03/2.13  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.03/2.13  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.03/2.13  tff(f_47, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 6.03/2.13  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.03/2.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.03/2.13  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.03/2.13  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.03/2.13  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.03/2.13  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.03/2.13  tff(c_4294, plain, (![A_402, B_403, C_404]: (k1_relset_1(A_402, B_403, C_404)=k1_relat_1(C_404) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.03/2.13  tff(c_4307, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4294])).
% 6.03/2.13  tff(c_4440, plain, (![A_412, B_413, C_414]: (m1_subset_1(k1_relset_1(A_412, B_413, C_414), k1_zfmisc_1(A_412)) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.03/2.13  tff(c_4467, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4307, c_4440])).
% 6.03/2.13  tff(c_4477, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4467])).
% 6.03/2.13  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.03/2.13  tff(c_4481, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_4477, c_8])).
% 6.03/2.13  tff(c_4161, plain, (![C_376, A_377, B_378]: (v1_relat_1(C_376) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_377, B_378))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.03/2.13  tff(c_4174, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4161])).
% 6.03/2.13  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.03/2.13  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.03/2.13  tff(c_18, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.03/2.13  tff(c_92, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.03/2.13  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_92])).
% 6.03/2.13  tff(c_115, plain, (![A_41]: (v1_funct_1(k2_funct_1(A_41)) | ~v2_funct_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.03/2.13  tff(c_54, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.03/2.13  tff(c_81, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 6.03/2.13  tff(c_118, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_81])).
% 6.03/2.13  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_64, c_58, c_118])).
% 6.03/2.13  tff(c_123, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 6.03/2.13  tff(c_125, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_123])).
% 6.03/2.13  tff(c_140, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.03/2.13  tff(c_149, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_140])).
% 6.03/2.13  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.03/2.13  tff(c_225, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.03/2.13  tff(c_232, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_225])).
% 6.03/2.13  tff(c_235, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_232])).
% 6.03/2.13  tff(c_20, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.03/2.13  tff(c_16, plain, (![A_5]: (v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.03/2.13  tff(c_124, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 6.03/2.13  tff(c_191, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.03/2.13  tff(c_200, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_191])).
% 6.03/2.13  tff(c_371, plain, (![A_78, B_79, C_80]: (m1_subset_1(k1_relset_1(A_78, B_79, C_80), k1_zfmisc_1(A_78)) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.03/2.13  tff(c_395, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_200, c_371])).
% 6.03/2.13  tff(c_403, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_395])).
% 6.03/2.13  tff(c_407, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_403, c_8])).
% 6.03/2.13  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.03/2.13  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.03/2.13  tff(c_741, plain, (![B_126, A_127, C_128]: (k1_xboole_0=B_126 | k1_relset_1(A_127, B_126, C_128)=A_127 | ~v1_funct_2(C_128, A_127, B_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.03/2.13  tff(c_761, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_741])).
% 6.03/2.13  tff(c_771, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_200, c_761])).
% 6.03/2.13  tff(c_772, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_771])).
% 6.03/2.13  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.03/2.13  tff(c_410, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_407, c_2])).
% 6.03/2.13  tff(c_416, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_410])).
% 6.03/2.13  tff(c_773, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_772, c_416])).
% 6.03/2.13  tff(c_786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_773])).
% 6.03/2.13  tff(c_788, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_771])).
% 6.03/2.13  tff(c_71, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.03/2.13  tff(c_75, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_71])).
% 6.03/2.13  tff(c_787, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_771])).
% 6.03/2.13  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.03/2.13  tff(c_543, plain, (![C_98, A_99]: (k1_xboole_0=C_98 | ~v1_funct_2(C_98, A_99, k1_xboole_0) | k1_xboole_0=A_99 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.03/2.13  tff(c_553, plain, (![A_3, A_99]: (k1_xboole_0=A_3 | ~v1_funct_2(A_3, A_99, k1_xboole_0) | k1_xboole_0=A_99 | ~r1_tarski(A_3, k2_zfmisc_1(A_99, k1_xboole_0)))), inference(resolution, [status(thm)], [c_10, c_543])).
% 6.03/2.13  tff(c_866, plain, (![A_137, A_138]: (A_137='#skF_2' | ~v1_funct_2(A_137, A_138, '#skF_2') | A_138='#skF_2' | ~r1_tarski(A_137, k2_zfmisc_1(A_138, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_787, c_787, c_787, c_553])).
% 6.03/2.13  tff(c_884, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_75, c_866])).
% 6.03/2.13  tff(c_897, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_884])).
% 6.03/2.13  tff(c_899, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_897])).
% 6.03/2.13  tff(c_922, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_62])).
% 6.03/2.13  tff(c_919, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_75])).
% 6.03/2.13  tff(c_645, plain, (![B_113, C_114]: (k1_relset_1(k1_xboole_0, B_113, C_114)=k1_xboole_0 | ~v1_funct_2(C_114, k1_xboole_0, B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_113))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.03/2.13  tff(c_655, plain, (![B_113, A_3]: (k1_relset_1(k1_xboole_0, B_113, A_3)=k1_xboole_0 | ~v1_funct_2(A_3, k1_xboole_0, B_113) | ~r1_tarski(A_3, k2_zfmisc_1(k1_xboole_0, B_113)))), inference(resolution, [status(thm)], [c_10, c_645])).
% 6.03/2.13  tff(c_791, plain, (![B_113, A_3]: (k1_relset_1('#skF_2', B_113, A_3)='#skF_2' | ~v1_funct_2(A_3, '#skF_2', B_113) | ~r1_tarski(A_3, k2_zfmisc_1('#skF_2', B_113)))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_787, c_787, c_787, c_655])).
% 6.03/2.13  tff(c_987, plain, (![B_139, A_140]: (k1_relset_1('#skF_1', B_139, A_140)='#skF_1' | ~v1_funct_2(A_140, '#skF_1', B_139) | ~r1_tarski(A_140, k2_zfmisc_1('#skF_1', B_139)))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_899, c_899, c_899, c_791])).
% 6.03/2.13  tff(c_990, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_919, c_987])).
% 6.03/2.13  tff(c_1005, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_922, c_990])).
% 6.03/2.13  tff(c_920, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_60])).
% 6.03/2.13  tff(c_26, plain, (![A_13, B_14, C_15]: (k1_relset_1(A_13, B_14, C_15)=k1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.03/2.13  tff(c_1030, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_920, c_26])).
% 6.03/2.13  tff(c_1042, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1005, c_1030])).
% 6.03/2.13  tff(c_1044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_788, c_1042])).
% 6.03/2.13  tff(c_1045, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_897])).
% 6.03/2.13  tff(c_1061, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_235])).
% 6.03/2.13  tff(c_179, plain, (![A_57]: (k1_relat_1(k2_funct_1(A_57))=k2_relat_1(A_57) | ~v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.03/2.13  tff(c_44, plain, (![A_22]: (v1_funct_2(A_22, k1_relat_1(A_22), k2_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.03/2.13  tff(c_2164, plain, (![A_229]: (v1_funct_2(k2_funct_1(A_229), k2_relat_1(A_229), k2_relat_1(k2_funct_1(A_229))) | ~v1_funct_1(k2_funct_1(A_229)) | ~v1_relat_1(k2_funct_1(A_229)) | ~v2_funct_1(A_229) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229))), inference(superposition, [status(thm), theory('equality')], [c_179, c_44])).
% 6.03/2.13  tff(c_2167, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1061, c_2164])).
% 6.03/2.13  tff(c_2175, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_64, c_58, c_124, c_2167])).
% 6.03/2.13  tff(c_2176, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2175])).
% 6.03/2.13  tff(c_2179, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_2176])).
% 6.03/2.13  tff(c_2183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_64, c_58, c_2179])).
% 6.03/2.13  tff(c_2185, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2175])).
% 6.03/2.13  tff(c_2184, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2175])).
% 6.03/2.13  tff(c_270, plain, (![A_75]: (m1_subset_1(A_75, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_75), k2_relat_1(A_75)))) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.03/2.13  tff(c_2283, plain, (![A_240]: (m1_subset_1(k2_funct_1(A_240), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_240), k2_relat_1(k2_funct_1(A_240))))) | ~v1_funct_1(k2_funct_1(A_240)) | ~v1_relat_1(k2_funct_1(A_240)) | ~v2_funct_1(A_240) | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(superposition, [status(thm), theory('equality')], [c_20, c_270])).
% 6.03/2.13  tff(c_2306, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1061, c_2283])).
% 6.03/2.13  tff(c_2321, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_64, c_58, c_2185, c_124, c_2306])).
% 6.03/2.13  tff(c_38, plain, (![B_20, C_21]: (k1_relset_1(k1_xboole_0, B_20, C_21)=k1_xboole_0 | ~v1_funct_2(C_21, k1_xboole_0, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.03/2.13  tff(c_792, plain, (![B_20, C_21]: (k1_relset_1('#skF_2', B_20, C_21)='#skF_2' | ~v1_funct_2(C_21, '#skF_2', B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_20))))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_787, c_787, c_787, c_38])).
% 6.03/2.13  tff(c_1534, plain, (![B_20, C_21]: (k1_relset_1('#skF_3', B_20, C_21)='#skF_3' | ~v1_funct_2(C_21, '#skF_3', B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_20))))), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_1045, c_1045, c_1045, c_792])).
% 6.03/2.13  tff(c_2355, plain, (k1_relset_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2321, c_1534])).
% 6.03/2.13  tff(c_2382, plain, (k1_relset_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2184, c_2355])).
% 6.03/2.13  tff(c_2388, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))), inference(resolution, [status(thm)], [c_2321, c_8])).
% 6.03/2.13  tff(c_199, plain, (![A_58, B_59, A_3]: (k1_relset_1(A_58, B_59, A_3)=k1_relat_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_58, B_59)))), inference(resolution, [status(thm)], [c_10, c_191])).
% 6.03/2.13  tff(c_2446, plain, (k1_relset_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2388, c_199])).
% 6.03/2.13  tff(c_2469, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2382, c_2446])).
% 6.03/2.13  tff(c_679, plain, (![B_122, A_123]: (m1_subset_1(B_122, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_122), A_123))) | ~r1_tarski(k2_relat_1(B_122), A_123) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.03/2.13  tff(c_711, plain, (![B_122, A_123]: (r1_tarski(B_122, k2_zfmisc_1(k1_relat_1(B_122), A_123)) | ~r1_tarski(k2_relat_1(B_122), A_123) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_679, c_8])).
% 6.03/2.13  tff(c_2509, plain, (![A_123]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', A_123)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_123) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2469, c_711])).
% 6.03/2.13  tff(c_2766, plain, (![A_244]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', A_244)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_244))), inference(demodulation, [status(thm), theory('equality')], [c_2185, c_124, c_2509])).
% 6.03/2.13  tff(c_2777, plain, (![A_244]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', A_244)) | ~r1_tarski(k1_relat_1('#skF_3'), A_244) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2766])).
% 6.03/2.13  tff(c_2788, plain, (![A_245]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', A_245)) | ~r1_tarski(k1_relat_1('#skF_3'), A_245))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_64, c_58, c_2777])).
% 6.03/2.13  tff(c_129, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_10, c_125])).
% 6.03/2.13  tff(c_1064, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_129])).
% 6.03/2.13  tff(c_2804, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2788, c_1064])).
% 6.03/2.13  tff(c_2827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_407, c_2804])).
% 6.03/2.13  tff(c_2828, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_410])).
% 6.03/2.13  tff(c_167, plain, (![A_56]: (k2_relat_1(k2_funct_1(A_56))=k1_relat_1(A_56) | ~v2_funct_1(A_56) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.03/2.13  tff(c_3915, plain, (![A_360]: (v1_funct_2(k2_funct_1(A_360), k1_relat_1(k2_funct_1(A_360)), k1_relat_1(A_360)) | ~v1_funct_1(k2_funct_1(A_360)) | ~v1_relat_1(k2_funct_1(A_360)) | ~v2_funct_1(A_360) | ~v1_funct_1(A_360) | ~v1_relat_1(A_360))), inference(superposition, [status(thm), theory('equality')], [c_167, c_44])).
% 6.03/2.13  tff(c_3918, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2828, c_3915])).
% 6.03/2.13  tff(c_3926, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_64, c_58, c_124, c_3918])).
% 6.03/2.13  tff(c_3927, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3926])).
% 6.03/2.13  tff(c_3930, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_3927])).
% 6.03/2.13  tff(c_3934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_64, c_58, c_3930])).
% 6.03/2.13  tff(c_3936, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3926])).
% 6.03/2.13  tff(c_4078, plain, (![A_375]: (m1_subset_1(k2_funct_1(A_375), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_375)), k1_relat_1(A_375)))) | ~v1_funct_1(k2_funct_1(A_375)) | ~v1_relat_1(k2_funct_1(A_375)) | ~v2_funct_1(A_375) | ~v1_funct_1(A_375) | ~v1_relat_1(A_375))), inference(superposition, [status(thm), theory('equality')], [c_18, c_270])).
% 6.03/2.13  tff(c_4101, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2828, c_4078])).
% 6.03/2.13  tff(c_4116, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_64, c_58, c_3936, c_124, c_4101])).
% 6.03/2.13  tff(c_4139, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_4116])).
% 6.03/2.13  tff(c_4152, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_64, c_58, c_235, c_4139])).
% 6.03/2.13  tff(c_4154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_4152])).
% 6.03/2.13  tff(c_4156, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_123])).
% 6.03/2.13  tff(c_4172, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4156, c_4161])).
% 6.03/2.13  tff(c_4235, plain, (![A_392, B_393, C_394]: (k2_relset_1(A_392, B_393, C_394)=k2_relat_1(C_394) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.03/2.13  tff(c_4245, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4235])).
% 6.03/2.13  tff(c_4249, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4245])).
% 6.03/2.13  tff(c_4305, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4156, c_4294])).
% 6.03/2.13  tff(c_4464, plain, (m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4305, c_4440])).
% 6.03/2.13  tff(c_4475, plain, (m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4156, c_4464])).
% 6.03/2.13  tff(c_4491, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_4475, c_8])).
% 6.03/2.13  tff(c_4505, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_4491, c_2])).
% 6.03/2.13  tff(c_4513, plain, (~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_4505])).
% 6.03/2.13  tff(c_4520, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_4513])).
% 6.03/2.13  tff(c_4523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4174, c_64, c_58, c_6, c_4249, c_4520])).
% 6.03/2.13  tff(c_4524, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_4505])).
% 6.03/2.13  tff(c_4622, plain, (![B_417, A_418]: (v1_funct_2(B_417, k1_relat_1(B_417), A_418) | ~r1_tarski(k2_relat_1(B_417), A_418) | ~v1_funct_1(B_417) | ~v1_relat_1(B_417))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.03/2.13  tff(c_4625, plain, (![A_418]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_418) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_418) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4524, c_4622])).
% 6.03/2.13  tff(c_4693, plain, (![A_419]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_419) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_419))), inference(demodulation, [status(thm), theory('equality')], [c_4172, c_124, c_4625])).
% 6.03/2.13  tff(c_4700, plain, (![A_419]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_419) | ~r1_tarski(k1_relat_1('#skF_3'), A_419) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4693])).
% 6.03/2.13  tff(c_4710, plain, (![A_420]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_420) | ~r1_tarski(k1_relat_1('#skF_3'), A_420))), inference(demodulation, [status(thm), theory('equality')], [c_4174, c_64, c_58, c_4700])).
% 6.03/2.13  tff(c_4155, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_123])).
% 6.03/2.13  tff(c_4713, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_4710, c_4155])).
% 6.03/2.13  tff(c_4717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4481, c_4713])).
% 6.03/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.13  
% 6.03/2.13  Inference rules
% 6.03/2.13  ----------------------
% 6.03/2.13  #Ref     : 0
% 6.03/2.13  #Sup     : 969
% 6.03/2.13  #Fact    : 0
% 6.03/2.13  #Define  : 0
% 6.03/2.13  #Split   : 16
% 6.03/2.13  #Chain   : 0
% 6.03/2.13  #Close   : 0
% 6.03/2.13  
% 6.03/2.13  Ordering : KBO
% 6.03/2.13  
% 6.03/2.13  Simplification rules
% 6.03/2.13  ----------------------
% 6.03/2.13  #Subsume      : 116
% 6.03/2.13  #Demod        : 1015
% 6.03/2.13  #Tautology    : 392
% 6.03/2.13  #SimpNegUnit  : 9
% 6.03/2.13  #BackRed      : 88
% 6.03/2.13  
% 6.03/2.13  #Partial instantiations: 0
% 6.03/2.13  #Strategies tried      : 1
% 6.03/2.13  
% 6.03/2.13  Timing (in seconds)
% 6.03/2.13  ----------------------
% 6.03/2.13  Preprocessing        : 0.32
% 6.03/2.13  Parsing              : 0.17
% 6.03/2.13  CNF conversion       : 0.02
% 6.03/2.13  Main loop            : 1.01
% 6.03/2.13  Inferencing          : 0.36
% 6.03/2.13  Reduction            : 0.33
% 6.03/2.13  Demodulation         : 0.24
% 6.03/2.14  BG Simplification    : 0.05
% 6.03/2.14  Subsumption          : 0.18
% 6.03/2.14  Abstraction          : 0.05
% 6.03/2.14  MUC search           : 0.00
% 6.03/2.14  Cooper               : 0.00
% 6.03/2.14  Total                : 1.39
% 6.03/2.14  Index Insertion      : 0.00
% 6.03/2.14  Index Deletion       : 0.00
% 6.03/2.14  Index Matching       : 0.00
% 6.03/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
