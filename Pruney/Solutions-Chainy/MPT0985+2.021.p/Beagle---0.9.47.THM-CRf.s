%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:28 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 6.17s
% Verified   : 
% Statistics : Number of formulae       :  275 (3168 expanded)
%              Number of leaves         :   45 (1057 expanded)
%              Depth                    :   17
%              Number of atoms          :  486 (8116 expanded)
%              Number of equality atoms :  200 (2077 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
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

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_144,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_167,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_157,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_4457,plain,(
    ! [C_368,A_369,B_370] :
      ( v1_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4474,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_4457])).

tff(c_90,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_84,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_82,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_4581,plain,(
    ! [A_383,B_384,C_385] :
      ( k2_relset_1(A_383,B_384,C_385) = k2_relat_1(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4590,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_4581])).

tff(c_4600,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4590])).

tff(c_42,plain,(
    ! [A_21] :
      ( k1_relat_1(k2_funct_1(A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_80,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_145,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_148,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_151,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_148])).

tff(c_166,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_169,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_166])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_169])).

tff(c_178,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_201,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_379,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_392,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_379])).

tff(c_32,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_475,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_481,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_475])).

tff(c_490,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_481])).

tff(c_24,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_399,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_392,c_24])).

tff(c_402,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_491,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_402])).

tff(c_88,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_604,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_626,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_604])).

tff(c_1067,plain,(
    ! [B_146,A_147,C_148] :
      ( k1_xboole_0 = B_146
      | k1_relset_1(A_147,B_146,C_148) = A_147
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1079,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_1067])).

tff(c_1096,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_626,c_1079])).

tff(c_1097,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_1096])).

tff(c_441,plain,(
    ! [A_93] :
      ( k2_relat_1(k2_funct_1(A_93)) = k1_relat_1(A_93)
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1358,plain,(
    ! [A_157] :
      ( k10_relat_1(k2_funct_1(A_157),k1_relat_1(A_157)) = k1_relat_1(k2_funct_1(A_157))
      | ~ v1_relat_1(k2_funct_1(A_157))
      | ~ v2_funct_1(A_157)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_22])).

tff(c_1373,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1097,c_1358])).

tff(c_1389,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_90,c_84,c_1373])).

tff(c_1435,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1389])).

tff(c_1438,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1435])).

tff(c_1442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_90,c_1438])).

tff(c_1444,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1389])).

tff(c_179,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_20,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1131,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1097,c_20])).

tff(c_1145,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_490,c_1131])).

tff(c_1443,plain,(
    k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1389])).

tff(c_36,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(k2_funct_1(B_17),A_16) = k9_relat_1(B_17,A_16)
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1456,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k9_relat_1('#skF_4','#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1443,c_36])).

tff(c_1463,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_90,c_84,c_1145,c_1456])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [A_18,B_20] :
      ( k9_relat_1(k2_funct_1(A_18),k9_relat_1(A_18,B_20)) = B_20
      | ~ r1_tarski(B_20,k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1150,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_38])).

tff(c_1154,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_90,c_84,c_10,c_1097,c_1150])).

tff(c_1495,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_20])).

tff(c_1518,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1154,c_1495])).

tff(c_74,plain,(
    ! [A_37] :
      ( m1_subset_1(A_37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37))))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1546,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_74])).

tff(c_1576,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_179,c_1463,c_1546])).

tff(c_1578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_1576])).

tff(c_1579,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1596,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_2])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1593,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1579,c_14])).

tff(c_1580,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_1713,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1580])).

tff(c_1963,plain,(
    ! [A_185,B_186,C_187] :
      ( k2_relset_1(A_185,B_186,C_187) = k2_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1978,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_1963])).

tff(c_1982,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1713,c_82,c_1978])).

tff(c_204,plain,(
    ! [B_66,A_67] :
      ( v1_xboole_0(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_224,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_86,c_204])).

tff(c_301,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_1984,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_301])).

tff(c_1991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1596,c_1593,c_1984])).

tff(c_1992,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2000,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1992,c_4])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_194,plain,(
    ! [A_62,B_63] : m1_subset_1('#skF_1'(A_62,B_63),k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_200,plain,(
    ! [B_5] : m1_subset_1('#skF_1'(k1_xboole_0,B_5),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_194])).

tff(c_207,plain,(
    ! [B_5] :
      ( v1_xboole_0('#skF_1'(k1_xboole_0,B_5))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_200,c_204])).

tff(c_225,plain,(
    ! [B_68] : v1_xboole_0('#skF_1'(k1_xboole_0,B_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_207])).

tff(c_232,plain,(
    ! [B_68] : '#skF_1'(k1_xboole_0,B_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_4])).

tff(c_257,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_200])).

tff(c_2085,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2000,c_257])).

tff(c_259,plain,(
    ! [B_72] : '#skF_1'(k1_xboole_0,B_72) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_4])).

tff(c_70,plain,(
    ! [A_34,B_35] : v1_relat_1('#skF_1'(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_281,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_70])).

tff(c_2003,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_281])).

tff(c_197,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_194])).

tff(c_210,plain,(
    ! [A_4] :
      ( v1_xboole_0('#skF_1'(A_4,k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_197,c_204])).

tff(c_246,plain,(
    ! [A_71] : v1_xboole_0('#skF_1'(A_71,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_210])).

tff(c_253,plain,(
    ! [A_71] : '#skF_1'(A_71,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_246,c_4])).

tff(c_2092,plain,(
    ! [A_71] : '#skF_1'(A_71,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2000,c_253])).

tff(c_72,plain,(
    ! [A_34,B_35] : m1_subset_1('#skF_1'(A_34,B_35),k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3808,plain,(
    ! [A_306,B_307,C_308] :
      ( k2_relset_1(A_306,B_307,C_308) = k2_relat_1(C_308)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3819,plain,(
    ! [A_309,B_310] : k2_relset_1(A_309,B_310,'#skF_1'(A_309,B_310)) = k2_relat_1('#skF_1'(A_309,B_310)) ),
    inference(resolution,[status(thm)],[c_72,c_3808])).

tff(c_3831,plain,(
    ! [A_71] : k2_relat_1('#skF_1'(A_71,'#skF_4')) = k2_relset_1(A_71,'#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2092,c_3819])).

tff(c_3843,plain,(
    ! [A_312] : k2_relset_1(A_312,'#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2092,c_3831])).

tff(c_2011,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2000,c_14])).

tff(c_1993,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_2053,plain,(
    ! [A_192] :
      ( A_192 = '#skF_4'
      | ~ v1_xboole_0(A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_4])).

tff(c_2064,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1993,c_2053])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2307,plain,(
    ! [B_211,A_212] :
      ( B_211 = '#skF_4'
      | A_212 = '#skF_4'
      | k2_zfmisc_1(A_212,B_211) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2000,c_2000,c_12])).

tff(c_2317,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2064,c_2307])).

tff(c_2322,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2317])).

tff(c_2325,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2322,c_201])).

tff(c_2330,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_2325])).

tff(c_2004,plain,(
    ! [B_68] : '#skF_1'('#skF_4',B_68) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2000,c_232])).

tff(c_2538,plain,(
    ! [A_234,B_235,C_236] :
      ( k1_relset_1(A_234,B_235,C_236) = k1_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2561,plain,(
    ! [A_237,B_238] : k1_relset_1(A_237,B_238,'#skF_1'(A_237,B_238)) = k1_relat_1('#skF_1'(A_237,B_238)) ),
    inference(resolution,[status(thm)],[c_72,c_2538])).

tff(c_2570,plain,(
    ! [B_68] : k1_relat_1('#skF_1'('#skF_4',B_68)) = k1_relset_1('#skF_4',B_68,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2004,c_2561])).

tff(c_2576,plain,(
    ! [B_68] : k1_relset_1('#skF_4',B_68,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_2570])).

tff(c_62,plain,(
    ! [A_34,B_35] : v1_funct_2('#skF_1'(A_34,B_35),A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_58,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_91,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_2707,plain,(
    ! [B_254,C_255] :
      ( k1_relset_1('#skF_4',B_254,C_255) = '#skF_4'
      | ~ v1_funct_2(C_255,'#skF_4',B_254)
      | ~ m1_subset_1(C_255,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2000,c_2000,c_2000,c_91])).

tff(c_2715,plain,(
    ! [B_35] :
      ( k1_relset_1('#skF_4',B_35,'#skF_1'('#skF_4',B_35)) = '#skF_4'
      | ~ m1_subset_1('#skF_1'('#skF_4',B_35),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_62,c_2707])).

tff(c_2724,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_2004,c_2576,c_2004,c_2715])).

tff(c_2362,plain,(
    ! [A_217] :
      ( k2_relat_1(k2_funct_1(A_217)) = k1_relat_1(A_217)
      | ~ v2_funct_1(A_217)
      | ~ v1_funct_1(A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3512,plain,(
    ! [A_296] :
      ( k10_relat_1(k2_funct_1(A_296),k1_relat_1(A_296)) = k1_relat_1(k2_funct_1(A_296))
      | ~ v1_relat_1(k2_funct_1(A_296))
      | ~ v2_funct_1(A_296)
      | ~ v1_funct_1(A_296)
      | ~ v1_relat_1(A_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2362,c_22])).

tff(c_3530,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2724,c_3512])).

tff(c_3545,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_90,c_84,c_3530])).

tff(c_3546,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3545])).

tff(c_3549,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3546])).

tff(c_3553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_90,c_3549])).

tff(c_3555,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3545])).

tff(c_2402,plain,(
    ! [A_221,B_222,C_223] :
      ( k2_relset_1(A_221,B_222,C_223) = k2_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2413,plain,(
    ! [A_224,B_225] : k2_relset_1(A_224,B_225,'#skF_1'(A_224,B_225)) = k2_relat_1('#skF_1'(A_224,B_225)) ),
    inference(resolution,[status(thm)],[c_72,c_2402])).

tff(c_2422,plain,(
    ! [B_68] : k2_relat_1('#skF_1'('#skF_4',B_68)) = k2_relset_1('#skF_4',B_68,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2004,c_2413])).

tff(c_2430,plain,(
    ! [B_226] : k2_relset_1('#skF_4',B_226,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_2422])).

tff(c_2326,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2322,c_82])).

tff(c_2434,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2430,c_2326])).

tff(c_2753,plain,
    ( k9_relat_1('#skF_4','#skF_4') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2724,c_20])).

tff(c_2767,plain,(
    k9_relat_1('#skF_4','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_2434,c_2753])).

tff(c_2991,plain,(
    ! [A_270,B_271] :
      ( k9_relat_1(k2_funct_1(A_270),k9_relat_1(A_270,B_271)) = B_271
      | ~ r1_tarski(B_271,k1_relat_1(A_270))
      | ~ v2_funct_1(A_270)
      | ~ v1_funct_1(A_270)
      | ~ v1_relat_1(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3009,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2767,c_2991])).

tff(c_3018,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_90,c_84,c_10,c_2724,c_3009])).

tff(c_2377,plain,(
    ! [A_218] :
      ( k1_relat_1(k2_funct_1(A_218)) = k2_relat_1(A_218)
      | ~ v2_funct_1(A_218)
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3642,plain,(
    ! [A_298] :
      ( k9_relat_1(k2_funct_1(A_298),k2_relat_1(A_298)) = k2_relat_1(k2_funct_1(A_298))
      | ~ v1_relat_1(k2_funct_1(A_298))
      | ~ v2_funct_1(A_298)
      | ~ v1_funct_1(A_298)
      | ~ v1_relat_1(A_298) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2377,c_20])).

tff(c_3663,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2434,c_3642])).

tff(c_3672,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_90,c_84,c_3555,c_3018,c_3663])).

tff(c_3696,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3672,c_74])).

tff(c_3729,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3555,c_179,c_2011,c_3696])).

tff(c_3731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2330,c_3729])).

tff(c_3732,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2317])).

tff(c_3737,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3732,c_3732,c_82])).

tff(c_3850,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3843,c_3737])).

tff(c_180,plain,(
    ! [A_60] :
      ( v1_relat_1(k2_funct_1(A_60))
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_184,plain,(
    ! [A_60] :
      ( k1_relat_1(k2_funct_1(A_60)) != k1_xboole_0
      | k2_funct_1(A_60) = k1_xboole_0
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_180,c_26])).

tff(c_3962,plain,(
    ! [A_322] :
      ( k1_relat_1(k2_funct_1(A_322)) != '#skF_4'
      | k2_funct_1(A_322) = '#skF_4'
      | ~ v1_funct_1(A_322)
      | ~ v1_relat_1(A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2000,c_184])).

tff(c_4261,plain,(
    ! [A_349] :
      ( k2_relat_1(A_349) != '#skF_4'
      | k2_funct_1(A_349) = '#skF_4'
      | ~ v1_funct_1(A_349)
      | ~ v1_relat_1(A_349)
      | ~ v2_funct_1(A_349)
      | ~ v1_funct_1(A_349)
      | ~ v1_relat_1(A_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3962])).

tff(c_4264,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_4261])).

tff(c_4267,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_90,c_3850,c_4264])).

tff(c_2013,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2000,c_16])).

tff(c_3736,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3732,c_201])).

tff(c_3741,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_3736])).

tff(c_4268,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4267,c_3741])).

tff(c_4272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_4268])).

tff(c_4273,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_4481,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4474,c_24])).

tff(c_4491,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4481])).

tff(c_4601,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4600,c_4491])).

tff(c_4716,plain,(
    ! [A_395,B_396,C_397] :
      ( k1_relset_1(A_395,B_396,C_397) = k1_relat_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4742,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_4716])).

tff(c_4998,plain,(
    ! [B_421,A_422,C_423] :
      ( k1_xboole_0 = B_421
      | k1_relset_1(A_422,B_421,C_423) = A_422
      | ~ v1_funct_2(C_423,A_422,B_421)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_422,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5013,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_4998])).

tff(c_5032,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4742,c_5013])).

tff(c_5033,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4601,c_5032])).

tff(c_4482,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4474,c_26])).

tff(c_4492,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4482])).

tff(c_5043,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5033,c_4492])).

tff(c_4274,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_4740,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4274,c_4716])).

tff(c_5137,plain,(
    ! [B_424,C_425,A_426] :
      ( k1_xboole_0 = B_424
      | v1_funct_2(C_425,A_426,B_424)
      | k1_relset_1(A_426,B_424,C_425) != A_426
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(A_426,B_424))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5143,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4274,c_5137])).

tff(c_5158,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4740,c_5143])).

tff(c_5159,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4273,c_5043,c_5158])).

tff(c_5169,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5159])).

tff(c_5172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4474,c_90,c_84,c_4600,c_5169])).

tff(c_5173,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4482])).

tff(c_5175,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5173,c_4491])).

tff(c_5174,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4482])).

tff(c_5203,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5173,c_5174])).

tff(c_5392,plain,(
    ! [A_439] :
      ( k2_relat_1(k2_funct_1(A_439)) = k1_relat_1(A_439)
      | ~ v2_funct_1(A_439)
      | ~ v1_funct_1(A_439)
      | ~ v1_relat_1(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4471,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4274,c_4457])).

tff(c_4489,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4471,c_24])).

tff(c_5383,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5173,c_5173,c_4489])).

tff(c_5384,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5383])).

tff(c_5398,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5392,c_5384])).

tff(c_5411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4474,c_90,c_84,c_5203,c_5398])).

tff(c_5412,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5383])).

tff(c_4490,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4471,c_26])).

tff(c_5282,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5173,c_5173,c_4490])).

tff(c_5283,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5282])).

tff(c_5414,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5412,c_5283])).

tff(c_5421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5203,c_5414])).

tff(c_5422,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5282])).

tff(c_5569,plain,(
    ! [A_447] :
      ( k1_relat_1(k2_funct_1(A_447)) = k2_relat_1(A_447)
      | ~ v2_funct_1(A_447)
      | ~ v1_funct_1(A_447)
      | ~ v1_relat_1(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5584,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5422,c_5569])).

tff(c_5588,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4474,c_90,c_84,c_5203,c_5584])).

tff(c_5590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5175,c_5588])).

tff(c_5591,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4481])).

tff(c_4277,plain,(
    ! [B_352,A_353] :
      ( v1_xboole_0(B_352)
      | ~ m1_subset_1(B_352,k1_zfmisc_1(A_353))
      | ~ v1_xboole_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4283,plain,(
    ! [B_5] :
      ( v1_xboole_0('#skF_1'(k1_xboole_0,B_5))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_200,c_4277])).

tff(c_4313,plain,(
    ! [B_356] : v1_xboole_0('#skF_1'(k1_xboole_0,B_356)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4283])).

tff(c_4320,plain,(
    ! [B_356] : '#skF_1'(k1_xboole_0,B_356) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4313,c_4])).

tff(c_5900,plain,(
    ! [B_463] : '#skF_1'('#skF_4',B_463) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5591,c_5591,c_4320])).

tff(c_5911,plain,(
    ! [B_463] : v1_funct_2('#skF_4','#skF_4',B_463) ),
    inference(superposition,[status(thm),theory(equality)],[c_5900,c_62])).

tff(c_5592,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4481])).

tff(c_5620,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5591,c_5592])).

tff(c_6069,plain,(
    ! [A_474,B_475,C_476] :
      ( k2_relset_1(A_474,B_475,C_476) = k2_relat_1(C_476)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(k2_zfmisc_1(A_474,B_475))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6084,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_6069])).

tff(c_6089,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5620,c_6084])).

tff(c_5820,plain,(
    ! [A_461] :
      ( k1_relat_1(k2_funct_1(A_461)) = k2_relat_1(A_461)
      | ~ v2_funct_1(A_461)
      | ~ v1_funct_1(A_461)
      | ~ v1_relat_1(A_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5706,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5591,c_5591,c_4490])).

tff(c_5707,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5706])).

tff(c_5829,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5820,c_5707])).

tff(c_5839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4474,c_90,c_84,c_5620,c_5829])).

tff(c_5840,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5706])).

tff(c_5844,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5840,c_4273])).

tff(c_6091,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6089,c_5844])).

tff(c_6100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5911,c_6091])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:15:52 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.22  
% 6.17/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.23  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.17/2.23  
% 6.17/2.23  %Foreground sorts:
% 6.17/2.23  
% 6.17/2.23  
% 6.17/2.23  %Background operators:
% 6.17/2.23  
% 6.17/2.23  
% 6.17/2.23  %Foreground operators:
% 6.17/2.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.17/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.17/2.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.17/2.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.17/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.17/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.17/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.17/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.17/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.17/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.17/2.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.17/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.17/2.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.17/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.17/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.17/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.17/2.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.17/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.17/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.17/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.17/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.17/2.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.17/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.17/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.17/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.17/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.17/2.23  
% 6.17/2.26  tff(f_184, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.17/2.26  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.17/2.26  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.17/2.26  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.17/2.26  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.17/2.26  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.17/2.26  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.17/2.26  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.17/2.26  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 6.17/2.26  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 6.17/2.26  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 6.17/2.26  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.17/2.26  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 6.17/2.26  tff(f_167, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.17/2.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.17/2.26  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.17/2.26  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.17/2.26  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.17/2.26  tff(f_157, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 6.17/2.26  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.17/2.26  tff(c_4457, plain, (![C_368, A_369, B_370]: (v1_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.17/2.26  tff(c_4474, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_4457])).
% 6.17/2.26  tff(c_90, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.17/2.26  tff(c_84, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.17/2.26  tff(c_82, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.17/2.26  tff(c_4581, plain, (![A_383, B_384, C_385]: (k2_relset_1(A_383, B_384, C_385)=k2_relat_1(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.17/2.26  tff(c_4590, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_4581])).
% 6.17/2.26  tff(c_4600, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4590])).
% 6.17/2.26  tff(c_42, plain, (![A_21]: (k1_relat_1(k2_funct_1(A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.17/2.26  tff(c_30, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.17/2.26  tff(c_80, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.17/2.26  tff(c_145, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_80])).
% 6.17/2.26  tff(c_148, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_145])).
% 6.17/2.26  tff(c_151, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_148])).
% 6.17/2.26  tff(c_166, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.17/2.26  tff(c_169, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_166])).
% 6.17/2.26  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_169])).
% 6.17/2.26  tff(c_178, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_80])).
% 6.17/2.26  tff(c_201, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_178])).
% 6.17/2.26  tff(c_379, plain, (![C_82, A_83, B_84]: (v1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.17/2.26  tff(c_392, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_379])).
% 6.17/2.26  tff(c_32, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.17/2.26  tff(c_475, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.17/2.26  tff(c_481, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_475])).
% 6.17/2.26  tff(c_490, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_481])).
% 6.17/2.26  tff(c_24, plain, (![A_11]: (k2_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.17/2.26  tff(c_399, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_392, c_24])).
% 6.17/2.26  tff(c_402, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_399])).
% 6.17/2.26  tff(c_491, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_490, c_402])).
% 6.17/2.26  tff(c_88, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.17/2.26  tff(c_604, plain, (![A_109, B_110, C_111]: (k1_relset_1(A_109, B_110, C_111)=k1_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.17/2.26  tff(c_626, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_604])).
% 6.17/2.26  tff(c_1067, plain, (![B_146, A_147, C_148]: (k1_xboole_0=B_146 | k1_relset_1(A_147, B_146, C_148)=A_147 | ~v1_funct_2(C_148, A_147, B_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.17/2.26  tff(c_1079, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_1067])).
% 6.17/2.26  tff(c_1096, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_626, c_1079])).
% 6.17/2.26  tff(c_1097, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_491, c_1096])).
% 6.17/2.26  tff(c_441, plain, (![A_93]: (k2_relat_1(k2_funct_1(A_93))=k1_relat_1(A_93) | ~v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.17/2.26  tff(c_22, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.17/2.26  tff(c_1358, plain, (![A_157]: (k10_relat_1(k2_funct_1(A_157), k1_relat_1(A_157))=k1_relat_1(k2_funct_1(A_157)) | ~v1_relat_1(k2_funct_1(A_157)) | ~v2_funct_1(A_157) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(superposition, [status(thm), theory('equality')], [c_441, c_22])).
% 6.17/2.26  tff(c_1373, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1097, c_1358])).
% 6.17/2.26  tff(c_1389, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_90, c_84, c_1373])).
% 6.17/2.26  tff(c_1435, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1389])).
% 6.17/2.26  tff(c_1438, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1435])).
% 6.17/2.26  tff(c_1442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_392, c_90, c_1438])).
% 6.17/2.26  tff(c_1444, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1389])).
% 6.17/2.26  tff(c_179, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_80])).
% 6.17/2.26  tff(c_20, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.17/2.26  tff(c_1131, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1097, c_20])).
% 6.17/2.26  tff(c_1145, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_392, c_490, c_1131])).
% 6.17/2.26  tff(c_1443, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1389])).
% 6.17/2.26  tff(c_36, plain, (![B_17, A_16]: (k10_relat_1(k2_funct_1(B_17), A_16)=k9_relat_1(B_17, A_16) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.17/2.26  tff(c_1456, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k9_relat_1('#skF_4', '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1443, c_36])).
% 6.17/2.26  tff(c_1463, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_392, c_90, c_84, c_1145, c_1456])).
% 6.17/2.26  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.17/2.26  tff(c_38, plain, (![A_18, B_20]: (k9_relat_1(k2_funct_1(A_18), k9_relat_1(A_18, B_20))=B_20 | ~r1_tarski(B_20, k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.17/2.26  tff(c_1150, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1145, c_38])).
% 6.17/2.26  tff(c_1154, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_392, c_90, c_84, c_10, c_1097, c_1150])).
% 6.17/2.26  tff(c_1495, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1463, c_20])).
% 6.17/2.26  tff(c_1518, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1154, c_1495])).
% 6.17/2.26  tff(c_74, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37)))) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.17/2.26  tff(c_1546, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1518, c_74])).
% 6.17/2.26  tff(c_1576, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_179, c_1463, c_1546])).
% 6.17/2.26  tff(c_1578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_1576])).
% 6.17/2.26  tff(c_1579, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_399])).
% 6.17/2.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.17/2.26  tff(c_1596, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_2])).
% 6.17/2.26  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.17/2.26  tff(c_1593, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1579, c_14])).
% 6.17/2.26  tff(c_1580, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_399])).
% 6.17/2.26  tff(c_1713, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1580])).
% 6.17/2.26  tff(c_1963, plain, (![A_185, B_186, C_187]: (k2_relset_1(A_185, B_186, C_187)=k2_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.17/2.26  tff(c_1978, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_1963])).
% 6.17/2.26  tff(c_1982, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1713, c_82, c_1978])).
% 6.17/2.26  tff(c_204, plain, (![B_66, A_67]: (v1_xboole_0(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.17/2.26  tff(c_224, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_86, c_204])).
% 6.17/2.26  tff(c_301, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_224])).
% 6.17/2.26  tff(c_1984, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_301])).
% 6.17/2.26  tff(c_1991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1596, c_1593, c_1984])).
% 6.17/2.26  tff(c_1992, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_224])).
% 6.17/2.26  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.17/2.26  tff(c_2000, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1992, c_4])).
% 6.17/2.26  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.17/2.26  tff(c_194, plain, (![A_62, B_63]: (m1_subset_1('#skF_1'(A_62, B_63), k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.17/2.26  tff(c_200, plain, (![B_5]: (m1_subset_1('#skF_1'(k1_xboole_0, B_5), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_194])).
% 6.17/2.26  tff(c_207, plain, (![B_5]: (v1_xboole_0('#skF_1'(k1_xboole_0, B_5)) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_200, c_204])).
% 6.17/2.26  tff(c_225, plain, (![B_68]: (v1_xboole_0('#skF_1'(k1_xboole_0, B_68)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_207])).
% 6.17/2.26  tff(c_232, plain, (![B_68]: ('#skF_1'(k1_xboole_0, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_225, c_4])).
% 6.17/2.26  tff(c_257, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_200])).
% 6.17/2.26  tff(c_2085, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2000, c_257])).
% 6.17/2.26  tff(c_259, plain, (![B_72]: ('#skF_1'(k1_xboole_0, B_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_225, c_4])).
% 6.17/2.26  tff(c_70, plain, (![A_34, B_35]: (v1_relat_1('#skF_1'(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.17/2.26  tff(c_281, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_259, c_70])).
% 6.17/2.26  tff(c_2003, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_281])).
% 6.17/2.26  tff(c_197, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_194])).
% 6.17/2.26  tff(c_210, plain, (![A_4]: (v1_xboole_0('#skF_1'(A_4, k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_197, c_204])).
% 6.17/2.26  tff(c_246, plain, (![A_71]: (v1_xboole_0('#skF_1'(A_71, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_210])).
% 6.17/2.26  tff(c_253, plain, (![A_71]: ('#skF_1'(A_71, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_246, c_4])).
% 6.17/2.26  tff(c_2092, plain, (![A_71]: ('#skF_1'(A_71, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2000, c_253])).
% 6.17/2.26  tff(c_72, plain, (![A_34, B_35]: (m1_subset_1('#skF_1'(A_34, B_35), k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.17/2.26  tff(c_3808, plain, (![A_306, B_307, C_308]: (k2_relset_1(A_306, B_307, C_308)=k2_relat_1(C_308) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.17/2.26  tff(c_3819, plain, (![A_309, B_310]: (k2_relset_1(A_309, B_310, '#skF_1'(A_309, B_310))=k2_relat_1('#skF_1'(A_309, B_310)))), inference(resolution, [status(thm)], [c_72, c_3808])).
% 6.17/2.26  tff(c_3831, plain, (![A_71]: (k2_relat_1('#skF_1'(A_71, '#skF_4'))=k2_relset_1(A_71, '#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2092, c_3819])).
% 6.17/2.26  tff(c_3843, plain, (![A_312]: (k2_relset_1(A_312, '#skF_4', '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2092, c_3831])).
% 6.17/2.26  tff(c_2011, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2000, c_14])).
% 6.17/2.26  tff(c_1993, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_224])).
% 6.17/2.26  tff(c_2053, plain, (![A_192]: (A_192='#skF_4' | ~v1_xboole_0(A_192))), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_4])).
% 6.17/2.26  tff(c_2064, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1993, c_2053])).
% 6.17/2.26  tff(c_12, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.17/2.26  tff(c_2307, plain, (![B_211, A_212]: (B_211='#skF_4' | A_212='#skF_4' | k2_zfmisc_1(A_212, B_211)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2000, c_2000, c_12])).
% 6.17/2.26  tff(c_2317, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2064, c_2307])).
% 6.17/2.26  tff(c_2322, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_2317])).
% 6.17/2.26  tff(c_2325, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2322, c_201])).
% 6.17/2.26  tff(c_2330, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2011, c_2325])).
% 6.17/2.26  tff(c_2004, plain, (![B_68]: ('#skF_1'('#skF_4', B_68)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2000, c_232])).
% 6.17/2.26  tff(c_2538, plain, (![A_234, B_235, C_236]: (k1_relset_1(A_234, B_235, C_236)=k1_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.17/2.26  tff(c_2561, plain, (![A_237, B_238]: (k1_relset_1(A_237, B_238, '#skF_1'(A_237, B_238))=k1_relat_1('#skF_1'(A_237, B_238)))), inference(resolution, [status(thm)], [c_72, c_2538])).
% 6.17/2.26  tff(c_2570, plain, (![B_68]: (k1_relat_1('#skF_1'('#skF_4', B_68))=k1_relset_1('#skF_4', B_68, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2004, c_2561])).
% 6.17/2.26  tff(c_2576, plain, (![B_68]: (k1_relset_1('#skF_4', B_68, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2004, c_2570])).
% 6.17/2.26  tff(c_62, plain, (![A_34, B_35]: (v1_funct_2('#skF_1'(A_34, B_35), A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.17/2.26  tff(c_58, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.17/2.26  tff(c_91, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 6.17/2.26  tff(c_2707, plain, (![B_254, C_255]: (k1_relset_1('#skF_4', B_254, C_255)='#skF_4' | ~v1_funct_2(C_255, '#skF_4', B_254) | ~m1_subset_1(C_255, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2000, c_2000, c_2000, c_91])).
% 6.17/2.26  tff(c_2715, plain, (![B_35]: (k1_relset_1('#skF_4', B_35, '#skF_1'('#skF_4', B_35))='#skF_4' | ~m1_subset_1('#skF_1'('#skF_4', B_35), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_62, c_2707])).
% 6.17/2.26  tff(c_2724, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2085, c_2004, c_2576, c_2004, c_2715])).
% 6.17/2.26  tff(c_2362, plain, (![A_217]: (k2_relat_1(k2_funct_1(A_217))=k1_relat_1(A_217) | ~v2_funct_1(A_217) | ~v1_funct_1(A_217) | ~v1_relat_1(A_217))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.17/2.26  tff(c_3512, plain, (![A_296]: (k10_relat_1(k2_funct_1(A_296), k1_relat_1(A_296))=k1_relat_1(k2_funct_1(A_296)) | ~v1_relat_1(k2_funct_1(A_296)) | ~v2_funct_1(A_296) | ~v1_funct_1(A_296) | ~v1_relat_1(A_296))), inference(superposition, [status(thm), theory('equality')], [c_2362, c_22])).
% 6.17/2.26  tff(c_3530, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2724, c_3512])).
% 6.17/2.26  tff(c_3545, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_90, c_84, c_3530])).
% 6.17/2.26  tff(c_3546, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3545])).
% 6.17/2.26  tff(c_3549, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3546])).
% 6.17/2.26  tff(c_3553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2003, c_90, c_3549])).
% 6.17/2.26  tff(c_3555, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3545])).
% 6.17/2.26  tff(c_2402, plain, (![A_221, B_222, C_223]: (k2_relset_1(A_221, B_222, C_223)=k2_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.17/2.26  tff(c_2413, plain, (![A_224, B_225]: (k2_relset_1(A_224, B_225, '#skF_1'(A_224, B_225))=k2_relat_1('#skF_1'(A_224, B_225)))), inference(resolution, [status(thm)], [c_72, c_2402])).
% 6.17/2.26  tff(c_2422, plain, (![B_68]: (k2_relat_1('#skF_1'('#skF_4', B_68))=k2_relset_1('#skF_4', B_68, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2004, c_2413])).
% 6.17/2.26  tff(c_2430, plain, (![B_226]: (k2_relset_1('#skF_4', B_226, '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2004, c_2422])).
% 6.17/2.26  tff(c_2326, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2322, c_82])).
% 6.17/2.26  tff(c_2434, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2430, c_2326])).
% 6.17/2.26  tff(c_2753, plain, (k9_relat_1('#skF_4', '#skF_4')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2724, c_20])).
% 6.17/2.26  tff(c_2767, plain, (k9_relat_1('#skF_4', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_2434, c_2753])).
% 6.17/2.26  tff(c_2991, plain, (![A_270, B_271]: (k9_relat_1(k2_funct_1(A_270), k9_relat_1(A_270, B_271))=B_271 | ~r1_tarski(B_271, k1_relat_1(A_270)) | ~v2_funct_1(A_270) | ~v1_funct_1(A_270) | ~v1_relat_1(A_270))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.17/2.26  tff(c_3009, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2767, c_2991])).
% 6.17/2.26  tff(c_3018, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_90, c_84, c_10, c_2724, c_3009])).
% 6.17/2.26  tff(c_2377, plain, (![A_218]: (k1_relat_1(k2_funct_1(A_218))=k2_relat_1(A_218) | ~v2_funct_1(A_218) | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.17/2.26  tff(c_3642, plain, (![A_298]: (k9_relat_1(k2_funct_1(A_298), k2_relat_1(A_298))=k2_relat_1(k2_funct_1(A_298)) | ~v1_relat_1(k2_funct_1(A_298)) | ~v2_funct_1(A_298) | ~v1_funct_1(A_298) | ~v1_relat_1(A_298))), inference(superposition, [status(thm), theory('equality')], [c_2377, c_20])).
% 6.17/2.26  tff(c_3663, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2434, c_3642])).
% 6.17/2.26  tff(c_3672, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_90, c_84, c_3555, c_3018, c_3663])).
% 6.17/2.26  tff(c_3696, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3672, c_74])).
% 6.17/2.26  tff(c_3729, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3555, c_179, c_2011, c_3696])).
% 6.17/2.26  tff(c_3731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2330, c_3729])).
% 6.17/2.26  tff(c_3732, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2317])).
% 6.17/2.26  tff(c_3737, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3732, c_3732, c_82])).
% 6.17/2.26  tff(c_3850, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3843, c_3737])).
% 6.17/2.26  tff(c_180, plain, (![A_60]: (v1_relat_1(k2_funct_1(A_60)) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.17/2.26  tff(c_26, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.17/2.26  tff(c_184, plain, (![A_60]: (k1_relat_1(k2_funct_1(A_60))!=k1_xboole_0 | k2_funct_1(A_60)=k1_xboole_0 | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_180, c_26])).
% 6.17/2.26  tff(c_3962, plain, (![A_322]: (k1_relat_1(k2_funct_1(A_322))!='#skF_4' | k2_funct_1(A_322)='#skF_4' | ~v1_funct_1(A_322) | ~v1_relat_1(A_322))), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2000, c_184])).
% 6.17/2.26  tff(c_4261, plain, (![A_349]: (k2_relat_1(A_349)!='#skF_4' | k2_funct_1(A_349)='#skF_4' | ~v1_funct_1(A_349) | ~v1_relat_1(A_349) | ~v2_funct_1(A_349) | ~v1_funct_1(A_349) | ~v1_relat_1(A_349))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3962])).
% 6.17/2.26  tff(c_4264, plain, (k2_relat_1('#skF_4')!='#skF_4' | k2_funct_1('#skF_4')='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_4261])).
% 6.17/2.26  tff(c_4267, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_90, c_3850, c_4264])).
% 6.17/2.26  tff(c_2013, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2000, c_16])).
% 6.17/2.26  tff(c_3736, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3732, c_201])).
% 6.17/2.26  tff(c_3741, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2013, c_3736])).
% 6.17/2.26  tff(c_4268, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4267, c_3741])).
% 6.17/2.26  tff(c_4272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2085, c_4268])).
% 6.17/2.26  tff(c_4273, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 6.17/2.26  tff(c_4481, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4474, c_24])).
% 6.17/2.26  tff(c_4491, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4481])).
% 6.17/2.26  tff(c_4601, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4600, c_4491])).
% 6.17/2.26  tff(c_4716, plain, (![A_395, B_396, C_397]: (k1_relset_1(A_395, B_396, C_397)=k1_relat_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.17/2.26  tff(c_4742, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_4716])).
% 6.17/2.26  tff(c_4998, plain, (![B_421, A_422, C_423]: (k1_xboole_0=B_421 | k1_relset_1(A_422, B_421, C_423)=A_422 | ~v1_funct_2(C_423, A_422, B_421) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_422, B_421))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.17/2.26  tff(c_5013, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_4998])).
% 6.17/2.26  tff(c_5032, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4742, c_5013])).
% 6.17/2.26  tff(c_5033, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4601, c_5032])).
% 6.17/2.26  tff(c_4482, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4474, c_26])).
% 6.17/2.26  tff(c_4492, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4482])).
% 6.17/2.26  tff(c_5043, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5033, c_4492])).
% 6.17/2.26  tff(c_4274, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_178])).
% 6.17/2.26  tff(c_4740, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4274, c_4716])).
% 6.17/2.26  tff(c_5137, plain, (![B_424, C_425, A_426]: (k1_xboole_0=B_424 | v1_funct_2(C_425, A_426, B_424) | k1_relset_1(A_426, B_424, C_425)!=A_426 | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(A_426, B_424))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.17/2.26  tff(c_5143, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_4274, c_5137])).
% 6.17/2.26  tff(c_5158, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4740, c_5143])).
% 6.17/2.26  tff(c_5159, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4273, c_5043, c_5158])).
% 6.17/2.26  tff(c_5169, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_5159])).
% 6.17/2.26  tff(c_5172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4474, c_90, c_84, c_4600, c_5169])).
% 6.17/2.26  tff(c_5173, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4482])).
% 6.17/2.26  tff(c_5175, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5173, c_4491])).
% 6.17/2.26  tff(c_5174, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4482])).
% 6.17/2.26  tff(c_5203, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5173, c_5174])).
% 6.17/2.26  tff(c_5392, plain, (![A_439]: (k2_relat_1(k2_funct_1(A_439))=k1_relat_1(A_439) | ~v2_funct_1(A_439) | ~v1_funct_1(A_439) | ~v1_relat_1(A_439))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.17/2.26  tff(c_4471, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4274, c_4457])).
% 6.17/2.26  tff(c_4489, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4471, c_24])).
% 6.17/2.26  tff(c_5383, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5173, c_5173, c_4489])).
% 6.17/2.26  tff(c_5384, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_5383])).
% 6.17/2.26  tff(c_5398, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5392, c_5384])).
% 6.17/2.26  tff(c_5411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4474, c_90, c_84, c_5203, c_5398])).
% 6.17/2.26  tff(c_5412, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_5383])).
% 6.17/2.26  tff(c_4490, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4471, c_26])).
% 6.17/2.26  tff(c_5282, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5173, c_5173, c_4490])).
% 6.17/2.26  tff(c_5283, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_5282])).
% 6.17/2.26  tff(c_5414, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5412, c_5283])).
% 6.17/2.26  tff(c_5421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5203, c_5414])).
% 6.17/2.26  tff(c_5422, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_5282])).
% 6.17/2.26  tff(c_5569, plain, (![A_447]: (k1_relat_1(k2_funct_1(A_447))=k2_relat_1(A_447) | ~v2_funct_1(A_447) | ~v1_funct_1(A_447) | ~v1_relat_1(A_447))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.17/2.26  tff(c_5584, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5422, c_5569])).
% 6.17/2.26  tff(c_5588, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4474, c_90, c_84, c_5203, c_5584])).
% 6.17/2.26  tff(c_5590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5175, c_5588])).
% 6.17/2.26  tff(c_5591, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4481])).
% 6.17/2.26  tff(c_4277, plain, (![B_352, A_353]: (v1_xboole_0(B_352) | ~m1_subset_1(B_352, k1_zfmisc_1(A_353)) | ~v1_xboole_0(A_353))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.17/2.26  tff(c_4283, plain, (![B_5]: (v1_xboole_0('#skF_1'(k1_xboole_0, B_5)) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_200, c_4277])).
% 6.17/2.26  tff(c_4313, plain, (![B_356]: (v1_xboole_0('#skF_1'(k1_xboole_0, B_356)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4283])).
% 6.17/2.26  tff(c_4320, plain, (![B_356]: ('#skF_1'(k1_xboole_0, B_356)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4313, c_4])).
% 6.17/2.26  tff(c_5900, plain, (![B_463]: ('#skF_1'('#skF_4', B_463)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5591, c_5591, c_4320])).
% 6.17/2.26  tff(c_5911, plain, (![B_463]: (v1_funct_2('#skF_4', '#skF_4', B_463))), inference(superposition, [status(thm), theory('equality')], [c_5900, c_62])).
% 6.17/2.26  tff(c_5592, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4481])).
% 6.17/2.26  tff(c_5620, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5591, c_5592])).
% 6.17/2.26  tff(c_6069, plain, (![A_474, B_475, C_476]: (k2_relset_1(A_474, B_475, C_476)=k2_relat_1(C_476) | ~m1_subset_1(C_476, k1_zfmisc_1(k2_zfmisc_1(A_474, B_475))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.17/2.26  tff(c_6084, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_6069])).
% 6.17/2.26  tff(c_6089, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_5620, c_6084])).
% 6.17/2.26  tff(c_5820, plain, (![A_461]: (k1_relat_1(k2_funct_1(A_461))=k2_relat_1(A_461) | ~v2_funct_1(A_461) | ~v1_funct_1(A_461) | ~v1_relat_1(A_461))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.17/2.26  tff(c_5706, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5591, c_5591, c_4490])).
% 6.17/2.26  tff(c_5707, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_5706])).
% 6.17/2.26  tff(c_5829, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5820, c_5707])).
% 6.17/2.26  tff(c_5839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4474, c_90, c_84, c_5620, c_5829])).
% 6.17/2.26  tff(c_5840, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_5706])).
% 6.17/2.26  tff(c_5844, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5840, c_4273])).
% 6.17/2.26  tff(c_6091, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6089, c_5844])).
% 6.17/2.26  tff(c_6100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5911, c_6091])).
% 6.17/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.26  
% 6.17/2.26  Inference rules
% 6.17/2.26  ----------------------
% 6.17/2.26  #Ref     : 0
% 6.17/2.26  #Sup     : 1374
% 6.17/2.26  #Fact    : 0
% 6.17/2.26  #Define  : 0
% 6.17/2.26  #Split   : 25
% 6.17/2.26  #Chain   : 0
% 6.17/2.26  #Close   : 0
% 6.17/2.26  
% 6.17/2.26  Ordering : KBO
% 6.17/2.26  
% 6.17/2.26  Simplification rules
% 6.17/2.26  ----------------------
% 6.17/2.26  #Subsume      : 66
% 6.17/2.26  #Demod        : 1540
% 6.17/2.26  #Tautology    : 923
% 6.17/2.26  #SimpNegUnit  : 15
% 6.17/2.26  #BackRed      : 154
% 6.17/2.26  
% 6.17/2.26  #Partial instantiations: 0
% 6.17/2.26  #Strategies tried      : 1
% 6.17/2.26  
% 6.17/2.26  Timing (in seconds)
% 6.17/2.26  ----------------------
% 6.17/2.26  Preprocessing        : 0.37
% 6.17/2.26  Parsing              : 0.19
% 6.17/2.26  CNF conversion       : 0.02
% 6.17/2.26  Main loop            : 1.06
% 6.17/2.26  Inferencing          : 0.38
% 6.17/2.26  Reduction            : 0.38
% 6.17/2.26  Demodulation         : 0.27
% 6.17/2.26  BG Simplification    : 0.05
% 6.17/2.26  Subsumption          : 0.16
% 6.17/2.26  Abstraction          : 0.05
% 6.17/2.26  MUC search           : 0.00
% 6.17/2.26  Cooper               : 0.00
% 6.17/2.26  Total                : 1.50
% 6.17/2.26  Index Insertion      : 0.00
% 6.17/2.26  Index Deletion       : 0.00
% 6.17/2.26  Index Matching       : 0.00
% 6.17/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
