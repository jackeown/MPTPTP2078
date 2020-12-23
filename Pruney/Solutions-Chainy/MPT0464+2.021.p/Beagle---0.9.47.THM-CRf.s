%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:45 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 147 expanded)
%              Number of leaves         :   42 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 256 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_132,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_106,plain,(
    ! [A_72,B_73] : r1_tarski(k3_xboole_0(A_72,B_73),A_72) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_106])).

tff(c_146,plain,(
    ! [B_91,C_92,A_93] :
      ( r2_hidden(B_91,C_92)
      | ~ r1_tarski(k2_tarski(A_93,B_91),C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_151,plain,(
    ! [B_91,A_93] : r2_hidden(B_91,k2_tarski(A_93,B_91)) ),
    inference(resolution,[status(thm)],[c_109,c_146])).

tff(c_76,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(k2_tarski(A_32,B_33),C_34)
      | ~ r2_hidden(B_33,C_34)
      | ~ r2_hidden(A_32,C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_153,plain,(
    ! [A_96,C_97,B_98] :
      ( r2_hidden(A_96,C_97)
      | ~ r1_tarski(k2_tarski(A_96,B_98),C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_158,plain,(
    ! [A_96,B_98] : r2_hidden(A_96,k2_tarski(A_96,B_98)) ),
    inference(resolution,[status(thm)],[c_109,c_153])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_160,plain,(
    ! [B_101,A_102] :
      ( ~ r1_xboole_0(B_101,A_102)
      | ~ r1_tarski(B_101,A_102)
      | v1_xboole_0(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_222,plain,(
    ! [A_137,B_138] :
      ( ~ r1_tarski(k4_xboole_0(A_137,B_138),B_138)
      | v1_xboole_0(k4_xboole_0(A_137,B_138)) ) ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_228,plain,(
    ! [A_139] : v1_xboole_0(k4_xboole_0(A_139,A_139)) ),
    inference(resolution,[status(thm)],[c_12,c_222])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_111,plain,(
    ! [B_75,A_76] :
      ( ~ v1_xboole_0(B_75)
      | B_75 = A_76
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    ! [A_76] :
      ( k1_xboole_0 = A_76
      | ~ v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_2,c_111])).

tff(c_234,plain,(
    ! [A_139] : k4_xboole_0(A_139,A_139) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_228,c_114])).

tff(c_326,plain,(
    ! [A_149,C_150,B_151] :
      ( ~ r2_hidden(A_149,C_150)
      | k4_xboole_0(k2_tarski(A_149,B_151),C_150) != k2_tarski(A_149,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_330,plain,(
    ! [A_149,B_151] :
      ( ~ r2_hidden(A_149,k2_tarski(A_149,B_151))
      | k2_tarski(A_149,B_151) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_326])).

tff(c_332,plain,(
    ! [A_149,B_151] : k2_tarski(A_149,B_151) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_330])).

tff(c_236,plain,(
    ! [B_140,A_141] :
      ( r1_tarski(k1_setfam_1(B_140),k1_setfam_1(A_141))
      | k1_xboole_0 = A_141
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_245,plain,(
    ! [B_140,A_47,B_48] :
      ( r1_tarski(k1_setfam_1(B_140),k3_xboole_0(A_47,B_48))
      | k2_tarski(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(k2_tarski(A_47,B_48),B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_236])).

tff(c_1330,plain,(
    ! [B_385,A_386,B_387] :
      ( r1_tarski(k1_setfam_1(B_385),k3_xboole_0(A_386,B_387))
      | ~ r1_tarski(k2_tarski(A_386,B_387),B_385) ) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_245])).

tff(c_1354,plain,(
    ! [B_390,A_391] :
      ( r1_tarski(k1_setfam_1(B_390),A_391)
      | ~ r1_tarski(k2_tarski(A_391,A_391),B_390) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1330])).

tff(c_1376,plain,(
    ! [C_392,B_393] :
      ( r1_tarski(k1_setfam_1(C_392),B_393)
      | ~ r2_hidden(B_393,C_392) ) ),
    inference(resolution,[status(thm)],[c_28,c_1354])).

tff(c_1478,plain,(
    ! [A_418,B_419,B_420] :
      ( r1_tarski(k3_xboole_0(A_418,B_419),B_420)
      | ~ r2_hidden(B_420,k2_tarski(A_418,B_419)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1376])).

tff(c_1487,plain,(
    ! [A_93,B_91] : r1_tarski(k3_xboole_0(A_93,B_91),B_91) ),
    inference(resolution,[status(thm)],[c_151,c_1478])).

tff(c_92,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_166,plain,(
    ! [B_108,A_109] :
      ( v1_relat_1(B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_109))
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_171,plain,(
    ! [A_110,B_111] :
      ( v1_relat_1(A_110)
      | ~ v1_relat_1(B_111)
      | ~ r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_80,c_166])).

tff(c_182,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_90,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_94,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_859,plain,(
    ! [C_301,A_302,B_303] :
      ( r1_tarski(k5_relat_1(C_301,A_302),k5_relat_1(C_301,B_303))
      | ~ r1_tarski(A_302,B_303)
      | ~ v1_relat_1(C_301)
      | ~ v1_relat_1(B_303)
      | ~ v1_relat_1(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_597,plain,(
    ! [C_228,A_229,B_230] :
      ( r1_tarski(k5_relat_1(C_228,A_229),k5_relat_1(C_228,B_230))
      | ~ r1_tarski(A_229,B_230)
      | ~ v1_relat_1(C_228)
      | ~ v1_relat_1(B_230)
      | ~ v1_relat_1(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_281,plain,(
    ! [A_145,B_146,C_147] :
      ( r1_tarski(A_145,k3_xboole_0(B_146,C_147))
      | ~ r1_tarski(A_145,C_147)
      | ~ r1_tarski(A_145,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_307,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_281,c_88])).

tff(c_359,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_600,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_597,c_359])).

tff(c_606,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94,c_8,c_600])).

tff(c_610,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_606])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_610])).

tff(c_615,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_862,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_859,c_615])).

tff(c_868,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_94,c_862])).

tff(c_870,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_873,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_870])).

tff(c_877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_873])).

tff(c_878,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_1500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.68  
% 3.96/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.96/1.68  
% 3.96/1.68  %Foreground sorts:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Background operators:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Foreground operators:
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.96/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.96/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.96/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.96/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.96/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.96/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.96/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.96/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.96/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.96/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.96/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.96/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.96/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.96/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.96/1.68  
% 3.96/1.70  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.96/1.70  tff(f_32, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.96/1.70  tff(f_72, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.96/1.70  tff(f_103, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.96/1.70  tff(f_40, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.96/1.70  tff(f_50, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.96/1.70  tff(f_48, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.96/1.70  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.96/1.70  tff(f_58, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.96/1.70  tff(f_80, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 3.96/1.70  tff(f_113, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.96/1.70  tff(f_143, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.96/1.70  tff(f_107, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.96/1.70  tff(f_120, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.96/1.70  tff(f_132, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 3.96/1.70  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.96/1.70  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.96/1.70  tff(c_106, plain, (![A_72, B_73]: (r1_tarski(k3_xboole_0(A_72, B_73), A_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.96/1.70  tff(c_109, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_106])).
% 3.96/1.70  tff(c_146, plain, (![B_91, C_92, A_93]: (r2_hidden(B_91, C_92) | ~r1_tarski(k2_tarski(A_93, B_91), C_92))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.70  tff(c_151, plain, (![B_91, A_93]: (r2_hidden(B_91, k2_tarski(A_93, B_91)))), inference(resolution, [status(thm)], [c_109, c_146])).
% 3.96/1.70  tff(c_76, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.96/1.70  tff(c_28, plain, (![A_32, B_33, C_34]: (r1_tarski(k2_tarski(A_32, B_33), C_34) | ~r2_hidden(B_33, C_34) | ~r2_hidden(A_32, C_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.70  tff(c_153, plain, (![A_96, C_97, B_98]: (r2_hidden(A_96, C_97) | ~r1_tarski(k2_tarski(A_96, B_98), C_97))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.70  tff(c_158, plain, (![A_96, B_98]: (r2_hidden(A_96, k2_tarski(A_96, B_98)))), inference(resolution, [status(thm)], [c_109, c_153])).
% 3.96/1.70  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.96/1.70  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.96/1.70  tff(c_160, plain, (![B_101, A_102]: (~r1_xboole_0(B_101, A_102) | ~r1_tarski(B_101, A_102) | v1_xboole_0(B_101))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.96/1.70  tff(c_222, plain, (![A_137, B_138]: (~r1_tarski(k4_xboole_0(A_137, B_138), B_138) | v1_xboole_0(k4_xboole_0(A_137, B_138)))), inference(resolution, [status(thm)], [c_16, c_160])).
% 3.96/1.70  tff(c_228, plain, (![A_139]: (v1_xboole_0(k4_xboole_0(A_139, A_139)))), inference(resolution, [status(thm)], [c_12, c_222])).
% 3.96/1.70  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.96/1.70  tff(c_111, plain, (![B_75, A_76]: (~v1_xboole_0(B_75) | B_75=A_76 | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.96/1.70  tff(c_114, plain, (![A_76]: (k1_xboole_0=A_76 | ~v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_2, c_111])).
% 3.96/1.70  tff(c_234, plain, (![A_139]: (k4_xboole_0(A_139, A_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_228, c_114])).
% 3.96/1.70  tff(c_326, plain, (![A_149, C_150, B_151]: (~r2_hidden(A_149, C_150) | k4_xboole_0(k2_tarski(A_149, B_151), C_150)!=k2_tarski(A_149, B_151))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.96/1.70  tff(c_330, plain, (![A_149, B_151]: (~r2_hidden(A_149, k2_tarski(A_149, B_151)) | k2_tarski(A_149, B_151)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_234, c_326])).
% 3.96/1.70  tff(c_332, plain, (![A_149, B_151]: (k2_tarski(A_149, B_151)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_330])).
% 3.96/1.70  tff(c_236, plain, (![B_140, A_141]: (r1_tarski(k1_setfam_1(B_140), k1_setfam_1(A_141)) | k1_xboole_0=A_141 | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.96/1.70  tff(c_245, plain, (![B_140, A_47, B_48]: (r1_tarski(k1_setfam_1(B_140), k3_xboole_0(A_47, B_48)) | k2_tarski(A_47, B_48)=k1_xboole_0 | ~r1_tarski(k2_tarski(A_47, B_48), B_140))), inference(superposition, [status(thm), theory('equality')], [c_76, c_236])).
% 3.96/1.70  tff(c_1330, plain, (![B_385, A_386, B_387]: (r1_tarski(k1_setfam_1(B_385), k3_xboole_0(A_386, B_387)) | ~r1_tarski(k2_tarski(A_386, B_387), B_385))), inference(negUnitSimplification, [status(thm)], [c_332, c_245])).
% 3.96/1.70  tff(c_1354, plain, (![B_390, A_391]: (r1_tarski(k1_setfam_1(B_390), A_391) | ~r1_tarski(k2_tarski(A_391, A_391), B_390))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1330])).
% 3.96/1.70  tff(c_1376, plain, (![C_392, B_393]: (r1_tarski(k1_setfam_1(C_392), B_393) | ~r2_hidden(B_393, C_392))), inference(resolution, [status(thm)], [c_28, c_1354])).
% 3.96/1.70  tff(c_1478, plain, (![A_418, B_419, B_420]: (r1_tarski(k3_xboole_0(A_418, B_419), B_420) | ~r2_hidden(B_420, k2_tarski(A_418, B_419)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_1376])).
% 3.96/1.70  tff(c_1487, plain, (![A_93, B_91]: (r1_tarski(k3_xboole_0(A_93, B_91), B_91))), inference(resolution, [status(thm)], [c_151, c_1478])).
% 3.96/1.70  tff(c_92, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.70  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.96/1.70  tff(c_80, plain, (![A_49, B_50]: (m1_subset_1(A_49, k1_zfmisc_1(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.96/1.70  tff(c_166, plain, (![B_108, A_109]: (v1_relat_1(B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(A_109)) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.96/1.70  tff(c_171, plain, (![A_110, B_111]: (v1_relat_1(A_110) | ~v1_relat_1(B_111) | ~r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_80, c_166])).
% 3.96/1.70  tff(c_182, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_8, c_171])).
% 3.96/1.70  tff(c_90, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.70  tff(c_94, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.70  tff(c_859, plain, (![C_301, A_302, B_303]: (r1_tarski(k5_relat_1(C_301, A_302), k5_relat_1(C_301, B_303)) | ~r1_tarski(A_302, B_303) | ~v1_relat_1(C_301) | ~v1_relat_1(B_303) | ~v1_relat_1(A_302))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.96/1.70  tff(c_597, plain, (![C_228, A_229, B_230]: (r1_tarski(k5_relat_1(C_228, A_229), k5_relat_1(C_228, B_230)) | ~r1_tarski(A_229, B_230) | ~v1_relat_1(C_228) | ~v1_relat_1(B_230) | ~v1_relat_1(A_229))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.96/1.70  tff(c_281, plain, (![A_145, B_146, C_147]: (r1_tarski(A_145, k3_xboole_0(B_146, C_147)) | ~r1_tarski(A_145, C_147) | ~r1_tarski(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.96/1.70  tff(c_88, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.96/1.70  tff(c_307, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_281, c_88])).
% 3.96/1.70  tff(c_359, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_307])).
% 3.96/1.70  tff(c_600, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_597, c_359])).
% 3.96/1.70  tff(c_606, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_94, c_8, c_600])).
% 3.96/1.70  tff(c_610, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_182, c_606])).
% 3.96/1.70  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_610])).
% 3.96/1.70  tff(c_615, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_307])).
% 3.96/1.70  tff(c_862, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_859, c_615])).
% 3.96/1.70  tff(c_868, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_94, c_862])).
% 3.96/1.70  tff(c_870, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_868])).
% 3.96/1.70  tff(c_873, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_182, c_870])).
% 3.96/1.70  tff(c_877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_873])).
% 3.96/1.70  tff(c_878, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_868])).
% 3.96/1.70  tff(c_1500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1487, c_878])).
% 3.96/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.70  
% 3.96/1.70  Inference rules
% 3.96/1.70  ----------------------
% 3.96/1.70  #Ref     : 0
% 3.96/1.70  #Sup     : 327
% 3.96/1.70  #Fact    : 0
% 3.96/1.70  #Define  : 0
% 3.96/1.70  #Split   : 5
% 3.96/1.70  #Chain   : 0
% 3.96/1.70  #Close   : 0
% 3.96/1.70  
% 3.96/1.70  Ordering : KBO
% 3.96/1.70  
% 3.96/1.70  Simplification rules
% 3.96/1.70  ----------------------
% 3.96/1.70  #Subsume      : 49
% 3.96/1.70  #Demod        : 86
% 3.96/1.70  #Tautology    : 90
% 3.96/1.70  #SimpNegUnit  : 24
% 3.96/1.70  #BackRed      : 6
% 3.96/1.70  
% 3.96/1.70  #Partial instantiations: 0
% 3.96/1.70  #Strategies tried      : 1
% 3.96/1.70  
% 3.96/1.70  Timing (in seconds)
% 3.96/1.70  ----------------------
% 3.96/1.70  Preprocessing        : 0.37
% 3.96/1.70  Parsing              : 0.19
% 3.96/1.70  CNF conversion       : 0.03
% 3.96/1.70  Main loop            : 0.56
% 3.96/1.70  Inferencing          : 0.19
% 3.96/1.70  Reduction            : 0.17
% 3.96/1.70  Demodulation         : 0.12
% 3.96/1.70  BG Simplification    : 0.03
% 3.96/1.70  Subsumption          : 0.13
% 3.96/1.70  Abstraction          : 0.03
% 3.96/1.70  MUC search           : 0.00
% 3.96/1.70  Cooper               : 0.00
% 3.96/1.71  Total                : 0.96
% 3.96/1.71  Index Insertion      : 0.00
% 3.96/1.71  Index Deletion       : 0.00
% 3.96/1.71  Index Matching       : 0.00
% 3.96/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
