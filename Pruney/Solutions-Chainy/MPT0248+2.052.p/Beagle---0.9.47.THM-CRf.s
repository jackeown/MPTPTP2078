%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:11 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 148 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 271 expanded)
%              Number of equality atoms :   78 ( 251 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_48,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_89,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_90,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_85,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_85])).

tff(c_463,plain,(
    ! [B_85,A_86] :
      ( k1_tarski(B_85) = A_86
      | k1_xboole_0 = A_86
      | ~ r1_tarski(A_86,k1_tarski(B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_473,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_88,c_463])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_90,c_473])).

tff(c_485,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_486,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_615,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_486,c_50])).

tff(c_20,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_488,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_792,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_808,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_792])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k5_xboole_0(k5_xboole_0(A_13,B_14),C_15) = k5_xboole_0(A_13,k5_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1201,plain,(
    ! [A_128,B_129] : k5_xboole_0(k5_xboole_0(A_128,B_129),k3_xboole_0(A_128,B_129)) = k2_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1238,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k5_xboole_0(B_14,k3_xboole_0(A_13,B_14))) = k2_xboole_0(A_13,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1201])).

tff(c_1749,plain,(
    ! [A_162,B_163] : k5_xboole_0(A_162,k4_xboole_0(B_163,A_162)) = k2_xboole_0(A_162,B_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_1238])).

tff(c_519,plain,(
    ! [B_89,A_90] : k5_xboole_0(B_89,A_90) = k5_xboole_0(A_90,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_535,plain,(
    ! [A_90] : k5_xboole_0(k1_xboole_0,A_90) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_14])).

tff(c_1044,plain,(
    ! [A_123,B_124,C_125] : k5_xboole_0(k5_xboole_0(A_123,B_124),C_125) = k5_xboole_0(A_123,k5_xboole_0(B_124,C_125)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1119,plain,(
    ! [A_16,C_125] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_125)) = k5_xboole_0(k1_xboole_0,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1044])).

tff(c_1132,plain,(
    ! [A_16,C_125] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_125)) = C_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_1119])).

tff(c_2470,plain,(
    ! [A_180,B_181] : k5_xboole_0(A_180,k2_xboole_0(A_180,B_181)) = k4_xboole_0(B_181,A_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_1132])).

tff(c_2528,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_2470])).

tff(c_2540,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2528])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_985,plain,(
    ! [B_119,A_120] :
      ( k1_tarski(B_119) = A_120
      | k1_xboole_0 = A_120
      | ~ r1_tarski(A_120,k1_tarski(B_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_995,plain,(
    ! [A_120] :
      ( k1_tarski('#skF_1') = A_120
      | k1_xboole_0 = A_120
      | ~ r1_tarski(A_120,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_985])).

tff(c_1006,plain,(
    ! [A_121] :
      ( A_121 = '#skF_2'
      | k1_xboole_0 = A_121
      | ~ r1_tarski(A_121,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_995])).

tff(c_1018,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | k1_xboole_0 = A_5
      | k4_xboole_0(A_5,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1006])).

tff(c_2553,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2540,c_1018])).

tff(c_2562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_485,c_615,c_2553])).

tff(c_2563,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2564,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2565,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_2') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2564,c_14])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2567,plain,(
    ! [A_9] : r1_tarski('#skF_2',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2564,c_12])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2791,plain,(
    ! [A_200,B_201] :
      ( k4_xboole_0(A_200,B_201) = '#skF_2'
      | ~ r1_tarski(A_200,B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2564,c_8])).

tff(c_2810,plain,(
    ! [A_9] : k4_xboole_0('#skF_2',A_9) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2567,c_2791])).

tff(c_2812,plain,(
    ! [A_202,B_203] : k5_xboole_0(A_202,k3_xboole_0(A_202,B_203)) = k4_xboole_0(A_202,B_203) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2645,plain,(
    ! [B_189,A_190] : k5_xboole_0(B_189,A_190) = k5_xboole_0(A_190,B_189) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2661,plain,(
    ! [A_190] : k5_xboole_0('#skF_2',A_190) = A_190 ),
    inference(superposition,[status(thm),theory(equality)],[c_2645,c_2565])).

tff(c_2819,plain,(
    ! [B_203] : k4_xboole_0('#skF_2',B_203) = k3_xboole_0('#skF_2',B_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_2812,c_2661])).

tff(c_2889,plain,(
    ! [B_203] : k3_xboole_0('#skF_2',B_203) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2810,c_2819])).

tff(c_3003,plain,(
    ! [A_217,B_218] : k5_xboole_0(k5_xboole_0(A_217,B_218),k3_xboole_0(A_217,B_218)) = k2_xboole_0(A_217,B_218) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3033,plain,(
    ! [A_190] : k5_xboole_0(A_190,k3_xboole_0('#skF_2',A_190)) = k2_xboole_0('#skF_2',A_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_3003])).

tff(c_3064,plain,(
    ! [A_190] : k2_xboole_0('#skF_2',A_190) = A_190 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_2889,c_3033])).

tff(c_3066,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3064,c_52])).

tff(c_3068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2563,c_3066])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n012.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 15:03:22 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.63  
% 3.83/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.63  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.83/1.63  
% 3.83/1.63  %Foreground sorts:
% 3.83/1.63  
% 3.83/1.63  
% 3.83/1.63  %Background operators:
% 3.83/1.63  
% 3.83/1.63  
% 3.83/1.63  %Foreground operators:
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.83/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.83/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.83/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.83/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.83/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.83/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.83/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.83/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/1.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.63  
% 3.83/1.65  tff(f_88, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.83/1.65  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.83/1.65  tff(f_67, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.83/1.65  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.83/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.83/1.65  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.83/1.65  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.83/1.65  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.83/1.65  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.83/1.65  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.83/1.65  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.83/1.65  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.83/1.65  tff(c_48, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.83/1.65  tff(c_89, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 3.83/1.65  tff(c_46, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.83/1.65  tff(c_90, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_46])).
% 3.83/1.65  tff(c_52, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.83/1.65  tff(c_85, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.83/1.65  tff(c_88, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_85])).
% 3.83/1.65  tff(c_463, plain, (![B_85, A_86]: (k1_tarski(B_85)=A_86 | k1_xboole_0=A_86 | ~r1_tarski(A_86, k1_tarski(B_85)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.83/1.65  tff(c_473, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_88, c_463])).
% 3.83/1.65  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_90, c_473])).
% 3.83/1.65  tff(c_485, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 3.83/1.65  tff(c_486, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_46])).
% 3.83/1.65  tff(c_50, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.83/1.65  tff(c_615, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_486, c_50])).
% 3.83/1.65  tff(c_20, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.83/1.65  tff(c_488, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_52])).
% 3.83/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.83/1.65  tff(c_792, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.83/1.65  tff(c_808, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_792])).
% 3.83/1.65  tff(c_18, plain, (![A_13, B_14, C_15]: (k5_xboole_0(k5_xboole_0(A_13, B_14), C_15)=k5_xboole_0(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.83/1.65  tff(c_1201, plain, (![A_128, B_129]: (k5_xboole_0(k5_xboole_0(A_128, B_129), k3_xboole_0(A_128, B_129))=k2_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.83/1.65  tff(c_1238, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k5_xboole_0(B_14, k3_xboole_0(A_13, B_14)))=k2_xboole_0(A_13, B_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1201])).
% 3.83/1.65  tff(c_1749, plain, (![A_162, B_163]: (k5_xboole_0(A_162, k4_xboole_0(B_163, A_162))=k2_xboole_0(A_162, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_1238])).
% 3.83/1.65  tff(c_519, plain, (![B_89, A_90]: (k5_xboole_0(B_89, A_90)=k5_xboole_0(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.83/1.65  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.83/1.65  tff(c_535, plain, (![A_90]: (k5_xboole_0(k1_xboole_0, A_90)=A_90)), inference(superposition, [status(thm), theory('equality')], [c_519, c_14])).
% 3.83/1.65  tff(c_1044, plain, (![A_123, B_124, C_125]: (k5_xboole_0(k5_xboole_0(A_123, B_124), C_125)=k5_xboole_0(A_123, k5_xboole_0(B_124, C_125)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.83/1.65  tff(c_1119, plain, (![A_16, C_125]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_125))=k5_xboole_0(k1_xboole_0, C_125))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1044])).
% 3.83/1.65  tff(c_1132, plain, (![A_16, C_125]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_125))=C_125)), inference(demodulation, [status(thm), theory('equality')], [c_535, c_1119])).
% 3.83/1.65  tff(c_2470, plain, (![A_180, B_181]: (k5_xboole_0(A_180, k2_xboole_0(A_180, B_181))=k4_xboole_0(B_181, A_180))), inference(superposition, [status(thm), theory('equality')], [c_1749, c_1132])).
% 3.83/1.65  tff(c_2528, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_488, c_2470])).
% 3.83/1.65  tff(c_2540, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2528])).
% 3.83/1.65  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.83/1.65  tff(c_985, plain, (![B_119, A_120]: (k1_tarski(B_119)=A_120 | k1_xboole_0=A_120 | ~r1_tarski(A_120, k1_tarski(B_119)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.83/1.65  tff(c_995, plain, (![A_120]: (k1_tarski('#skF_1')=A_120 | k1_xboole_0=A_120 | ~r1_tarski(A_120, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_486, c_985])).
% 3.83/1.65  tff(c_1006, plain, (![A_121]: (A_121='#skF_2' | k1_xboole_0=A_121 | ~r1_tarski(A_121, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_995])).
% 3.83/1.65  tff(c_1018, plain, (![A_5]: (A_5='#skF_2' | k1_xboole_0=A_5 | k4_xboole_0(A_5, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1006])).
% 3.83/1.65  tff(c_2553, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2540, c_1018])).
% 3.83/1.65  tff(c_2562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_485, c_615, c_2553])).
% 3.83/1.65  tff(c_2563, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 3.83/1.65  tff(c_2564, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 3.83/1.65  tff(c_2565, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_2')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_2564, c_14])).
% 3.83/1.65  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.83/1.65  tff(c_2567, plain, (![A_9]: (r1_tarski('#skF_2', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_2564, c_12])).
% 3.83/1.65  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.83/1.65  tff(c_2791, plain, (![A_200, B_201]: (k4_xboole_0(A_200, B_201)='#skF_2' | ~r1_tarski(A_200, B_201))), inference(demodulation, [status(thm), theory('equality')], [c_2564, c_8])).
% 3.83/1.65  tff(c_2810, plain, (![A_9]: (k4_xboole_0('#skF_2', A_9)='#skF_2')), inference(resolution, [status(thm)], [c_2567, c_2791])).
% 3.83/1.65  tff(c_2812, plain, (![A_202, B_203]: (k5_xboole_0(A_202, k3_xboole_0(A_202, B_203))=k4_xboole_0(A_202, B_203))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.83/1.65  tff(c_2645, plain, (![B_189, A_190]: (k5_xboole_0(B_189, A_190)=k5_xboole_0(A_190, B_189))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.83/1.65  tff(c_2661, plain, (![A_190]: (k5_xboole_0('#skF_2', A_190)=A_190)), inference(superposition, [status(thm), theory('equality')], [c_2645, c_2565])).
% 3.83/1.65  tff(c_2819, plain, (![B_203]: (k4_xboole_0('#skF_2', B_203)=k3_xboole_0('#skF_2', B_203))), inference(superposition, [status(thm), theory('equality')], [c_2812, c_2661])).
% 3.83/1.65  tff(c_2889, plain, (![B_203]: (k3_xboole_0('#skF_2', B_203)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2810, c_2819])).
% 3.83/1.65  tff(c_3003, plain, (![A_217, B_218]: (k5_xboole_0(k5_xboole_0(A_217, B_218), k3_xboole_0(A_217, B_218))=k2_xboole_0(A_217, B_218))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.83/1.65  tff(c_3033, plain, (![A_190]: (k5_xboole_0(A_190, k3_xboole_0('#skF_2', A_190))=k2_xboole_0('#skF_2', A_190))), inference(superposition, [status(thm), theory('equality')], [c_2661, c_3003])).
% 3.83/1.65  tff(c_3064, plain, (![A_190]: (k2_xboole_0('#skF_2', A_190)=A_190)), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_2889, c_3033])).
% 3.83/1.65  tff(c_3066, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3064, c_52])).
% 3.83/1.65  tff(c_3068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2563, c_3066])).
% 3.83/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.65  
% 3.83/1.65  Inference rules
% 3.83/1.65  ----------------------
% 3.83/1.65  #Ref     : 0
% 3.83/1.65  #Sup     : 727
% 3.83/1.65  #Fact    : 0
% 3.83/1.65  #Define  : 0
% 3.83/1.65  #Split   : 4
% 3.83/1.65  #Chain   : 0
% 3.83/1.65  #Close   : 0
% 3.83/1.65  
% 3.83/1.65  Ordering : KBO
% 3.83/1.65  
% 3.83/1.65  Simplification rules
% 3.83/1.65  ----------------------
% 3.83/1.65  #Subsume      : 8
% 3.83/1.65  #Demod        : 405
% 3.83/1.65  #Tautology    : 530
% 3.83/1.65  #SimpNegUnit  : 9
% 3.83/1.65  #BackRed      : 13
% 3.83/1.65  
% 3.83/1.65  #Partial instantiations: 0
% 3.83/1.65  #Strategies tried      : 1
% 3.83/1.65  
% 3.83/1.65  Timing (in seconds)
% 3.83/1.65  ----------------------
% 3.83/1.65  Preprocessing        : 0.35
% 3.83/1.65  Parsing              : 0.19
% 3.83/1.65  CNF conversion       : 0.02
% 3.83/1.65  Main loop            : 0.59
% 3.83/1.65  Inferencing          : 0.20
% 3.83/1.65  Reduction            : 0.24
% 3.83/1.65  Demodulation         : 0.19
% 3.83/1.65  BG Simplification    : 0.03
% 3.83/1.65  Subsumption          : 0.08
% 3.83/1.65  Abstraction          : 0.03
% 3.83/1.65  MUC search           : 0.00
% 3.83/1.65  Cooper               : 0.00
% 3.83/1.65  Total                : 0.97
% 3.83/1.65  Index Insertion      : 0.00
% 3.83/1.65  Index Deletion       : 0.00
% 3.83/1.65  Index Matching       : 0.00
% 3.83/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
