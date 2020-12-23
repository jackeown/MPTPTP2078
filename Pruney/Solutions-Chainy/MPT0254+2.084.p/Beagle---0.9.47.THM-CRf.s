%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:30 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  120 (1566 expanded)
%              Number of leaves         :   47 ( 549 expanded)
%              Depth                    :   16
%              Number of atoms          :  119 (1648 expanded)
%              Number of equality atoms :   75 (1435 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_96,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_98,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_97,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_70,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    ! [B_78,A_79] : k5_xboole_0(B_78,A_79) = k5_xboole_0(A_79,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_159,plain,(
    ! [A_79] : k5_xboole_0(k1_xboole_0,A_79) = A_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_28])).

tff(c_34,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_991,plain,(
    ! [A_135,B_136,C_137] : k5_xboole_0(k5_xboole_0(A_135,B_136),C_137) = k5_xboole_0(A_135,k5_xboole_0(B_136,C_137)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1079,plain,(
    ! [A_28,C_137] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_137)) = k5_xboole_0(k1_xboole_0,C_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_991])).

tff(c_1095,plain,(
    ! [A_138,C_139] : k5_xboole_0(A_138,k5_xboole_0(A_138,C_139)) = C_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_1079])).

tff(c_1169,plain,(
    ! [A_140,B_141] : k5_xboole_0(A_140,k5_xboole_0(B_141,A_140)) = B_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1095])).

tff(c_1147,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1095])).

tff(c_1172,plain,(
    ! [B_141,A_140] : k5_xboole_0(k5_xboole_0(B_141,A_140),B_141) = A_140 ),
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_1147])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_478,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_500,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_478])).

tff(c_36,plain,(
    ! [A_29,B_30] : k5_xboole_0(k5_xboole_0(A_29,B_30),k3_xboole_0(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1038,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k5_xboole_0(B_30,k3_xboole_0(A_29,B_30))) = k2_xboole_0(A_29,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_991])).

tff(c_1725,plain,(
    ! [A_163,B_164] : k5_xboole_0(A_163,k4_xboole_0(B_164,A_163)) = k2_xboole_0(A_163,B_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_1038])).

tff(c_1094,plain,(
    ! [A_28,C_137] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_137)) = C_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_1079])).

tff(c_2195,plain,(
    ! [A_187,B_188] : k5_xboole_0(A_187,k2_xboole_0(A_187,B_188)) = k4_xboole_0(B_188,A_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_1725,c_1094])).

tff(c_2253,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2195])).

tff(c_2267,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2253])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2284,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2267,c_26])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2296,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_2284,c_22])).

tff(c_2420,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski('#skF_4'),'#skF_5'),k1_tarski('#skF_4')) = k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2296,c_36])).

tff(c_2459,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1172,c_2420])).

tff(c_24,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_129,plain,(
    ! [A_74,B_75] : r1_tarski(k3_xboole_0(A_74,B_75),A_74) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_132,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_129])).

tff(c_2488,plain,(
    ! [A_20] : r1_tarski('#skF_5',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_132])).

tff(c_385,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = A_93
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_405,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),A_21) = k4_xboole_0(A_21,B_22) ),
    inference(resolution,[status(thm)],[c_26,c_385])).

tff(c_2281,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2267,c_405])).

tff(c_2288,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_2,c_2281])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_459,plain,(
    ! [B_100,A_101] :
      ( B_100 = A_101
      | ~ r1_tarski(B_100,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2548,plain,(
    ! [A_200,B_201] :
      ( k3_xboole_0(A_200,B_201) = A_200
      | ~ r1_tarski(A_200,k3_xboole_0(A_200,B_201)) ) ),
    inference(resolution,[status(thm)],[c_20,c_459])).

tff(c_2558,plain,
    ( k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2288,c_2548])).

tff(c_2581,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_2288,c_2558])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_354,plain,(
    ! [A_88,B_89] : k3_tarski(k2_tarski(A_88,B_89)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_363,plain,(
    ! [A_31] : k3_tarski(k1_tarski(A_31)) = k2_xboole_0(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_354])).

tff(c_366,plain,(
    ! [A_31] : k3_tarski(k1_tarski(A_31)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_363])).

tff(c_2603,plain,(
    k3_tarski('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2581,c_366])).

tff(c_68,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2495,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_2459,c_68])).

tff(c_2628,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_2495])).

tff(c_2635,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2628,c_2581])).

tff(c_237,plain,(
    ! [B_81,A_82] : k3_xboole_0(B_81,A_82) = k3_xboole_0(A_82,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_252,plain,(
    ! [B_81,A_82] : r1_tarski(k3_xboole_0(B_81,A_82),A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_20])).

tff(c_30,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_578,plain,(
    ! [A_107,B_108,C_109] :
      ( ~ r1_xboole_0(A_107,B_108)
      | ~ r2_hidden(C_109,k3_xboole_0(A_107,B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_593,plain,(
    ! [A_20,C_109] :
      ( ~ r1_xboole_0(A_20,k1_xboole_0)
      | ~ r2_hidden(C_109,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_578])).

tff(c_595,plain,(
    ! [C_109] : ~ r2_hidden(C_109,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_593])).

tff(c_66,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1950,plain,(
    ! [A_173,B_174] :
      ( r1_tarski('#skF_2'(A_173,B_174),A_173)
      | r2_hidden('#skF_3'(A_173,B_174),B_174)
      | k1_zfmisc_1(A_173) = B_174 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2117,plain,(
    ! [A_179] :
      ( r1_tarski('#skF_2'(A_179,k1_xboole_0),A_179)
      | k1_zfmisc_1(A_179) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1950,c_595])).

tff(c_471,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_132,c_459])).

tff(c_2121,plain,
    ( '#skF_2'(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2117,c_471])).

tff(c_2128,plain,
    ( '#skF_2'(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2121])).

tff(c_2132,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2128])).

tff(c_377,plain,(
    ! [C_91,A_92] :
      ( r2_hidden(C_91,k1_zfmisc_1(A_92))
      | ~ r1_tarski(C_91,A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_383,plain,(
    ! [C_91] :
      ( r2_hidden(C_91,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_91,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_377])).

tff(c_2133,plain,(
    ! [C_91] :
      ( r2_hidden(C_91,k1_xboole_0)
      | ~ r1_tarski(C_91,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2132,c_383])).

tff(c_2145,plain,(
    ! [C_180] : ~ r1_tarski(C_180,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_2133])).

tff(c_2169,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_252,c_2145])).

tff(c_2171,plain,(
    k1_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2128])).

tff(c_2471,plain,(
    k1_tarski('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_2459,c_2171])).

tff(c_2640,plain,(
    k1_tarski('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2628,c_2628,c_2471])).

tff(c_2671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2635,c_2640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.70  
% 3.99/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.99/1.70  
% 3.99/1.70  %Foreground sorts:
% 3.99/1.70  
% 3.99/1.70  
% 3.99/1.70  %Background operators:
% 3.99/1.70  
% 3.99/1.70  
% 3.99/1.70  %Foreground operators:
% 3.99/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.99/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.99/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.99/1.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.99/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.99/1.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.99/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.99/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.99/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.99/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.99/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.99/1.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.99/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.99/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.99/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.99/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.99/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.99/1.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.99/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.99/1.70  
% 3.99/1.71  tff(f_102, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.99/1.71  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.99/1.71  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.99/1.71  tff(f_71, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.99/1.71  tff(f_69, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.99/1.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.99/1.71  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.99/1.71  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.99/1.71  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.99/1.71  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.99/1.71  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.99/1.71  tff(f_55, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.99/1.71  tff(f_51, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.99/1.71  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.99/1.71  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.99/1.71  tff(f_96, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.99/1.71  tff(f_98, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 3.99/1.71  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.99/1.71  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.99/1.71  tff(f_97, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.99/1.71  tff(f_94, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.99/1.71  tff(c_70, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.99/1.71  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.71  tff(c_143, plain, (![B_78, A_79]: (k5_xboole_0(B_78, A_79)=k5_xboole_0(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.71  tff(c_28, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.99/1.71  tff(c_159, plain, (![A_79]: (k5_xboole_0(k1_xboole_0, A_79)=A_79)), inference(superposition, [status(thm), theory('equality')], [c_143, c_28])).
% 3.99/1.71  tff(c_34, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.99/1.71  tff(c_991, plain, (![A_135, B_136, C_137]: (k5_xboole_0(k5_xboole_0(A_135, B_136), C_137)=k5_xboole_0(A_135, k5_xboole_0(B_136, C_137)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.99/1.71  tff(c_1079, plain, (![A_28, C_137]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_137))=k5_xboole_0(k1_xboole_0, C_137))), inference(superposition, [status(thm), theory('equality')], [c_34, c_991])).
% 3.99/1.71  tff(c_1095, plain, (![A_138, C_139]: (k5_xboole_0(A_138, k5_xboole_0(A_138, C_139))=C_139)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_1079])).
% 3.99/1.71  tff(c_1169, plain, (![A_140, B_141]: (k5_xboole_0(A_140, k5_xboole_0(B_141, A_140))=B_141)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1095])).
% 3.99/1.71  tff(c_1147, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1095])).
% 3.99/1.71  tff(c_1172, plain, (![B_141, A_140]: (k5_xboole_0(k5_xboole_0(B_141, A_140), B_141)=A_140)), inference(superposition, [status(thm), theory('equality')], [c_1169, c_1147])).
% 3.99/1.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.71  tff(c_478, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.99/1.71  tff(c_500, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_478])).
% 3.99/1.71  tff(c_36, plain, (![A_29, B_30]: (k5_xboole_0(k5_xboole_0(A_29, B_30), k3_xboole_0(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.99/1.71  tff(c_1038, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k5_xboole_0(B_30, k3_xboole_0(A_29, B_30)))=k2_xboole_0(A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_36, c_991])).
% 3.99/1.71  tff(c_1725, plain, (![A_163, B_164]: (k5_xboole_0(A_163, k4_xboole_0(B_164, A_163))=k2_xboole_0(A_163, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_500, c_1038])).
% 3.99/1.71  tff(c_1094, plain, (![A_28, C_137]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_137))=C_137)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_1079])).
% 3.99/1.71  tff(c_2195, plain, (![A_187, B_188]: (k5_xboole_0(A_187, k2_xboole_0(A_187, B_188))=k4_xboole_0(B_188, A_187))), inference(superposition, [status(thm), theory('equality')], [c_1725, c_1094])).
% 3.99/1.71  tff(c_2253, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2195])).
% 3.99/1.71  tff(c_2267, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2253])).
% 3.99/1.71  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.99/1.71  tff(c_2284, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2267, c_26])).
% 3.99/1.71  tff(c_22, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.99/1.71  tff(c_2296, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_2284, c_22])).
% 3.99/1.71  tff(c_2420, plain, (k5_xboole_0(k5_xboole_0(k1_tarski('#skF_4'), '#skF_5'), k1_tarski('#skF_4'))=k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2296, c_36])).
% 3.99/1.71  tff(c_2459, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1172, c_2420])).
% 3.99/1.71  tff(c_24, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.99/1.71  tff(c_129, plain, (![A_74, B_75]: (r1_tarski(k3_xboole_0(A_74, B_75), A_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.71  tff(c_132, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(superposition, [status(thm), theory('equality')], [c_24, c_129])).
% 3.99/1.71  tff(c_2488, plain, (![A_20]: (r1_tarski('#skF_5', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_132])).
% 3.99/1.71  tff(c_385, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=A_93 | ~r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.99/1.71  tff(c_405, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), A_21)=k4_xboole_0(A_21, B_22))), inference(resolution, [status(thm)], [c_26, c_385])).
% 3.99/1.71  tff(c_2281, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2267, c_405])).
% 3.99/1.71  tff(c_2288, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2267, c_2, c_2281])).
% 3.99/1.71  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.71  tff(c_459, plain, (![B_100, A_101]: (B_100=A_101 | ~r1_tarski(B_100, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.99/1.71  tff(c_2548, plain, (![A_200, B_201]: (k3_xboole_0(A_200, B_201)=A_200 | ~r1_tarski(A_200, k3_xboole_0(A_200, B_201)))), inference(resolution, [status(thm)], [c_20, c_459])).
% 3.99/1.71  tff(c_2558, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5' | ~r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2288, c_2548])).
% 3.99/1.71  tff(c_2581, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_2288, c_2558])).
% 3.99/1.71  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.71  tff(c_38, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.99/1.71  tff(c_354, plain, (![A_88, B_89]: (k3_tarski(k2_tarski(A_88, B_89))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.99/1.71  tff(c_363, plain, (![A_31]: (k3_tarski(k1_tarski(A_31))=k2_xboole_0(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_38, c_354])).
% 3.99/1.71  tff(c_366, plain, (![A_31]: (k3_tarski(k1_tarski(A_31))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_363])).
% 3.99/1.71  tff(c_2603, plain, (k3_tarski('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2581, c_366])).
% 3.99/1.71  tff(c_68, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.99/1.71  tff(c_2495, plain, (k3_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_2459, c_68])).
% 3.99/1.71  tff(c_2628, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2603, c_2495])).
% 3.99/1.71  tff(c_2635, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2628, c_2581])).
% 3.99/1.71  tff(c_237, plain, (![B_81, A_82]: (k3_xboole_0(B_81, A_82)=k3_xboole_0(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.71  tff(c_252, plain, (![B_81, A_82]: (r1_tarski(k3_xboole_0(B_81, A_82), A_82))), inference(superposition, [status(thm), theory('equality')], [c_237, c_20])).
% 3.99/1.71  tff(c_30, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.99/1.71  tff(c_578, plain, (![A_107, B_108, C_109]: (~r1_xboole_0(A_107, B_108) | ~r2_hidden(C_109, k3_xboole_0(A_107, B_108)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.99/1.71  tff(c_593, plain, (![A_20, C_109]: (~r1_xboole_0(A_20, k1_xboole_0) | ~r2_hidden(C_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_578])).
% 3.99/1.71  tff(c_595, plain, (![C_109]: (~r2_hidden(C_109, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_593])).
% 3.99/1.71  tff(c_66, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.99/1.71  tff(c_1950, plain, (![A_173, B_174]: (r1_tarski('#skF_2'(A_173, B_174), A_173) | r2_hidden('#skF_3'(A_173, B_174), B_174) | k1_zfmisc_1(A_173)=B_174)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.99/1.71  tff(c_2117, plain, (![A_179]: (r1_tarski('#skF_2'(A_179, k1_xboole_0), A_179) | k1_zfmisc_1(A_179)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1950, c_595])).
% 3.99/1.71  tff(c_471, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_132, c_459])).
% 3.99/1.71  tff(c_2121, plain, ('#skF_2'(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2117, c_471])).
% 3.99/1.71  tff(c_2128, plain, ('#skF_2'(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k1_tarski(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2121])).
% 3.99/1.71  tff(c_2132, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2128])).
% 3.99/1.71  tff(c_377, plain, (![C_91, A_92]: (r2_hidden(C_91, k1_zfmisc_1(A_92)) | ~r1_tarski(C_91, A_92))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.99/1.71  tff(c_383, plain, (![C_91]: (r2_hidden(C_91, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_377])).
% 3.99/1.72  tff(c_2133, plain, (![C_91]: (r2_hidden(C_91, k1_xboole_0) | ~r1_tarski(C_91, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2132, c_383])).
% 3.99/1.72  tff(c_2145, plain, (![C_180]: (~r1_tarski(C_180, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_595, c_2133])).
% 3.99/1.72  tff(c_2169, plain, $false, inference(resolution, [status(thm)], [c_252, c_2145])).
% 3.99/1.72  tff(c_2171, plain, (k1_tarski(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2128])).
% 3.99/1.72  tff(c_2471, plain, (k1_tarski('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_2459, c_2171])).
% 3.99/1.72  tff(c_2640, plain, (k1_tarski('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2628, c_2628, c_2471])).
% 3.99/1.72  tff(c_2671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2635, c_2640])).
% 3.99/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.72  
% 3.99/1.72  Inference rules
% 3.99/1.72  ----------------------
% 3.99/1.72  #Ref     : 0
% 3.99/1.72  #Sup     : 635
% 3.99/1.72  #Fact    : 0
% 3.99/1.72  #Define  : 0
% 3.99/1.72  #Split   : 1
% 3.99/1.72  #Chain   : 0
% 3.99/1.72  #Close   : 0
% 3.99/1.72  
% 3.99/1.72  Ordering : KBO
% 3.99/1.72  
% 3.99/1.72  Simplification rules
% 3.99/1.72  ----------------------
% 3.99/1.72  #Subsume      : 24
% 3.99/1.72  #Demod        : 455
% 3.99/1.72  #Tautology    : 432
% 3.99/1.72  #SimpNegUnit  : 5
% 3.99/1.72  #BackRed      : 46
% 3.99/1.72  
% 3.99/1.72  #Partial instantiations: 0
% 3.99/1.72  #Strategies tried      : 1
% 3.99/1.72  
% 3.99/1.72  Timing (in seconds)
% 3.99/1.72  ----------------------
% 3.99/1.72  Preprocessing        : 0.33
% 3.99/1.72  Parsing              : 0.17
% 3.99/1.72  CNF conversion       : 0.02
% 3.99/1.72  Main loop            : 0.58
% 3.99/1.72  Inferencing          : 0.19
% 3.99/1.72  Reduction            : 0.23
% 3.99/1.72  Demodulation         : 0.19
% 3.99/1.72  BG Simplification    : 0.03
% 3.99/1.72  Subsumption          : 0.08
% 3.99/1.72  Abstraction          : 0.03
% 3.99/1.72  MUC search           : 0.00
% 3.99/1.72  Cooper               : 0.00
% 3.99/1.72  Total                : 0.95
% 3.99/1.72  Index Insertion      : 0.00
% 3.99/1.72  Index Deletion       : 0.00
% 3.99/1.72  Index Matching       : 0.00
% 3.99/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
