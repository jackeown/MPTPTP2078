%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:31 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 247 expanded)
%              Number of leaves         :   39 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 232 expanded)
%              Number of equality atoms :   69 ( 213 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_314,plain,(
    ! [A_82,B_83] : r1_xboole_0(k3_xboole_0(A_82,B_83),k5_xboole_0(A_82,B_83)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_335,plain,(
    ! [A_14] : r1_xboole_0(k1_xboole_0,k5_xboole_0(A_14,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_314])).

tff(c_344,plain,(
    ! [A_14] : r1_xboole_0(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_335])).

tff(c_116,plain,(
    ! [B_74,A_75] : k3_xboole_0(B_74,A_75) = k3_xboole_0(A_75,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [A_75] : k3_xboole_0(k1_xboole_0,A_75) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_14])).

tff(c_547,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | ~ r2_hidden(C_104,k3_xboole_0(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_553,plain,(
    ! [A_75,C_104] :
      ( ~ r1_xboole_0(k1_xboole_0,A_75)
      | ~ r2_hidden(C_104,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_547])).

tff(c_564,plain,(
    ! [C_104] : ~ r2_hidden(C_104,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_553])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_381,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_404,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_381])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_651,plain,(
    ! [A_114,B_115,C_116] : k5_xboole_0(k5_xboole_0(A_114,B_115),C_116) = k5_xboole_0(A_114,k5_xboole_0(B_115,C_116)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5921,plain,(
    ! [A_14343,B_14344,C_14345] : k5_xboole_0(k5_xboole_0(A_14343,B_14344),C_14345) = k5_xboole_0(B_14344,k5_xboole_0(A_14343,C_14345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_651])).

tff(c_997,plain,(
    ! [A_123,B_124] : k5_xboole_0(k5_xboole_0(A_123,B_124),k3_xboole_0(A_123,B_124)) = k2_xboole_0(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1082,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),k3_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_997])).

tff(c_5934,plain,(
    ! [B_14344,A_14343] : k5_xboole_0(B_14344,k5_xboole_0(A_14343,k3_xboole_0(B_14344,A_14343))) = k2_xboole_0(A_14343,B_14344) ),
    inference(superposition,[status(thm),theory(equality)],[c_5921,c_1082])).

tff(c_6323,plain,(
    ! [B_14678,A_14679] : k5_xboole_0(B_14678,k4_xboole_0(A_14679,B_14678)) = k2_xboole_0(A_14679,B_14678) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_5934])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] : k5_xboole_0(k5_xboole_0(A_18,B_19),C_20) = k5_xboole_0(A_18,k5_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5722,plain,(
    ! [B_14176,A_14177] : k5_xboole_0(k5_xboole_0(B_14176,A_14177),k3_xboole_0(A_14177,B_14176)) = k2_xboole_0(B_14176,A_14177) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_997])).

tff(c_5842,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k5_xboole_0(B_19,k3_xboole_0(B_19,A_18))) = k2_xboole_0(A_18,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5722])).

tff(c_5902,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5842])).

tff(c_6613,plain,(
    ! [B_15012,A_15013] : k2_xboole_0(B_15012,A_15013) = k2_xboole_0(A_15013,B_15012) ),
    inference(superposition,[status(thm),theory(equality)],[c_6323,c_5902])).

tff(c_66,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6668,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6613,c_66])).

tff(c_1085,plain,(
    ! [A_14] : k5_xboole_0(k5_xboole_0(A_14,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_997])).

tff(c_1101,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_1085])).

tff(c_6180,plain,(
    ! [A_14511,B_14512] : k5_xboole_0(A_14511,k4_xboole_0(B_14512,A_14511)) = k2_xboole_0(A_14511,B_14512) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5842])).

tff(c_163,plain,(
    ! [B_76,A_77] : k5_xboole_0(B_76,A_77) = k5_xboole_0(A_77,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_201,plain,(
    ! [A_17] : k5_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_163])).

tff(c_22,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_721,plain,(
    ! [A_21,C_116] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_116)) = k5_xboole_0(k1_xboole_0,C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_651])).

tff(c_735,plain,(
    ! [A_117,C_118] : k5_xboole_0(A_117,k5_xboole_0(A_117,C_118)) = C_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_721])).

tff(c_784,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_735])).

tff(c_7086,plain,(
    ! [B_15678,A_15679] : k5_xboole_0(k4_xboole_0(B_15678,A_15679),k2_xboole_0(A_15679,B_15678)) = A_15679 ),
    inference(superposition,[status(thm),theory(equality)],[c_6180,c_784])).

tff(c_7152,plain,(
    k5_xboole_0(k4_xboole_0(k1_tarski('#skF_4'),'#skF_5'),k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6668,c_7086])).

tff(c_1076,plain,(
    ! [A_123,B_124] : k5_xboole_0(k3_xboole_0(A_123,B_124),k5_xboole_0(A_123,B_124)) = k2_xboole_0(A_123,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_997])).

tff(c_7254,plain,(
    k5_xboole_0(k3_xboole_0(k4_xboole_0(k1_tarski('#skF_4'),'#skF_5'),k1_xboole_0),'#skF_5') = k2_xboole_0(k4_xboole_0(k1_tarski('#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7152,c_1076])).

tff(c_7329,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_18,c_4,c_14,c_7254])).

tff(c_807,plain,(
    ! [A_119,B_120] : k5_xboole_0(A_119,k5_xboole_0(B_120,A_119)) = B_120 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_735])).

tff(c_860,plain,(
    ! [A_12,B_13] : k5_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_807])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2430,plain,(
    ! [A_3619,B_3620] : k5_xboole_0(A_3619,k3_xboole_0(B_3620,A_3619)) = k4_xboole_0(A_3619,B_3620) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_381])).

tff(c_734,plain,(
    ! [A_21,C_116] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_116)) = C_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_721])).

tff(c_2535,plain,(
    ! [A_3676,B_3677] : k5_xboole_0(A_3676,k4_xboole_0(A_3676,B_3677)) = k3_xboole_0(B_3677,A_3676) ),
    inference(superposition,[status(thm),theory(equality)],[c_2430,c_734])).

tff(c_2603,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(k4_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2535])).

tff(c_2623,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2,c_2603])).

tff(c_894,plain,(
    ! [B_121,A_122] : k5_xboole_0(k5_xboole_0(B_121,A_122),B_121) = A_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_784])).

tff(c_5121,plain,(
    ! [A_12673,B_12674] : k5_xboole_0(k4_xboole_0(A_12673,B_12674),A_12673) = k3_xboole_0(A_12673,B_12674) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_894])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5148,plain,(
    ! [A_12673,B_12674] : k5_xboole_0(k3_xboole_0(A_12673,B_12674),k3_xboole_0(k4_xboole_0(A_12673,B_12674),A_12673)) = k2_xboole_0(k4_xboole_0(A_12673,B_12674),A_12673) ),
    inference(superposition,[status(thm),theory(equality)],[c_5121,c_24])).

tff(c_5224,plain,(
    ! [A_12673,B_12674] : k2_xboole_0(k4_xboole_0(A_12673,B_12674),A_12673) = A_12673 ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_2623,c_2,c_5148])).

tff(c_7379,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7329,c_5224])).

tff(c_7416,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6668,c_7379])).

tff(c_50,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_293,plain,(
    ! [A_80,B_81] : k1_enumset1(A_80,A_80,B_81) = k2_tarski(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [E_30,B_25,C_26] : r2_hidden(E_30,k1_enumset1(E_30,B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_350,plain,(
    ! [A_85,B_86] : r2_hidden(A_85,k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_32])).

tff(c_353,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_350])).

tff(c_7435,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7416,c_353])).

tff(c_7439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_7435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:02:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.72/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.92/2.41  
% 6.92/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.92/2.41  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.92/2.41  
% 6.92/2.41  %Foreground sorts:
% 6.92/2.41  
% 6.92/2.41  
% 6.92/2.41  %Background operators:
% 6.92/2.41  
% 6.92/2.41  
% 6.92/2.41  %Foreground operators:
% 6.92/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.92/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.92/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.92/2.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.92/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.92/2.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.92/2.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.92/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.92/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.92/2.41  tff('#skF_5', type, '#skF_5': $i).
% 6.92/2.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.92/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.92/2.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.92/2.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.92/2.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.92/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.92/2.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.92/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.92/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.92/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.92/2.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.92/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.92/2.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.92/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.92/2.41  
% 6.92/2.43  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.92/2.43  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.92/2.43  tff(f_45, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.92/2.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.92/2.43  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.92/2.43  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.92/2.43  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.92/2.43  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.92/2.43  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.92/2.43  tff(f_94, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.92/2.43  tff(f_57, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.92/2.43  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.92/2.43  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.92/2.43  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.92/2.43  tff(f_74, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.92/2.43  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.92/2.43  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.92/2.43  tff(c_314, plain, (![A_82, B_83]: (r1_xboole_0(k3_xboole_0(A_82, B_83), k5_xboole_0(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.92/2.43  tff(c_335, plain, (![A_14]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(A_14, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_314])).
% 6.92/2.43  tff(c_344, plain, (![A_14]: (r1_xboole_0(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_335])).
% 6.92/2.43  tff(c_116, plain, (![B_74, A_75]: (k3_xboole_0(B_74, A_75)=k3_xboole_0(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.92/2.43  tff(c_132, plain, (![A_75]: (k3_xboole_0(k1_xboole_0, A_75)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_14])).
% 6.92/2.43  tff(c_547, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | ~r2_hidden(C_104, k3_xboole_0(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.92/2.43  tff(c_553, plain, (![A_75, C_104]: (~r1_xboole_0(k1_xboole_0, A_75) | ~r2_hidden(C_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_132, c_547])).
% 6.92/2.43  tff(c_564, plain, (![C_104]: (~r2_hidden(C_104, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_553])).
% 6.92/2.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.92/2.43  tff(c_381, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.92/2.43  tff(c_404, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_381])).
% 6.92/2.43  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.92/2.43  tff(c_651, plain, (![A_114, B_115, C_116]: (k5_xboole_0(k5_xboole_0(A_114, B_115), C_116)=k5_xboole_0(A_114, k5_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.92/2.43  tff(c_5921, plain, (![A_14343, B_14344, C_14345]: (k5_xboole_0(k5_xboole_0(A_14343, B_14344), C_14345)=k5_xboole_0(B_14344, k5_xboole_0(A_14343, C_14345)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_651])).
% 6.92/2.43  tff(c_997, plain, (![A_123, B_124]: (k5_xboole_0(k5_xboole_0(A_123, B_124), k3_xboole_0(A_123, B_124))=k2_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.92/2.43  tff(c_1082, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), k3_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_997])).
% 6.92/2.43  tff(c_5934, plain, (![B_14344, A_14343]: (k5_xboole_0(B_14344, k5_xboole_0(A_14343, k3_xboole_0(B_14344, A_14343)))=k2_xboole_0(A_14343, B_14344))), inference(superposition, [status(thm), theory('equality')], [c_5921, c_1082])).
% 6.92/2.43  tff(c_6323, plain, (![B_14678, A_14679]: (k5_xboole_0(B_14678, k4_xboole_0(A_14679, B_14678))=k2_xboole_0(A_14679, B_14678))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_5934])).
% 6.92/2.43  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.92/2.43  tff(c_20, plain, (![A_18, B_19, C_20]: (k5_xboole_0(k5_xboole_0(A_18, B_19), C_20)=k5_xboole_0(A_18, k5_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.92/2.43  tff(c_5722, plain, (![B_14176, A_14177]: (k5_xboole_0(k5_xboole_0(B_14176, A_14177), k3_xboole_0(A_14177, B_14176))=k2_xboole_0(B_14176, A_14177))), inference(superposition, [status(thm), theory('equality')], [c_2, c_997])).
% 6.92/2.43  tff(c_5842, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k5_xboole_0(B_19, k3_xboole_0(B_19, A_18)))=k2_xboole_0(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5722])).
% 6.92/2.43  tff(c_5902, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5842])).
% 6.92/2.43  tff(c_6613, plain, (![B_15012, A_15013]: (k2_xboole_0(B_15012, A_15013)=k2_xboole_0(A_15013, B_15012))), inference(superposition, [status(thm), theory('equality')], [c_6323, c_5902])).
% 6.92/2.43  tff(c_66, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.92/2.43  tff(c_6668, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6613, c_66])).
% 6.92/2.43  tff(c_1085, plain, (![A_14]: (k5_xboole_0(k5_xboole_0(A_14, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_997])).
% 6.92/2.43  tff(c_1101, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_1085])).
% 6.92/2.43  tff(c_6180, plain, (![A_14511, B_14512]: (k5_xboole_0(A_14511, k4_xboole_0(B_14512, A_14511))=k2_xboole_0(A_14511, B_14512))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5842])).
% 6.92/2.43  tff(c_163, plain, (![B_76, A_77]: (k5_xboole_0(B_76, A_77)=k5_xboole_0(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.92/2.43  tff(c_201, plain, (![A_17]: (k5_xboole_0(k1_xboole_0, A_17)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_18, c_163])).
% 6.92/2.43  tff(c_22, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.92/2.43  tff(c_721, plain, (![A_21, C_116]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_116))=k5_xboole_0(k1_xboole_0, C_116))), inference(superposition, [status(thm), theory('equality')], [c_22, c_651])).
% 6.92/2.43  tff(c_735, plain, (![A_117, C_118]: (k5_xboole_0(A_117, k5_xboole_0(A_117, C_118))=C_118)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_721])).
% 6.92/2.43  tff(c_784, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_735])).
% 6.92/2.43  tff(c_7086, plain, (![B_15678, A_15679]: (k5_xboole_0(k4_xboole_0(B_15678, A_15679), k2_xboole_0(A_15679, B_15678))=A_15679)), inference(superposition, [status(thm), theory('equality')], [c_6180, c_784])).
% 6.92/2.43  tff(c_7152, plain, (k5_xboole_0(k4_xboole_0(k1_tarski('#skF_4'), '#skF_5'), k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6668, c_7086])).
% 6.92/2.43  tff(c_1076, plain, (![A_123, B_124]: (k5_xboole_0(k3_xboole_0(A_123, B_124), k5_xboole_0(A_123, B_124))=k2_xboole_0(A_123, B_124))), inference(superposition, [status(thm), theory('equality')], [c_4, c_997])).
% 6.92/2.43  tff(c_7254, plain, (k5_xboole_0(k3_xboole_0(k4_xboole_0(k1_tarski('#skF_4'), '#skF_5'), k1_xboole_0), '#skF_5')=k2_xboole_0(k4_xboole_0(k1_tarski('#skF_4'), '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7152, c_1076])).
% 6.92/2.43  tff(c_7329, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_18, c_4, c_14, c_7254])).
% 6.92/2.43  tff(c_807, plain, (![A_119, B_120]: (k5_xboole_0(A_119, k5_xboole_0(B_120, A_119))=B_120)), inference(superposition, [status(thm), theory('equality')], [c_4, c_735])).
% 6.92/2.43  tff(c_860, plain, (![A_12, B_13]: (k5_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(superposition, [status(thm), theory('equality')], [c_12, c_807])).
% 6.92/2.43  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.92/2.43  tff(c_2430, plain, (![A_3619, B_3620]: (k5_xboole_0(A_3619, k3_xboole_0(B_3620, A_3619))=k4_xboole_0(A_3619, B_3620))), inference(superposition, [status(thm), theory('equality')], [c_2, c_381])).
% 6.92/2.43  tff(c_734, plain, (![A_21, C_116]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_116))=C_116)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_721])).
% 6.92/2.43  tff(c_2535, plain, (![A_3676, B_3677]: (k5_xboole_0(A_3676, k4_xboole_0(A_3676, B_3677))=k3_xboole_0(B_3677, A_3676))), inference(superposition, [status(thm), theory('equality')], [c_2430, c_734])).
% 6.92/2.43  tff(c_2603, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(k4_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2535])).
% 6.92/2.43  tff(c_2623, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2, c_2603])).
% 6.92/2.43  tff(c_894, plain, (![B_121, A_122]: (k5_xboole_0(k5_xboole_0(B_121, A_122), B_121)=A_122)), inference(superposition, [status(thm), theory('equality')], [c_807, c_784])).
% 6.92/2.43  tff(c_5121, plain, (![A_12673, B_12674]: (k5_xboole_0(k4_xboole_0(A_12673, B_12674), A_12673)=k3_xboole_0(A_12673, B_12674))), inference(superposition, [status(thm), theory('equality')], [c_12, c_894])).
% 6.92/2.43  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.92/2.43  tff(c_5148, plain, (![A_12673, B_12674]: (k5_xboole_0(k3_xboole_0(A_12673, B_12674), k3_xboole_0(k4_xboole_0(A_12673, B_12674), A_12673))=k2_xboole_0(k4_xboole_0(A_12673, B_12674), A_12673))), inference(superposition, [status(thm), theory('equality')], [c_5121, c_24])).
% 6.92/2.43  tff(c_5224, plain, (![A_12673, B_12674]: (k2_xboole_0(k4_xboole_0(A_12673, B_12674), A_12673)=A_12673)), inference(demodulation, [status(thm), theory('equality')], [c_860, c_2623, c_2, c_5148])).
% 6.92/2.43  tff(c_7379, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7329, c_5224])).
% 6.92/2.43  tff(c_7416, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6668, c_7379])).
% 6.92/2.43  tff(c_50, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.92/2.43  tff(c_293, plain, (![A_80, B_81]: (k1_enumset1(A_80, A_80, B_81)=k2_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.92/2.43  tff(c_32, plain, (![E_30, B_25, C_26]: (r2_hidden(E_30, k1_enumset1(E_30, B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.92/2.43  tff(c_350, plain, (![A_85, B_86]: (r2_hidden(A_85, k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_293, c_32])).
% 6.92/2.43  tff(c_353, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_350])).
% 6.92/2.43  tff(c_7435, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7416, c_353])).
% 6.92/2.43  tff(c_7439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_564, c_7435])).
% 6.92/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.92/2.43  
% 6.92/2.43  Inference rules
% 6.92/2.43  ----------------------
% 6.92/2.43  #Ref     : 0
% 6.92/2.43  #Sup     : 1416
% 6.92/2.43  #Fact    : 18
% 6.92/2.43  #Define  : 0
% 6.92/2.43  #Split   : 0
% 6.92/2.43  #Chain   : 0
% 6.92/2.43  #Close   : 0
% 6.92/2.43  
% 6.92/2.43  Ordering : KBO
% 6.92/2.43  
% 6.92/2.43  Simplification rules
% 6.92/2.43  ----------------------
% 6.92/2.43  #Subsume      : 91
% 6.92/2.43  #Demod        : 1045
% 6.92/2.43  #Tautology    : 747
% 6.92/2.43  #SimpNegUnit  : 12
% 6.92/2.43  #BackRed      : 6
% 6.92/2.43  
% 6.92/2.43  #Partial instantiations: 5529
% 6.92/2.43  #Strategies tried      : 1
% 6.92/2.43  
% 6.92/2.43  Timing (in seconds)
% 6.92/2.43  ----------------------
% 6.92/2.43  Preprocessing        : 0.36
% 6.92/2.43  Parsing              : 0.19
% 6.92/2.43  CNF conversion       : 0.03
% 6.92/2.43  Main loop            : 1.29
% 6.92/2.43  Inferencing          : 0.58
% 6.92/2.43  Reduction            : 0.46
% 6.92/2.43  Demodulation         : 0.38
% 6.92/2.43  BG Simplification    : 0.05
% 6.92/2.43  Subsumption          : 0.15
% 6.92/2.43  Abstraction          : 0.06
% 6.92/2.43  MUC search           : 0.00
% 6.92/2.43  Cooper               : 0.00
% 6.92/2.43  Total                : 1.69
% 6.92/2.43  Index Insertion      : 0.00
% 6.92/2.43  Index Deletion       : 0.00
% 6.92/2.43  Index Matching       : 0.00
% 6.92/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
