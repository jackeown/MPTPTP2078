%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:06 EST 2020

% Result     : Theorem 6.37s
% Output     : CNFRefutation 6.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 705 expanded)
%              Number of leaves         :   23 ( 249 expanded)
%              Depth                    :   22
%              Number of atoms          :   65 ( 692 expanded)
%              Number of equality atoms :   64 ( 691 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k2_xboole_0(A_26,B_27)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_138,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k4_xboole_0(B_34,A_33)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_147,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_138])).

tff(c_153,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k1_tarski(A_19),k2_tarski(B_20,C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [A_31,B_32] : k2_xboole_0(k1_tarski(A_31),k1_tarski(B_32)) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [A_31,B_32] : k4_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_178,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_16,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_193,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_214,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_193])).

tff(c_220,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k3_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_193])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_232,plain,(
    ! [A_42] : k5_xboole_0(A_42,k4_xboole_0(A_42,k1_xboole_0)) = k4_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_6])).

tff(c_314,plain,(
    ! [A_46] : k5_xboole_0(A_46,k4_xboole_0(A_46,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_232])).

tff(c_336,plain,(
    ! [A_3] : k5_xboole_0(A_3,k3_xboole_0(A_3,A_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_314])).

tff(c_217,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_193])).

tff(c_253,plain,(
    ! [A_43,B_44,C_45] : k5_xboole_0(k5_xboole_0(A_43,B_44),C_45) = k5_xboole_0(A_43,k5_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1128,plain,(
    ! [A_82,B_83,C_84] : k5_xboole_0(A_82,k5_xboole_0(k3_xboole_0(A_82,B_83),C_84)) = k5_xboole_0(k4_xboole_0(A_82,B_83),C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_253])).

tff(c_1175,plain,(
    ! [A_8,B_9,C_84] : k5_xboole_0(k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)),C_84) = k5_xboole_0(A_8,k5_xboole_0(k4_xboole_0(A_8,k1_xboole_0),C_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_1128])).

tff(c_1230,plain,(
    ! [A_85,C_86] : k5_xboole_0(A_85,k5_xboole_0(k4_xboole_0(A_85,k1_xboole_0),C_86)) = k5_xboole_0(k1_xboole_0,C_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1175])).

tff(c_1291,plain,(
    ! [A_85] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(A_85,k1_xboole_0),k4_xboole_0(A_85,k1_xboole_0))) = k5_xboole_0(A_85,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_1230])).

tff(c_1335,plain,(
    ! [A_87] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_87,k1_xboole_0)) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_214,c_153,c_1291])).

tff(c_1350,plain,(
    ! [A_87] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_1335,c_217])).

tff(c_1583,plain,(
    ! [A_90] : k3_xboole_0(k1_xboole_0,A_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1350])).

tff(c_1616,plain,(
    ! [A_90] : k5_xboole_0(A_90,k1_xboole_0) = k4_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_190])).

tff(c_1652,plain,(
    ! [A_90] : k4_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_1616])).

tff(c_251,plain,(
    ! [A_42] : k5_xboole_0(A_42,k4_xboole_0(A_42,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_232])).

tff(c_1955,plain,(
    ! [A_97] : k5_xboole_0(A_97,A_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1652,c_251])).

tff(c_280,plain,(
    ! [A_5,B_6,C_45] : k5_xboole_0(A_5,k5_xboole_0(k3_xboole_0(A_5,B_6),C_45)) = k5_xboole_0(k4_xboole_0(A_5,B_6),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_253])).

tff(c_1969,plain,(
    ! [A_5,B_6] : k5_xboole_0(k4_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1955,c_280])).

tff(c_3348,plain,(
    ! [A_127,B_128] : k5_xboole_0(k4_xboole_0(A_127,B_128),k3_xboole_0(A_127,B_128)) = A_127 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_1969])).

tff(c_1331,plain,(
    ! [A_85] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_85,k1_xboole_0)) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_214,c_153,c_1291])).

tff(c_514,plain,(
    ! [A_60,C_61] : k5_xboole_0(A_60,k5_xboole_0(k1_xboole_0,C_61)) = k5_xboole_0(A_60,C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_253])).

tff(c_922,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,k1_xboole_0)) = k5_xboole_0(A_76,k2_xboole_0(k1_xboole_0,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_514])).

tff(c_944,plain,(
    ! [B_77] : k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,B_77)) = k2_xboole_0(k1_xboole_0,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_16])).

tff(c_1341,plain,(
    ! [A_87] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_87,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_1335,c_944])).

tff(c_1365,plain,(
    ! [A_87] : k5_xboole_0(k1_xboole_0,A_87) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1331,c_1341])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1972,plain,(
    ! [A_97,C_14] : k5_xboole_0(A_97,k5_xboole_0(A_97,C_14)) = k5_xboole_0(k1_xboole_0,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_1955,c_14])).

tff(c_1999,plain,(
    ! [A_97,C_14] : k5_xboole_0(A_97,k5_xboole_0(A_97,C_14)) = C_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_1972])).

tff(c_5457,plain,(
    ! [A_168,B_169] : k5_xboole_0(k4_xboole_0(A_168,B_169),A_168) = k3_xboole_0(A_168,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_3348,c_1999])).

tff(c_294,plain,(
    ! [A_15,B_16,C_45] : k5_xboole_0(A_15,k5_xboole_0(k4_xboole_0(B_16,A_15),C_45)) = k5_xboole_0(k2_xboole_0(A_15,B_16),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_253])).

tff(c_5490,plain,(
    ! [B_169,A_168] : k5_xboole_0(k2_xboole_0(B_169,A_168),A_168) = k5_xboole_0(B_169,k3_xboole_0(A_168,B_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5457,c_294])).

tff(c_5769,plain,(
    ! [B_174,A_175] : k5_xboole_0(k2_xboole_0(B_174,A_175),A_175) = k4_xboole_0(B_174,A_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_5490])).

tff(c_11121,plain,(
    ! [B_237,A_238] : k5_xboole_0(k2_xboole_0(B_237,A_238),k4_xboole_0(B_237,A_238)) = A_238 ),
    inference(superposition,[status(thm),theory(equality)],[c_5769,c_1999])).

tff(c_11246,plain,(
    ! [A_31,B_32] : k5_xboole_0(k2_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)),k1_xboole_0) = k2_tarski(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_11121])).

tff(c_11295,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_20,c_11246])).

tff(c_24,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11295,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.37/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.46  
% 6.37/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.47  %$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.37/2.47  
% 6.37/2.47  %Foreground sorts:
% 6.37/2.47  
% 6.37/2.47  
% 6.37/2.47  %Background operators:
% 6.37/2.47  
% 6.37/2.47  
% 6.37/2.47  %Foreground operators:
% 6.37/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.37/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.37/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.37/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.37/2.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.37/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.37/2.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.37/2.47  tff('#skF_2', type, '#skF_2': $i).
% 6.37/2.47  tff('#skF_1', type, '#skF_1': $i).
% 6.37/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.37/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.37/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.37/2.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.37/2.47  
% 6.37/2.48  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.37/2.48  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.37/2.48  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.37/2.48  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 6.37/2.48  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 6.37/2.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.37/2.48  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.37/2.48  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.37/2.48  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.37/2.48  tff(f_50, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.37/2.48  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.37/2.48  tff(c_62, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k2_xboole_0(A_26, B_27))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.37/2.48  tff(c_69, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 6.37/2.48  tff(c_138, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k4_xboole_0(B_34, A_33))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.37/2.48  tff(c_147, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_69, c_138])).
% 6.37/2.48  tff(c_153, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_147])).
% 6.37/2.48  tff(c_20, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k1_tarski(A_19), k2_tarski(B_20, C_21))=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.37/2.48  tff(c_116, plain, (![A_31, B_32]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(B_32))=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.37/2.48  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.37/2.48  tff(c_122, plain, (![A_31, B_32]: (k4_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_10])).
% 6.37/2.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.37/2.48  tff(c_178, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.37/2.48  tff(c_190, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 6.37/2.48  tff(c_16, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.37/2.48  tff(c_193, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.37/2.48  tff(c_214, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_69, c_193])).
% 6.37/2.48  tff(c_220, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k3_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_69, c_193])).
% 6.37/2.48  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.37/2.48  tff(c_232, plain, (![A_42]: (k5_xboole_0(A_42, k4_xboole_0(A_42, k1_xboole_0))=k4_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_220, c_6])).
% 6.37/2.48  tff(c_314, plain, (![A_46]: (k5_xboole_0(A_46, k4_xboole_0(A_46, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_232])).
% 6.37/2.48  tff(c_336, plain, (![A_3]: (k5_xboole_0(A_3, k3_xboole_0(A_3, A_3))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_214, c_314])).
% 6.37/2.48  tff(c_217, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_193])).
% 6.37/2.48  tff(c_253, plain, (![A_43, B_44, C_45]: (k5_xboole_0(k5_xboole_0(A_43, B_44), C_45)=k5_xboole_0(A_43, k5_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.37/2.48  tff(c_1128, plain, (![A_82, B_83, C_84]: (k5_xboole_0(A_82, k5_xboole_0(k3_xboole_0(A_82, B_83), C_84))=k5_xboole_0(k4_xboole_0(A_82, B_83), C_84))), inference(superposition, [status(thm), theory('equality')], [c_6, c_253])).
% 6.37/2.48  tff(c_1175, plain, (![A_8, B_9, C_84]: (k5_xboole_0(k4_xboole_0(A_8, k2_xboole_0(A_8, B_9)), C_84)=k5_xboole_0(A_8, k5_xboole_0(k4_xboole_0(A_8, k1_xboole_0), C_84)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_1128])).
% 6.37/2.48  tff(c_1230, plain, (![A_85, C_86]: (k5_xboole_0(A_85, k5_xboole_0(k4_xboole_0(A_85, k1_xboole_0), C_86))=k5_xboole_0(k1_xboole_0, C_86))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1175])).
% 6.37/2.48  tff(c_1291, plain, (![A_85]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(k4_xboole_0(A_85, k1_xboole_0), k4_xboole_0(A_85, k1_xboole_0)))=k5_xboole_0(A_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_336, c_1230])).
% 6.37/2.48  tff(c_1335, plain, (![A_87]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_87, k1_xboole_0))=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_214, c_153, c_1291])).
% 6.37/2.48  tff(c_1350, plain, (![A_87]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, A_87))), inference(superposition, [status(thm), theory('equality')], [c_1335, c_217])).
% 6.37/2.48  tff(c_1583, plain, (![A_90]: (k3_xboole_0(k1_xboole_0, A_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1350])).
% 6.37/2.48  tff(c_1616, plain, (![A_90]: (k5_xboole_0(A_90, k1_xboole_0)=k4_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1583, c_190])).
% 6.37/2.48  tff(c_1652, plain, (![A_90]: (k4_xboole_0(A_90, k1_xboole_0)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_1616])).
% 6.37/2.48  tff(c_251, plain, (![A_42]: (k5_xboole_0(A_42, k4_xboole_0(A_42, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_232])).
% 6.37/2.48  tff(c_1955, plain, (![A_97]: (k5_xboole_0(A_97, A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1652, c_251])).
% 6.37/2.48  tff(c_280, plain, (![A_5, B_6, C_45]: (k5_xboole_0(A_5, k5_xboole_0(k3_xboole_0(A_5, B_6), C_45))=k5_xboole_0(k4_xboole_0(A_5, B_6), C_45))), inference(superposition, [status(thm), theory('equality')], [c_6, c_253])).
% 6.37/2.48  tff(c_1969, plain, (![A_5, B_6]: (k5_xboole_0(k4_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k5_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1955, c_280])).
% 6.37/2.48  tff(c_3348, plain, (![A_127, B_128]: (k5_xboole_0(k4_xboole_0(A_127, B_128), k3_xboole_0(A_127, B_128))=A_127)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_1969])).
% 6.37/2.48  tff(c_1331, plain, (![A_85]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_85, k1_xboole_0))=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_214, c_153, c_1291])).
% 6.37/2.48  tff(c_514, plain, (![A_60, C_61]: (k5_xboole_0(A_60, k5_xboole_0(k1_xboole_0, C_61))=k5_xboole_0(A_60, C_61))), inference(superposition, [status(thm), theory('equality')], [c_153, c_253])).
% 6.37/2.48  tff(c_922, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, k1_xboole_0))=k5_xboole_0(A_76, k2_xboole_0(k1_xboole_0, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_514])).
% 6.37/2.48  tff(c_944, plain, (![B_77]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(k1_xboole_0, B_77))=k2_xboole_0(k1_xboole_0, B_77))), inference(superposition, [status(thm), theory('equality')], [c_922, c_16])).
% 6.37/2.48  tff(c_1341, plain, (![A_87]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_87, k1_xboole_0))=k5_xboole_0(k1_xboole_0, A_87))), inference(superposition, [status(thm), theory('equality')], [c_1335, c_944])).
% 6.37/2.48  tff(c_1365, plain, (![A_87]: (k5_xboole_0(k1_xboole_0, A_87)=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_1331, c_1341])).
% 6.37/2.48  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.37/2.48  tff(c_1972, plain, (![A_97, C_14]: (k5_xboole_0(A_97, k5_xboole_0(A_97, C_14))=k5_xboole_0(k1_xboole_0, C_14))), inference(superposition, [status(thm), theory('equality')], [c_1955, c_14])).
% 6.37/2.48  tff(c_1999, plain, (![A_97, C_14]: (k5_xboole_0(A_97, k5_xboole_0(A_97, C_14))=C_14)), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_1972])).
% 6.37/2.48  tff(c_5457, plain, (![A_168, B_169]: (k5_xboole_0(k4_xboole_0(A_168, B_169), A_168)=k3_xboole_0(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_3348, c_1999])).
% 6.37/2.48  tff(c_294, plain, (![A_15, B_16, C_45]: (k5_xboole_0(A_15, k5_xboole_0(k4_xboole_0(B_16, A_15), C_45))=k5_xboole_0(k2_xboole_0(A_15, B_16), C_45))), inference(superposition, [status(thm), theory('equality')], [c_16, c_253])).
% 6.37/2.48  tff(c_5490, plain, (![B_169, A_168]: (k5_xboole_0(k2_xboole_0(B_169, A_168), A_168)=k5_xboole_0(B_169, k3_xboole_0(A_168, B_169)))), inference(superposition, [status(thm), theory('equality')], [c_5457, c_294])).
% 6.37/2.48  tff(c_5769, plain, (![B_174, A_175]: (k5_xboole_0(k2_xboole_0(B_174, A_175), A_175)=k4_xboole_0(B_174, A_175))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_5490])).
% 6.37/2.48  tff(c_11121, plain, (![B_237, A_238]: (k5_xboole_0(k2_xboole_0(B_237, A_238), k4_xboole_0(B_237, A_238))=A_238)), inference(superposition, [status(thm), theory('equality')], [c_5769, c_1999])).
% 6.37/2.48  tff(c_11246, plain, (![A_31, B_32]: (k5_xboole_0(k2_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32)), k1_xboole_0)=k2_tarski(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_122, c_11121])).
% 6.37/2.48  tff(c_11295, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_20, c_11246])).
% 6.37/2.48  tff(c_24, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.37/2.48  tff(c_11302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11295, c_24])).
% 6.37/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.37/2.48  
% 6.37/2.48  Inference rules
% 6.37/2.48  ----------------------
% 6.37/2.48  #Ref     : 0
% 6.37/2.48  #Sup     : 2757
% 6.37/2.48  #Fact    : 0
% 6.37/2.48  #Define  : 0
% 6.37/2.48  #Split   : 0
% 6.37/2.48  #Chain   : 0
% 6.37/2.48  #Close   : 0
% 6.37/2.48  
% 6.37/2.48  Ordering : KBO
% 6.37/2.48  
% 6.37/2.48  Simplification rules
% 6.37/2.48  ----------------------
% 6.37/2.48  #Subsume      : 46
% 6.37/2.48  #Demod        : 3466
% 6.37/2.48  #Tautology    : 1953
% 6.37/2.48  #SimpNegUnit  : 0
% 6.37/2.48  #BackRed      : 17
% 6.37/2.48  
% 6.37/2.48  #Partial instantiations: 0
% 6.37/2.48  #Strategies tried      : 1
% 6.37/2.48  
% 6.37/2.48  Timing (in seconds)
% 6.37/2.48  ----------------------
% 6.37/2.48  Preprocessing        : 0.28
% 6.37/2.49  Parsing              : 0.15
% 6.37/2.49  CNF conversion       : 0.01
% 6.37/2.49  Main loop            : 1.43
% 6.37/2.49  Inferencing          : 0.41
% 6.37/2.49  Reduction            : 0.73
% 6.37/2.49  Demodulation         : 0.64
% 6.37/2.49  BG Simplification    : 0.05
% 6.37/2.49  Subsumption          : 0.16
% 6.37/2.49  Abstraction          : 0.08
% 6.37/2.49  MUC search           : 0.00
% 6.37/2.49  Cooper               : 0.00
% 6.37/2.49  Total                : 1.74
% 6.37/2.49  Index Insertion      : 0.00
% 6.37/2.49  Index Deletion       : 0.00
% 6.37/2.49  Index Matching       : 0.00
% 6.37/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
