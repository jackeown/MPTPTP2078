%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:39 EST 2020

% Result     : Theorem 9.01s
% Output     : CNFRefutation 9.16s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 278 expanded)
%              Number of leaves         :   18 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :   47 ( 266 expanded)
%              Number of equality atoms :   46 ( 265 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(c_497,plain,(
    ! [A_38,B_39,C_40,D_41] : k2_xboole_0(k1_tarski(A_38),k1_enumset1(B_39,C_40,D_41)) = k2_enumset1(A_38,B_39,C_40,D_41) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_515,plain,(
    ! [B_39,C_40,D_41,A_38] : k2_xboole_0(k1_enumset1(B_39,C_40,D_41),k1_tarski(A_38)) = k2_enumset1(A_38,B_39,C_40,D_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_2])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [B_19,A_20] : k2_xboole_0(k1_tarski(B_19),k1_tarski(A_20)) = k2_tarski(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [B_19,A_20] : k2_tarski(B_19,A_20) = k2_tarski(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_6])).

tff(c_179,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k1_tarski(A_26),k2_tarski(B_27,C_28)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_454,plain,(
    ! [B_35,C_36,A_37] : k2_xboole_0(k2_tarski(B_35,C_36),k1_tarski(A_37)) = k1_enumset1(A_37,B_35,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_3033,plain,(
    ! [B_90,A_91,A_92] : k2_xboole_0(k2_tarski(B_90,A_91),k1_tarski(A_92)) = k1_enumset1(A_92,A_91,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_454])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_185,plain,(
    ! [A_26,B_27,C_28,C_5] : k2_xboole_0(k1_tarski(A_26),k2_xboole_0(k2_tarski(B_27,C_28),C_5)) = k2_xboole_0(k1_enumset1(A_26,B_27,C_28),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_4])).

tff(c_3039,plain,(
    ! [A_26,B_90,A_91,A_92] : k2_xboole_0(k1_enumset1(A_26,B_90,A_91),k1_tarski(A_92)) = k2_xboole_0(k1_tarski(A_26),k1_enumset1(A_92,A_91,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3033,c_185])).

tff(c_3326,plain,(
    ! [A_99,A_98,A_101,B_100] : k2_enumset1(A_99,A_98,A_101,B_100) = k2_enumset1(A_98,A_99,B_100,A_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_10,c_3039])).

tff(c_206,plain,(
    ! [B_27,C_28,A_26] : k2_xboole_0(k2_tarski(B_27,C_28),k1_tarski(A_26)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_2813,plain,(
    ! [A_82,B_83,C_84,C_85] : k2_xboole_0(k1_tarski(A_82),k2_xboole_0(k2_tarski(B_83,C_84),C_85)) = k2_xboole_0(k1_enumset1(A_82,B_83,C_84),C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_4])).

tff(c_2946,plain,(
    ! [A_82,B_27,C_28,A_26] : k2_xboole_0(k1_enumset1(A_82,B_27,C_28),k1_tarski(A_26)) = k2_xboole_0(k1_tarski(A_82),k1_enumset1(A_26,B_27,C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2813])).

tff(c_2997,plain,(
    ! [A_82,A_26,B_27,C_28] : k2_enumset1(A_82,A_26,B_27,C_28) = k2_enumset1(A_26,A_82,B_27,C_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_10,c_2946])).

tff(c_3344,plain,(
    ! [A_99,A_98,B_100,A_101] : k2_enumset1(A_99,A_98,B_100,A_101) = k2_enumset1(A_99,A_98,A_101,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_3326,c_2997])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k1_tarski(A_8),k2_tarski(B_9,C_10)) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2029,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k1_tarski(A_64),k2_xboole_0(k1_tarski(B_65),C_66)) = k2_xboole_0(k2_tarski(A_64,B_65),C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_133])).

tff(c_2186,plain,(
    ! [A_64,A_6,B_7] : k2_xboole_0(k2_tarski(A_64,A_6),k1_tarski(B_7)) = k2_xboole_0(k1_tarski(A_64),k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2029])).

tff(c_2265,plain,(
    ! [B_70,A_71,A_72] : k1_enumset1(B_70,A_71,A_72) = k1_enumset1(A_71,A_72,B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_8,c_2186])).

tff(c_8891,plain,(
    ! [A_171,A_172,B_173,A_174] : k2_xboole_0(k1_enumset1(A_171,A_172,B_173),k1_tarski(A_174)) = k2_enumset1(A_174,B_173,A_171,A_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_2265,c_515])).

tff(c_8939,plain,(
    ! [A_174,B_173,A_171,A_172] : k2_enumset1(A_174,B_173,A_171,A_172) = k2_enumset1(A_174,A_171,A_172,B_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_8891,c_515])).

tff(c_2180,plain,(
    ! [A_64,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_64,A_8),k2_tarski(B_9,C_10)) = k2_xboole_0(k1_tarski(A_64),k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2029])).

tff(c_2217,plain,(
    ! [A_64,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_64,A_8),k2_tarski(B_9,C_10)) = k2_enumset1(A_64,A_8,B_9,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2180])).

tff(c_54,plain,(
    ! [B_18,A_17] : k2_xboole_0(k1_tarski(B_18),k1_tarski(A_17)) = k2_tarski(A_17,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_271,plain,(
    ! [C_32,A_33,B_34] : k2_xboole_0(C_32,k2_xboole_0(A_33,B_34)) = k2_xboole_0(A_33,k2_xboole_0(B_34,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_2])).

tff(c_5423,plain,(
    ! [A_125,A_126,B_127] : k2_xboole_0(k1_tarski(A_125),k2_xboole_0(A_126,k1_tarski(B_127))) = k2_xboole_0(A_126,k2_tarski(A_125,B_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_271])).

tff(c_5453,plain,(
    ! [A_125,B_27,C_28,B_127] : k2_xboole_0(k1_enumset1(A_125,B_27,C_28),k1_tarski(B_127)) = k2_xboole_0(k2_tarski(B_27,C_28),k2_tarski(A_125,B_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5423,c_185])).

tff(c_5650,plain,(
    ! [B_27,C_28,A_125,B_127] : k2_enumset1(B_27,C_28,A_125,B_127) = k2_enumset1(B_127,A_125,B_27,C_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2217,c_515,c_5453])).

tff(c_12,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k1_tarski('#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_enumset1('#skF_1','#skF_2','#skF_3')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_14,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13])).

tff(c_5341,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3344,c_3344,c_14])).

tff(c_5912,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3344,c_5650,c_5341])).

tff(c_9013,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8939,c_5912])).

tff(c_9016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3344,c_9013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.01/3.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.16/3.57  
% 9.16/3.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.16/3.58  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.16/3.58  
% 9.16/3.58  %Foreground sorts:
% 9.16/3.58  
% 9.16/3.58  
% 9.16/3.58  %Background operators:
% 9.16/3.58  
% 9.16/3.58  
% 9.16/3.58  %Foreground operators:
% 9.16/3.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.16/3.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.16/3.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.16/3.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.16/3.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.16/3.58  tff('#skF_2', type, '#skF_2': $i).
% 9.16/3.58  tff('#skF_3', type, '#skF_3': $i).
% 9.16/3.58  tff('#skF_1', type, '#skF_1': $i).
% 9.16/3.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.16/3.58  tff('#skF_4', type, '#skF_4': $i).
% 9.16/3.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.16/3.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.16/3.58  
% 9.16/3.59  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 9.16/3.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.16/3.59  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 9.16/3.59  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 9.16/3.59  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 9.16/3.59  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 9.16/3.59  tff(c_497, plain, (![A_38, B_39, C_40, D_41]: (k2_xboole_0(k1_tarski(A_38), k1_enumset1(B_39, C_40, D_41))=k2_enumset1(A_38, B_39, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.16/3.59  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.16/3.59  tff(c_515, plain, (![B_39, C_40, D_41, A_38]: (k2_xboole_0(k1_enumset1(B_39, C_40, D_41), k1_tarski(A_38))=k2_enumset1(A_38, B_39, C_40, D_41))), inference(superposition, [status(thm), theory('equality')], [c_497, c_2])).
% 9.16/3.59  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.16/3.59  tff(c_48, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.16/3.59  tff(c_69, plain, (![B_19, A_20]: (k2_xboole_0(k1_tarski(B_19), k1_tarski(A_20))=k2_tarski(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2])).
% 9.16/3.59  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.16/3.59  tff(c_75, plain, (![B_19, A_20]: (k2_tarski(B_19, A_20)=k2_tarski(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_69, c_6])).
% 9.16/3.59  tff(c_179, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k1_tarski(A_26), k2_tarski(B_27, C_28))=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.16/3.59  tff(c_454, plain, (![B_35, C_36, A_37]: (k2_xboole_0(k2_tarski(B_35, C_36), k1_tarski(A_37))=k1_enumset1(A_37, B_35, C_36))), inference(superposition, [status(thm), theory('equality')], [c_2, c_179])).
% 9.16/3.59  tff(c_3033, plain, (![B_90, A_91, A_92]: (k2_xboole_0(k2_tarski(B_90, A_91), k1_tarski(A_92))=k1_enumset1(A_92, A_91, B_90))), inference(superposition, [status(thm), theory('equality')], [c_75, c_454])).
% 9.16/3.59  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.16/3.59  tff(c_185, plain, (![A_26, B_27, C_28, C_5]: (k2_xboole_0(k1_tarski(A_26), k2_xboole_0(k2_tarski(B_27, C_28), C_5))=k2_xboole_0(k1_enumset1(A_26, B_27, C_28), C_5))), inference(superposition, [status(thm), theory('equality')], [c_179, c_4])).
% 9.16/3.59  tff(c_3039, plain, (![A_26, B_90, A_91, A_92]: (k2_xboole_0(k1_enumset1(A_26, B_90, A_91), k1_tarski(A_92))=k2_xboole_0(k1_tarski(A_26), k1_enumset1(A_92, A_91, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_3033, c_185])).
% 9.16/3.59  tff(c_3326, plain, (![A_99, A_98, A_101, B_100]: (k2_enumset1(A_99, A_98, A_101, B_100)=k2_enumset1(A_98, A_99, B_100, A_101))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_10, c_3039])).
% 9.16/3.59  tff(c_206, plain, (![B_27, C_28, A_26]: (k2_xboole_0(k2_tarski(B_27, C_28), k1_tarski(A_26))=k1_enumset1(A_26, B_27, C_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_179])).
% 9.16/3.59  tff(c_2813, plain, (![A_82, B_83, C_84, C_85]: (k2_xboole_0(k1_tarski(A_82), k2_xboole_0(k2_tarski(B_83, C_84), C_85))=k2_xboole_0(k1_enumset1(A_82, B_83, C_84), C_85))), inference(superposition, [status(thm), theory('equality')], [c_179, c_4])).
% 9.16/3.59  tff(c_2946, plain, (![A_82, B_27, C_28, A_26]: (k2_xboole_0(k1_enumset1(A_82, B_27, C_28), k1_tarski(A_26))=k2_xboole_0(k1_tarski(A_82), k1_enumset1(A_26, B_27, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_206, c_2813])).
% 9.16/3.59  tff(c_2997, plain, (![A_82, A_26, B_27, C_28]: (k2_enumset1(A_82, A_26, B_27, C_28)=k2_enumset1(A_26, A_82, B_27, C_28))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_10, c_2946])).
% 9.16/3.59  tff(c_3344, plain, (![A_99, A_98, B_100, A_101]: (k2_enumset1(A_99, A_98, B_100, A_101)=k2_enumset1(A_99, A_98, A_101, B_100))), inference(superposition, [status(thm), theory('equality')], [c_3326, c_2997])).
% 9.16/3.59  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k1_tarski(A_8), k2_tarski(B_9, C_10))=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.16/3.59  tff(c_133, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.16/3.59  tff(c_2029, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k1_tarski(A_64), k2_xboole_0(k1_tarski(B_65), C_66))=k2_xboole_0(k2_tarski(A_64, B_65), C_66))), inference(superposition, [status(thm), theory('equality')], [c_6, c_133])).
% 9.16/3.59  tff(c_2186, plain, (![A_64, A_6, B_7]: (k2_xboole_0(k2_tarski(A_64, A_6), k1_tarski(B_7))=k2_xboole_0(k1_tarski(A_64), k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2029])).
% 9.16/3.59  tff(c_2265, plain, (![B_70, A_71, A_72]: (k1_enumset1(B_70, A_71, A_72)=k1_enumset1(A_71, A_72, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_8, c_2186])).
% 9.16/3.59  tff(c_8891, plain, (![A_171, A_172, B_173, A_174]: (k2_xboole_0(k1_enumset1(A_171, A_172, B_173), k1_tarski(A_174))=k2_enumset1(A_174, B_173, A_171, A_172))), inference(superposition, [status(thm), theory('equality')], [c_2265, c_515])).
% 9.16/3.59  tff(c_8939, plain, (![A_174, B_173, A_171, A_172]: (k2_enumset1(A_174, B_173, A_171, A_172)=k2_enumset1(A_174, A_171, A_172, B_173))), inference(superposition, [status(thm), theory('equality')], [c_8891, c_515])).
% 9.16/3.59  tff(c_2180, plain, (![A_64, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_64, A_8), k2_tarski(B_9, C_10))=k2_xboole_0(k1_tarski(A_64), k1_enumset1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2029])).
% 9.16/3.59  tff(c_2217, plain, (![A_64, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_64, A_8), k2_tarski(B_9, C_10))=k2_enumset1(A_64, A_8, B_9, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2180])).
% 9.16/3.59  tff(c_54, plain, (![B_18, A_17]: (k2_xboole_0(k1_tarski(B_18), k1_tarski(A_17))=k2_tarski(A_17, B_18))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2])).
% 9.16/3.59  tff(c_271, plain, (![C_32, A_33, B_34]: (k2_xboole_0(C_32, k2_xboole_0(A_33, B_34))=k2_xboole_0(A_33, k2_xboole_0(B_34, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_2])).
% 9.16/3.59  tff(c_5423, plain, (![A_125, A_126, B_127]: (k2_xboole_0(k1_tarski(A_125), k2_xboole_0(A_126, k1_tarski(B_127)))=k2_xboole_0(A_126, k2_tarski(A_125, B_127)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_271])).
% 9.16/3.59  tff(c_5453, plain, (![A_125, B_27, C_28, B_127]: (k2_xboole_0(k1_enumset1(A_125, B_27, C_28), k1_tarski(B_127))=k2_xboole_0(k2_tarski(B_27, C_28), k2_tarski(A_125, B_127)))), inference(superposition, [status(thm), theory('equality')], [c_5423, c_185])).
% 9.16/3.59  tff(c_5650, plain, (![B_27, C_28, A_125, B_127]: (k2_enumset1(B_27, C_28, A_125, B_127)=k2_enumset1(B_127, A_125, B_27, C_28))), inference(demodulation, [status(thm), theory('equality')], [c_2217, c_515, c_5453])).
% 9.16/3.59  tff(c_12, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k1_tarski('#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.16/3.59  tff(c_13, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_enumset1('#skF_1', '#skF_2', '#skF_3'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 9.16/3.59  tff(c_14, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13])).
% 9.16/3.59  tff(c_5341, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3344, c_3344, c_14])).
% 9.16/3.59  tff(c_5912, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3344, c_5650, c_5341])).
% 9.16/3.59  tff(c_9013, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8939, c_5912])).
% 9.16/3.59  tff(c_9016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3344, c_9013])).
% 9.16/3.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.16/3.59  
% 9.16/3.59  Inference rules
% 9.16/3.59  ----------------------
% 9.16/3.59  #Ref     : 0
% 9.16/3.59  #Sup     : 2391
% 9.16/3.59  #Fact    : 0
% 9.16/3.59  #Define  : 0
% 9.16/3.59  #Split   : 0
% 9.16/3.59  #Chain   : 0
% 9.16/3.59  #Close   : 0
% 9.16/3.59  
% 9.16/3.59  Ordering : KBO
% 9.16/3.59  
% 9.16/3.59  Simplification rules
% 9.16/3.59  ----------------------
% 9.16/3.59  #Subsume      : 588
% 9.16/3.59  #Demod        : 1382
% 9.16/3.59  #Tautology    : 474
% 9.16/3.59  #SimpNegUnit  : 0
% 9.16/3.59  #BackRed      : 2
% 9.16/3.59  
% 9.16/3.59  #Partial instantiations: 0
% 9.16/3.59  #Strategies tried      : 1
% 9.16/3.59  
% 9.16/3.59  Timing (in seconds)
% 9.16/3.59  ----------------------
% 9.16/3.60  Preprocessing        : 0.27
% 9.16/3.60  Parsing              : 0.16
% 9.16/3.60  CNF conversion       : 0.01
% 9.16/3.60  Main loop            : 2.55
% 9.16/3.60  Inferencing          : 0.48
% 9.16/3.60  Reduction            : 1.69
% 9.16/3.60  Demodulation         : 1.59
% 9.16/3.60  BG Simplification    : 0.08
% 9.16/3.60  Subsumption          : 0.22
% 9.16/3.60  Abstraction          : 0.13
% 9.16/3.60  MUC search           : 0.00
% 9.16/3.60  Cooper               : 0.00
% 9.16/3.60  Total                : 2.86
% 9.16/3.60  Index Insertion      : 0.00
% 9.16/3.60  Index Deletion       : 0.00
% 9.16/3.60  Index Matching       : 0.00
% 9.16/3.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
