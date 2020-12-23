%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:16 EST 2020

% Result     : Theorem 13.78s
% Output     : CNFRefutation 13.96s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 122 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 ( 108 expanded)
%              Number of equality atoms :   38 ( 107 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_38,C_40,B_39] : k1_enumset1(A_38,C_40,B_39) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [B_12,C_13,A_11] : k1_enumset1(B_12,C_13,A_11) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k1_tarski(A_17),k2_tarski(B_18,C_19)) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1079,plain,(
    ! [A_95,B_96,C_97,D_98] : k2_xboole_0(k1_tarski(A_95),k1_enumset1(B_96,C_97,D_98)) = k2_enumset1(A_95,B_96,C_97,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1136,plain,(
    ! [A_95,A_29,B_30] : k2_xboole_0(k1_tarski(A_95),k2_tarski(A_29,B_30)) = k2_enumset1(A_95,A_29,A_29,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1079])).

tff(c_1147,plain,(
    ! [A_95,A_29,B_30] : k2_enumset1(A_95,A_29,A_29,B_30) = k1_enumset1(A_95,A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1136])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_xboole_0(k1_tarski(A_20),k1_enumset1(B_21,C_22,D_23)) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_168,plain,(
    ! [B_51,C_52,A_53] : k1_enumset1(B_51,C_52,A_53) = k1_enumset1(A_53,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_208,plain,(
    ! [A_53,C_52] : k1_enumset1(A_53,C_52,C_52) = k2_tarski(C_52,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_22])).

tff(c_20,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_582,plain,(
    ! [A_67,B_68,C_69] : k2_xboole_0(k1_tarski(A_67),k2_tarski(B_68,C_69)) = k1_enumset1(A_67,B_68,C_69) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_603,plain,(
    ! [A_67,A_28] : k2_xboole_0(k1_tarski(A_67),k1_tarski(A_28)) = k1_enumset1(A_67,A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_582])).

tff(c_606,plain,(
    ! [A_67,A_28] : k2_xboole_0(k1_tarski(A_67),k1_tarski(A_28)) = k2_tarski(A_28,A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_603])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_727,plain,(
    ! [A_79,B_80,C_81] : k2_xboole_0(k2_xboole_0(A_79,B_80),C_81) = k2_xboole_0(A_79,k2_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_776,plain,(
    ! [A_84,A_82,B_83] : k2_xboole_0(A_84,k2_xboole_0(A_82,B_83)) = k2_xboole_0(A_82,k2_xboole_0(B_83,A_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_727])).

tff(c_876,plain,(
    ! [A_28,A_82,A_67] : k2_xboole_0(k1_tarski(A_28),k2_xboole_0(A_82,k1_tarski(A_67))) = k2_xboole_0(A_82,k2_tarski(A_28,A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_776])).

tff(c_22560,plain,(
    ! [A_392,B_393,C_394,A_395] : k2_xboole_0(k1_tarski(A_392),k2_xboole_0(k2_tarski(B_393,C_394),A_395)) = k2_xboole_0(A_395,k1_enumset1(A_392,B_393,C_394)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_776])).

tff(c_22664,plain,(
    ! [B_393,C_394,A_28,A_67] : k2_xboole_0(k2_tarski(B_393,C_394),k2_tarski(A_28,A_67)) = k2_xboole_0(k1_tarski(A_67),k1_enumset1(A_28,B_393,C_394)) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_22560])).

tff(c_22805,plain,(
    ! [B_393,C_394,A_28,A_67] : k2_xboole_0(k2_tarski(B_393,C_394),k2_tarski(A_28,A_67)) = k2_enumset1(A_67,A_28,B_393,C_394) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22664])).

tff(c_635,plain,(
    ! [A_73,A_74] : k2_xboole_0(k1_tarski(A_73),k1_tarski(A_74)) = k2_tarski(A_74,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_603])).

tff(c_656,plain,(
    ! [A_75,A_76] : k2_xboole_0(k1_tarski(A_75),k1_tarski(A_76)) = k2_tarski(A_75,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_2])).

tff(c_662,plain,(
    ! [A_76,A_75] : k2_tarski(A_76,A_75) = k2_tarski(A_75,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_606])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_31])).

tff(c_687,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_662,c_32])).

tff(c_23506,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22805,c_687])).

tff(c_23509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10,c_28,c_10,c_1147,c_23506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.78/5.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.78/5.71  
% 13.78/5.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.78/5.71  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 13.78/5.71  
% 13.78/5.71  %Foreground sorts:
% 13.78/5.71  
% 13.78/5.71  
% 13.78/5.71  %Background operators:
% 13.78/5.71  
% 13.78/5.71  
% 13.78/5.71  %Foreground operators:
% 13.78/5.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.78/5.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.78/5.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.78/5.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.78/5.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.78/5.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.78/5.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.78/5.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.78/5.71  tff('#skF_2', type, '#skF_2': $i).
% 13.78/5.71  tff('#skF_3', type, '#skF_3': $i).
% 13.78/5.71  tff('#skF_1', type, '#skF_1': $i).
% 13.78/5.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.78/5.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.78/5.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.78/5.71  
% 13.96/5.72  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 13.96/5.72  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 13.96/5.72  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 13.96/5.72  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.96/5.72  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 13.96/5.72  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.96/5.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.96/5.72  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 13.96/5.72  tff(f_56, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 13.96/5.72  tff(c_28, plain, (![A_38, C_40, B_39]: (k1_enumset1(A_38, C_40, B_39)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.96/5.72  tff(c_10, plain, (![B_12, C_13, A_11]: (k1_enumset1(B_12, C_13, A_11)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.96/5.72  tff(c_14, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(B_18, C_19))=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.96/5.72  tff(c_22, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.96/5.72  tff(c_1079, plain, (![A_95, B_96, C_97, D_98]: (k2_xboole_0(k1_tarski(A_95), k1_enumset1(B_96, C_97, D_98))=k2_enumset1(A_95, B_96, C_97, D_98))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.96/5.72  tff(c_1136, plain, (![A_95, A_29, B_30]: (k2_xboole_0(k1_tarski(A_95), k2_tarski(A_29, B_30))=k2_enumset1(A_95, A_29, A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1079])).
% 13.96/5.72  tff(c_1147, plain, (![A_95, A_29, B_30]: (k2_enumset1(A_95, A_29, A_29, B_30)=k1_enumset1(A_95, A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1136])).
% 13.96/5.72  tff(c_16, plain, (![A_20, B_21, C_22, D_23]: (k2_xboole_0(k1_tarski(A_20), k1_enumset1(B_21, C_22, D_23))=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.96/5.72  tff(c_168, plain, (![B_51, C_52, A_53]: (k1_enumset1(B_51, C_52, A_53)=k1_enumset1(A_53, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.96/5.72  tff(c_208, plain, (![A_53, C_52]: (k1_enumset1(A_53, C_52, C_52)=k2_tarski(C_52, A_53))), inference(superposition, [status(thm), theory('equality')], [c_168, c_22])).
% 13.96/5.72  tff(c_20, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.96/5.72  tff(c_582, plain, (![A_67, B_68, C_69]: (k2_xboole_0(k1_tarski(A_67), k2_tarski(B_68, C_69))=k1_enumset1(A_67, B_68, C_69))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.96/5.72  tff(c_603, plain, (![A_67, A_28]: (k2_xboole_0(k1_tarski(A_67), k1_tarski(A_28))=k1_enumset1(A_67, A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_20, c_582])).
% 13.96/5.72  tff(c_606, plain, (![A_67, A_28]: (k2_xboole_0(k1_tarski(A_67), k1_tarski(A_28))=k2_tarski(A_28, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_603])).
% 13.96/5.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.96/5.72  tff(c_727, plain, (![A_79, B_80, C_81]: (k2_xboole_0(k2_xboole_0(A_79, B_80), C_81)=k2_xboole_0(A_79, k2_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.96/5.72  tff(c_776, plain, (![A_84, A_82, B_83]: (k2_xboole_0(A_84, k2_xboole_0(A_82, B_83))=k2_xboole_0(A_82, k2_xboole_0(B_83, A_84)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_727])).
% 13.96/5.72  tff(c_876, plain, (![A_28, A_82, A_67]: (k2_xboole_0(k1_tarski(A_28), k2_xboole_0(A_82, k1_tarski(A_67)))=k2_xboole_0(A_82, k2_tarski(A_28, A_67)))), inference(superposition, [status(thm), theory('equality')], [c_606, c_776])).
% 13.96/5.72  tff(c_22560, plain, (![A_392, B_393, C_394, A_395]: (k2_xboole_0(k1_tarski(A_392), k2_xboole_0(k2_tarski(B_393, C_394), A_395))=k2_xboole_0(A_395, k1_enumset1(A_392, B_393, C_394)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_776])).
% 13.96/5.72  tff(c_22664, plain, (![B_393, C_394, A_28, A_67]: (k2_xboole_0(k2_tarski(B_393, C_394), k2_tarski(A_28, A_67))=k2_xboole_0(k1_tarski(A_67), k1_enumset1(A_28, B_393, C_394)))), inference(superposition, [status(thm), theory('equality')], [c_876, c_22560])).
% 13.96/5.72  tff(c_22805, plain, (![B_393, C_394, A_28, A_67]: (k2_xboole_0(k2_tarski(B_393, C_394), k2_tarski(A_28, A_67))=k2_enumset1(A_67, A_28, B_393, C_394))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22664])).
% 13.96/5.72  tff(c_635, plain, (![A_73, A_74]: (k2_xboole_0(k1_tarski(A_73), k1_tarski(A_74))=k2_tarski(A_74, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_603])).
% 13.96/5.72  tff(c_656, plain, (![A_75, A_76]: (k2_xboole_0(k1_tarski(A_75), k1_tarski(A_76))=k2_tarski(A_75, A_76))), inference(superposition, [status(thm), theory('equality')], [c_635, c_2])).
% 13.96/5.72  tff(c_662, plain, (![A_76, A_75]: (k2_tarski(A_76, A_75)=k2_tarski(A_75, A_76))), inference(superposition, [status(thm), theory('equality')], [c_656, c_606])).
% 13.96/5.72  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.96/5.72  tff(c_31, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 13.96/5.72  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_31])).
% 13.96/5.72  tff(c_687, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_662, c_32])).
% 13.96/5.72  tff(c_23506, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22805, c_687])).
% 13.96/5.72  tff(c_23509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_10, c_28, c_10, c_1147, c_23506])).
% 13.96/5.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.96/5.72  
% 13.96/5.72  Inference rules
% 13.96/5.72  ----------------------
% 13.96/5.72  #Ref     : 0
% 13.96/5.72  #Sup     : 6083
% 13.96/5.72  #Fact    : 0
% 13.96/5.72  #Define  : 0
% 13.96/5.72  #Split   : 0
% 13.96/5.72  #Chain   : 0
% 13.96/5.72  #Close   : 0
% 13.96/5.72  
% 13.96/5.72  Ordering : KBO
% 13.96/5.72  
% 13.96/5.72  Simplification rules
% 13.96/5.72  ----------------------
% 13.96/5.72  #Subsume      : 1760
% 13.96/5.72  #Demod        : 3842
% 13.96/5.72  #Tautology    : 2662
% 13.96/5.72  #SimpNegUnit  : 0
% 13.96/5.72  #BackRed      : 2
% 13.96/5.72  
% 13.96/5.72  #Partial instantiations: 0
% 13.96/5.72  #Strategies tried      : 1
% 13.96/5.72  
% 13.96/5.72  Timing (in seconds)
% 13.96/5.72  ----------------------
% 13.96/5.72  Preprocessing        : 0.29
% 13.96/5.72  Parsing              : 0.15
% 13.96/5.72  CNF conversion       : 0.02
% 13.96/5.72  Main loop            : 4.65
% 13.96/5.72  Inferencing          : 0.80
% 13.96/5.72  Reduction            : 3.13
% 13.96/5.72  Demodulation         : 2.97
% 13.96/5.72  BG Simplification    : 0.10
% 13.96/5.72  Subsumption          : 0.45
% 13.96/5.72  Abstraction          : 0.17
% 13.96/5.72  MUC search           : 0.00
% 13.96/5.72  Cooper               : 0.00
% 13.96/5.72  Total                : 4.96
% 13.96/5.72  Index Insertion      : 0.00
% 13.96/5.72  Index Deletion       : 0.00
% 13.96/5.72  Index Matching       : 0.00
% 13.96/5.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
