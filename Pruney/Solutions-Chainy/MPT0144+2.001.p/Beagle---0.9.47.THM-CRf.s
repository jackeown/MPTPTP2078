%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:51 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   39 (  72 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  52 expanded)
%              Number of equality atoms :   18 (  51 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_208,plain,(
    ! [A_57,C_56,F_59,G_58,E_60,D_54,B_55] : k2_xboole_0(k2_enumset1(A_57,B_55,C_56,D_54),k1_enumset1(E_60,F_59,G_58)) = k5_enumset1(A_57,B_55,C_56,D_54,E_60,F_59,G_58) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_309,plain,(
    ! [F_84,A_88,E_87,G_85,D_83,B_86,C_82] : k2_xboole_0(k1_enumset1(E_87,F_84,G_85),k2_enumset1(A_88,B_86,C_82,D_83)) = k5_enumset1(A_88,B_86,C_82,D_83,E_87,F_84,G_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_16,plain,(
    ! [C_29,D_30,B_28,G_33,F_32,A_27,E_31] : k2_xboole_0(k1_enumset1(A_27,B_28,C_29),k2_enumset1(D_30,E_31,F_32,G_33)) = k5_enumset1(A_27,B_28,C_29,D_30,E_31,F_32,G_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_315,plain,(
    ! [F_84,A_88,E_87,G_85,D_83,B_86,C_82] : k5_enumset1(E_87,F_84,G_85,A_88,B_86,C_82,D_83) = k5_enumset1(A_88,B_86,C_82,D_83,E_87,F_84,G_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_16])).

tff(c_341,plain,(
    ! [E_94,F_91,A_92,B_89,G_95,C_90,D_93] : k5_enumset1(E_94,F_91,G_95,A_92,B_89,C_90,D_93) = k5_enumset1(A_92,B_89,C_90,D_93,E_94,F_91,G_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_16])).

tff(c_344,plain,(
    ! [E_94,F_91,A_92,B_89,G_95,C_90,D_93] : k5_enumset1(E_94,F_91,G_95,A_92,B_89,C_90,D_93) = k5_enumset1(D_93,E_94,F_91,G_95,A_92,B_89,C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_315])).

tff(c_14,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,G_26,E_24] : k2_xboole_0(k2_tarski(A_20,B_21),k3_enumset1(C_22,D_23,E_24,F_25,G_26)) = k5_enumset1(A_20,B_21,C_22,D_23,E_24,F_25,G_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_20,plain,(
    k5_enumset1('#skF_6','#skF_7','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_19])).

tff(c_340,plain,(
    k5_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_1') != k5_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_315,c_20])).

tff(c_370,plain,(
    k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_340])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:06:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.25  
% 2.17/1.25  %Foreground sorts:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Background operators:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Foreground operators:
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.17/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.25  
% 2.17/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.17/1.26  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 2.17/1.26  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 2.17/1.26  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 2.17/1.26  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 2.17/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.26  tff(c_208, plain, (![A_57, C_56, F_59, G_58, E_60, D_54, B_55]: (k2_xboole_0(k2_enumset1(A_57, B_55, C_56, D_54), k1_enumset1(E_60, F_59, G_58))=k5_enumset1(A_57, B_55, C_56, D_54, E_60, F_59, G_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.26  tff(c_309, plain, (![F_84, A_88, E_87, G_85, D_83, B_86, C_82]: (k2_xboole_0(k1_enumset1(E_87, F_84, G_85), k2_enumset1(A_88, B_86, C_82, D_83))=k5_enumset1(A_88, B_86, C_82, D_83, E_87, F_84, G_85))), inference(superposition, [status(thm), theory('equality')], [c_2, c_208])).
% 2.17/1.26  tff(c_16, plain, (![C_29, D_30, B_28, G_33, F_32, A_27, E_31]: (k2_xboole_0(k1_enumset1(A_27, B_28, C_29), k2_enumset1(D_30, E_31, F_32, G_33))=k5_enumset1(A_27, B_28, C_29, D_30, E_31, F_32, G_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.26  tff(c_315, plain, (![F_84, A_88, E_87, G_85, D_83, B_86, C_82]: (k5_enumset1(E_87, F_84, G_85, A_88, B_86, C_82, D_83)=k5_enumset1(A_88, B_86, C_82, D_83, E_87, F_84, G_85))), inference(superposition, [status(thm), theory('equality')], [c_309, c_16])).
% 2.17/1.26  tff(c_341, plain, (![E_94, F_91, A_92, B_89, G_95, C_90, D_93]: (k5_enumset1(E_94, F_91, G_95, A_92, B_89, C_90, D_93)=k5_enumset1(A_92, B_89, C_90, D_93, E_94, F_91, G_95))), inference(superposition, [status(thm), theory('equality')], [c_309, c_16])).
% 2.17/1.26  tff(c_344, plain, (![E_94, F_91, A_92, B_89, G_95, C_90, D_93]: (k5_enumset1(E_94, F_91, G_95, A_92, B_89, C_90, D_93)=k5_enumset1(D_93, E_94, F_91, G_95, A_92, B_89, C_90))), inference(superposition, [status(thm), theory('equality')], [c_341, c_315])).
% 2.17/1.26  tff(c_14, plain, (![C_22, D_23, A_20, B_21, F_25, G_26, E_24]: (k2_xboole_0(k2_tarski(A_20, B_21), k3_enumset1(C_22, D_23, E_24, F_25, G_26))=k5_enumset1(A_20, B_21, C_22, D_23, E_24, F_25, G_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.26  tff(c_18, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.26  tff(c_19, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 2.17/1.26  tff(c_20, plain, (k5_enumset1('#skF_6', '#skF_7', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_19])).
% 2.17/1.26  tff(c_340, plain, (k5_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_1')!=k5_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_315, c_20])).
% 2.17/1.26  tff(c_370, plain, (k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_340])).
% 2.17/1.26  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_315, c_370])).
% 2.17/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  Inference rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Ref     : 0
% 2.17/1.26  #Sup     : 90
% 2.17/1.26  #Fact    : 0
% 2.17/1.26  #Define  : 0
% 2.17/1.26  #Split   : 0
% 2.17/1.26  #Chain   : 0
% 2.17/1.26  #Close   : 0
% 2.17/1.26  
% 2.17/1.26  Ordering : KBO
% 2.17/1.26  
% 2.17/1.26  Simplification rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Subsume      : 2
% 2.17/1.26  #Demod        : 28
% 2.17/1.26  #Tautology    : 64
% 2.17/1.26  #SimpNegUnit  : 0
% 2.17/1.26  #BackRed      : 2
% 2.17/1.26  
% 2.17/1.26  #Partial instantiations: 0
% 2.17/1.26  #Strategies tried      : 1
% 2.17/1.26  
% 2.17/1.26  Timing (in seconds)
% 2.17/1.26  ----------------------
% 2.17/1.27  Preprocessing        : 0.27
% 2.17/1.27  Parsing              : 0.15
% 2.17/1.27  CNF conversion       : 0.02
% 2.17/1.27  Main loop            : 0.22
% 2.17/1.27  Inferencing          : 0.09
% 2.17/1.27  Reduction            : 0.09
% 2.17/1.27  Demodulation         : 0.07
% 2.17/1.27  BG Simplification    : 0.01
% 2.17/1.27  Subsumption          : 0.03
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.52
% 2.17/1.27  Index Insertion      : 0.00
% 2.17/1.27  Index Deletion       : 0.00
% 2.17/1.27  Index Matching       : 0.00
% 2.17/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
