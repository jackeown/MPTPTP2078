%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:14 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   38 (  72 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  52 expanded)
%              Number of equality atoms :   17 (  51 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k2_tarski(H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_tarski(A,B),k5_enumset1(C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [G_49,E_50,B_51,D_52,I_53,C_47,H_54,F_48,A_55] : k2_xboole_0(k5_enumset1(A_55,B_51,C_47,D_52,E_50,F_48,G_49),k2_tarski(H_54,I_53)) = k7_enumset1(A_55,B_51,C_47,D_52,E_50,F_48,G_49,H_54,I_53) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_435,plain,(
    ! [E_108,B_110,I_111,A_106,D_112,F_107,C_109,H_104,G_105] : k2_xboole_0(k2_tarski(H_104,I_111),k5_enumset1(A_106,B_110,C_109,D_112,E_108,F_107,G_105)) = k7_enumset1(A_106,B_110,C_109,D_112,E_108,F_107,G_105,H_104,I_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_8,plain,(
    ! [G_20,H_21,E_18,C_16,I_22,D_17,F_19,A_14,B_15] : k2_xboole_0(k2_tarski(A_14,B_15),k5_enumset1(C_16,D_17,E_18,F_19,G_20,H_21,I_22)) = k7_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20,H_21,I_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_470,plain,(
    ! [E_115,B_118,C_114,H_119,G_116,A_120,F_121,I_113,D_117] : k7_enumset1(H_119,I_113,A_120,B_118,C_114,D_117,E_115,F_121,G_116) = k7_enumset1(A_120,B_118,C_114,D_117,E_115,F_121,G_116,H_119,I_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_8])).

tff(c_441,plain,(
    ! [E_108,B_110,I_111,A_106,D_112,F_107,C_109,H_104,G_105] : k7_enumset1(H_104,I_111,A_106,B_110,C_109,D_112,E_108,F_107,G_105) = k7_enumset1(A_106,B_110,C_109,D_112,E_108,F_107,G_105,H_104,I_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_8])).

tff(c_473,plain,(
    ! [E_115,B_118,C_114,H_119,G_116,A_120,F_121,I_113,D_117] : k7_enumset1(H_119,I_113,A_120,B_118,C_114,D_117,E_115,F_121,G_116) = k7_enumset1(C_114,D_117,E_115,F_121,G_116,H_119,I_113,A_120,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_441])).

tff(c_6,plain,(
    ! [B_6,H_12,C_7,I_13,E_9,D_8,A_5,G_11,F_10] : k2_xboole_0(k1_tarski(A_5),k6_enumset1(B_6,C_7,D_8,E_9,F_10,G_11,H_12,I_13)) = k7_enumset1(A_5,B_6,C_7,D_8,E_9,F_10,G_11,H_12,I_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    k2_xboole_0(k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),k1_tarski('#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_xboole_0(k1_tarski('#skF_9'),k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_16,plain,(
    k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k7_enumset1('#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15])).

tff(c_469,plain,(
    k7_enumset1('#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') != k7_enumset1('#skF_8','#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_16])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_473,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.87  
% 3.62/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.88  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 3.62/1.88  
% 3.62/1.88  %Foreground sorts:
% 3.62/1.88  
% 3.62/1.88  
% 3.62/1.88  %Background operators:
% 3.62/1.88  
% 3.62/1.88  
% 3.62/1.88  %Foreground operators:
% 3.62/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.62/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.62/1.88  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.88  tff('#skF_7', type, '#skF_7': $i).
% 3.62/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.62/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.62/1.88  tff('#skF_5', type, '#skF_5': $i).
% 3.62/1.88  tff('#skF_6', type, '#skF_6': $i).
% 3.62/1.88  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.88  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.88  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.88  tff('#skF_9', type, '#skF_9': $i).
% 3.62/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.88  tff('#skF_8', type, '#skF_8': $i).
% 3.62/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.88  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.62/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.88  
% 3.62/1.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.62/1.89  tff(f_35, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k2_tarski(H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_enumset1)).
% 3.62/1.89  tff(f_33, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_tarski(A, B), k5_enumset1(C, D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_enumset1)).
% 3.62/1.89  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_enumset1)).
% 3.62/1.89  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 3.62/1.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.62/1.89  tff(c_89, plain, (![G_49, E_50, B_51, D_52, I_53, C_47, H_54, F_48, A_55]: (k2_xboole_0(k5_enumset1(A_55, B_51, C_47, D_52, E_50, F_48, G_49), k2_tarski(H_54, I_53))=k7_enumset1(A_55, B_51, C_47, D_52, E_50, F_48, G_49, H_54, I_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.62/1.89  tff(c_435, plain, (![E_108, B_110, I_111, A_106, D_112, F_107, C_109, H_104, G_105]: (k2_xboole_0(k2_tarski(H_104, I_111), k5_enumset1(A_106, B_110, C_109, D_112, E_108, F_107, G_105))=k7_enumset1(A_106, B_110, C_109, D_112, E_108, F_107, G_105, H_104, I_111))), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 3.62/1.89  tff(c_8, plain, (![G_20, H_21, E_18, C_16, I_22, D_17, F_19, A_14, B_15]: (k2_xboole_0(k2_tarski(A_14, B_15), k5_enumset1(C_16, D_17, E_18, F_19, G_20, H_21, I_22))=k7_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20, H_21, I_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.62/1.89  tff(c_470, plain, (![E_115, B_118, C_114, H_119, G_116, A_120, F_121, I_113, D_117]: (k7_enumset1(H_119, I_113, A_120, B_118, C_114, D_117, E_115, F_121, G_116)=k7_enumset1(A_120, B_118, C_114, D_117, E_115, F_121, G_116, H_119, I_113))), inference(superposition, [status(thm), theory('equality')], [c_435, c_8])).
% 3.62/1.89  tff(c_441, plain, (![E_108, B_110, I_111, A_106, D_112, F_107, C_109, H_104, G_105]: (k7_enumset1(H_104, I_111, A_106, B_110, C_109, D_112, E_108, F_107, G_105)=k7_enumset1(A_106, B_110, C_109, D_112, E_108, F_107, G_105, H_104, I_111))), inference(superposition, [status(thm), theory('equality')], [c_435, c_8])).
% 3.62/1.89  tff(c_473, plain, (![E_115, B_118, C_114, H_119, G_116, A_120, F_121, I_113, D_117]: (k7_enumset1(H_119, I_113, A_120, B_118, C_114, D_117, E_115, F_121, G_116)=k7_enumset1(C_114, D_117, E_115, F_121, G_116, H_119, I_113, A_120, B_118))), inference(superposition, [status(thm), theory('equality')], [c_470, c_441])).
% 3.62/1.89  tff(c_6, plain, (![B_6, H_12, C_7, I_13, E_9, D_8, A_5, G_11, F_10]: (k2_xboole_0(k1_tarski(A_5), k6_enumset1(B_6, C_7, D_8, E_9, F_10, G_11, H_12, I_13))=k7_enumset1(A_5, B_6, C_7, D_8, E_9, F_10, G_11, H_12, I_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.89  tff(c_14, plain, (k2_xboole_0(k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_tarski('#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.89  tff(c_15, plain, (k2_xboole_0(k1_tarski('#skF_9'), k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 3.62/1.89  tff(c_16, plain, (k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_enumset1('#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_15])).
% 3.62/1.89  tff(c_469, plain, (k7_enumset1('#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')!=k7_enumset1('#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_441, c_16])).
% 3.62/1.89  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_473, c_473, c_469])).
% 3.62/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.89  
% 3.62/1.89  Inference rules
% 3.62/1.89  ----------------------
% 3.62/1.89  #Ref     : 0
% 3.62/1.89  #Sup     : 173
% 3.62/1.89  #Fact    : 0
% 3.62/1.89  #Define  : 0
% 3.62/1.89  #Split   : 0
% 3.62/1.89  #Chain   : 0
% 3.62/1.89  #Close   : 0
% 3.62/1.89  
% 3.62/1.89  Ordering : KBO
% 3.62/1.89  
% 3.62/1.89  Simplification rules
% 3.62/1.89  ----------------------
% 3.62/1.89  #Subsume      : 39
% 3.62/1.89  #Demod        : 9
% 3.62/1.89  #Tautology    : 52
% 3.62/1.89  #SimpNegUnit  : 0
% 3.62/1.89  #BackRed      : 2
% 3.62/1.89  
% 3.62/1.89  #Partial instantiations: 0
% 3.62/1.89  #Strategies tried      : 1
% 3.62/1.89  
% 3.62/1.89  Timing (in seconds)
% 3.62/1.89  ----------------------
% 3.62/1.89  Preprocessing        : 0.46
% 3.62/1.89  Parsing              : 0.23
% 3.62/1.89  CNF conversion       : 0.03
% 3.62/1.89  Main loop            : 0.57
% 3.62/1.89  Inferencing          : 0.25
% 3.62/1.89  Reduction            : 0.20
% 3.62/1.89  Demodulation         : 0.18
% 3.62/1.89  BG Simplification    : 0.04
% 3.62/1.89  Subsumption          : 0.07
% 3.62/1.89  Abstraction          : 0.05
% 3.62/1.89  MUC search           : 0.00
% 3.62/1.89  Cooper               : 0.00
% 3.62/1.89  Total                : 1.06
% 3.62/1.89  Index Insertion      : 0.00
% 3.62/1.89  Index Deletion       : 0.00
% 3.62/1.89  Index Matching       : 0.00
% 3.62/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
