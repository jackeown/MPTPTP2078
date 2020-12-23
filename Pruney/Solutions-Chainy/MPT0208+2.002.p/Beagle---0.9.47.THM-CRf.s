%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:14 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   43 (  85 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  61 expanded)
%              Number of equality atoms :   18 (  60 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_enumset1(F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).

tff(c_307,plain,(
    ! [B_115,I_112,F_113,E_119,D_111,A_117,H_118,C_116,G_114] : k2_xboole_0(k2_enumset1(A_117,B_115,C_116,D_111),k3_enumset1(E_119,F_113,G_114,H_118,I_112)) = k7_enumset1(A_117,B_115,C_116,D_111,E_119,F_113,G_114,H_118,I_112) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_349,plain,(
    ! [F_135,D_137,I_129,E_130,C_133,H_131,G_132,A_136,B_134] : k2_xboole_0(k3_enumset1(E_130,F_135,G_132,H_131,I_129),k2_enumset1(A_136,B_134,C_133,D_137)) = k7_enumset1(A_136,B_134,C_133,D_137,E_130,F_135,G_132,H_131,I_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_2])).

tff(c_12,plain,(
    ! [H_39,B_33,C_34,E_36,F_37,G_38,I_40,A_32,D_35] : k2_xboole_0(k3_enumset1(A_32,B_33,C_34,D_35,E_36),k2_enumset1(F_37,G_38,H_39,I_40)) = k7_enumset1(A_32,B_33,C_34,D_35,E_36,F_37,G_38,H_39,I_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_355,plain,(
    ! [F_135,D_137,I_129,E_130,C_133,H_131,G_132,A_136,B_134] : k7_enumset1(E_130,F_135,G_132,H_131,I_129,A_136,B_134,C_133,D_137) = k7_enumset1(A_136,B_134,C_133,D_137,E_130,F_135,G_132,H_131,I_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_12])).

tff(c_381,plain,(
    ! [H_140,A_145,G_144,I_138,B_142,F_143,E_141,D_146,C_139] : k7_enumset1(E_141,F_143,G_144,H_140,I_138,A_145,B_142,C_139,D_146) = k7_enumset1(A_145,B_142,C_139,D_146,E_141,F_143,G_144,H_140,I_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_12])).

tff(c_384,plain,(
    ! [H_140,A_145,G_144,I_138,B_142,F_143,E_141,D_146,C_139] : k7_enumset1(F_143,G_144,H_140,I_138,A_145,B_142,C_139,D_146,E_141) = k7_enumset1(E_141,F_143,G_144,H_140,I_138,A_145,B_142,C_139,D_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_355])).

tff(c_8,plain,(
    ! [G_20,H_21,E_18,C_16,I_22,D_17,F_19,A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k6_enumset1(B_15,C_16,D_17,E_18,F_19,G_20,H_21,I_22)) = k7_enumset1(A_14,B_15,C_16,D_17,E_18,F_19,G_20,H_21,I_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    k2_xboole_0(k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),k1_tarski('#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k2_xboole_0(k1_tarski('#skF_9'),k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_22,plain,(
    k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k7_enumset1('#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_21])).

tff(c_380,plain,(
    k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k7_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_22])).

tff(c_466,plain,(
    k7_enumset1('#skF_8','#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k7_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_384,c_380])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.58/1.35  
% 2.58/1.35  %Foreground sorts:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Background operators:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Foreground operators:
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.35  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.58/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.58/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.35  
% 2.58/1.36  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_enumset1(A, B, C, D), k3_enumset1(E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l142_enumset1)).
% 2.58/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.58/1.36  tff(f_37, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_enumset1(F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_enumset1)).
% 2.58/1.36  tff(f_33, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_enumset1)).
% 2.58/1.36  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_enumset1)).
% 2.58/1.36  tff(c_307, plain, (![B_115, I_112, F_113, E_119, D_111, A_117, H_118, C_116, G_114]: (k2_xboole_0(k2_enumset1(A_117, B_115, C_116, D_111), k3_enumset1(E_119, F_113, G_114, H_118, I_112))=k7_enumset1(A_117, B_115, C_116, D_111, E_119, F_113, G_114, H_118, I_112))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.36  tff(c_349, plain, (![F_135, D_137, I_129, E_130, C_133, H_131, G_132, A_136, B_134]: (k2_xboole_0(k3_enumset1(E_130, F_135, G_132, H_131, I_129), k2_enumset1(A_136, B_134, C_133, D_137))=k7_enumset1(A_136, B_134, C_133, D_137, E_130, F_135, G_132, H_131, I_129))), inference(superposition, [status(thm), theory('equality')], [c_307, c_2])).
% 2.58/1.36  tff(c_12, plain, (![H_39, B_33, C_34, E_36, F_37, G_38, I_40, A_32, D_35]: (k2_xboole_0(k3_enumset1(A_32, B_33, C_34, D_35, E_36), k2_enumset1(F_37, G_38, H_39, I_40))=k7_enumset1(A_32, B_33, C_34, D_35, E_36, F_37, G_38, H_39, I_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.36  tff(c_355, plain, (![F_135, D_137, I_129, E_130, C_133, H_131, G_132, A_136, B_134]: (k7_enumset1(E_130, F_135, G_132, H_131, I_129, A_136, B_134, C_133, D_137)=k7_enumset1(A_136, B_134, C_133, D_137, E_130, F_135, G_132, H_131, I_129))), inference(superposition, [status(thm), theory('equality')], [c_349, c_12])).
% 2.58/1.36  tff(c_381, plain, (![H_140, A_145, G_144, I_138, B_142, F_143, E_141, D_146, C_139]: (k7_enumset1(E_141, F_143, G_144, H_140, I_138, A_145, B_142, C_139, D_146)=k7_enumset1(A_145, B_142, C_139, D_146, E_141, F_143, G_144, H_140, I_138))), inference(superposition, [status(thm), theory('equality')], [c_349, c_12])).
% 2.58/1.36  tff(c_384, plain, (![H_140, A_145, G_144, I_138, B_142, F_143, E_141, D_146, C_139]: (k7_enumset1(F_143, G_144, H_140, I_138, A_145, B_142, C_139, D_146, E_141)=k7_enumset1(E_141, F_143, G_144, H_140, I_138, A_145, B_142, C_139, D_146))), inference(superposition, [status(thm), theory('equality')], [c_381, c_355])).
% 2.58/1.36  tff(c_8, plain, (![G_20, H_21, E_18, C_16, I_22, D_17, F_19, A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k6_enumset1(B_15, C_16, D_17, E_18, F_19, G_20, H_21, I_22))=k7_enumset1(A_14, B_15, C_16, D_17, E_18, F_19, G_20, H_21, I_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.36  tff(c_20, plain, (k2_xboole_0(k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_tarski('#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.58/1.36  tff(c_21, plain, (k2_xboole_0(k1_tarski('#skF_9'), k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 2.58/1.36  tff(c_22, plain, (k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_enumset1('#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_21])).
% 2.58/1.36  tff(c_380, plain, (k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_22])).
% 2.58/1.36  tff(c_466, plain, (k7_enumset1('#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k7_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_384, c_380])).
% 2.58/1.36  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_466])).
% 2.58/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.36  
% 2.58/1.36  Inference rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Ref     : 0
% 2.58/1.36  #Sup     : 119
% 2.58/1.36  #Fact    : 0
% 2.58/1.36  #Define  : 0
% 2.58/1.36  #Split   : 0
% 2.58/1.36  #Chain   : 0
% 2.58/1.36  #Close   : 0
% 2.58/1.36  
% 2.58/1.36  Ordering : KBO
% 2.58/1.36  
% 2.58/1.36  Simplification rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Subsume      : 24
% 2.58/1.36  #Demod        : 18
% 2.58/1.36  #Tautology    : 54
% 2.58/1.36  #SimpNegUnit  : 0
% 2.58/1.36  #BackRed      : 2
% 2.58/1.36  
% 2.58/1.36  #Partial instantiations: 0
% 2.58/1.36  #Strategies tried      : 1
% 2.58/1.36  
% 2.58/1.36  Timing (in seconds)
% 2.58/1.36  ----------------------
% 2.58/1.36  Preprocessing        : 0.31
% 2.58/1.36  Parsing              : 0.16
% 2.58/1.36  CNF conversion       : 0.02
% 2.58/1.36  Main loop            : 0.28
% 2.58/1.36  Inferencing          : 0.12
% 2.58/1.36  Reduction            : 0.11
% 2.58/1.36  Demodulation         : 0.09
% 2.58/1.36  BG Simplification    : 0.02
% 2.58/1.36  Subsumption          : 0.03
% 2.58/1.36  Abstraction          : 0.03
% 2.58/1.36  MUC search           : 0.00
% 2.58/1.36  Cooper               : 0.00
% 2.58/1.36  Total                : 0.62
% 2.58/1.36  Index Insertion      : 0.00
% 2.58/1.36  Index Deletion       : 0.00
% 2.58/1.36  Index Matching       : 0.00
% 2.58/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
