%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:53 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(c_26,plain,(
    ! [G_60,C_56,E_58,F_59,D_57,B_55,A_54] : k2_xboole_0(k1_enumset1(A_54,B_55,C_56),k2_enumset1(D_57,E_58,F_59,G_60)) = k5_enumset1(A_54,B_55,C_56,D_57,E_58,F_59,G_60) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_xboole_0(k2_tarski(A_29,B_30),k2_tarski(C_31,D_32)) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [A_87,E_88,D_91,B_89,C_90] : k2_xboole_0(k1_enumset1(A_87,B_89,C_90),k2_tarski(D_91,E_88)) = k3_enumset1(A_87,B_89,C_90,D_91,E_88) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_507,plain,(
    ! [A_181,E_185,C_184,C_183,B_182,D_180] : k2_xboole_0(k1_enumset1(A_181,B_182,C_184),k2_xboole_0(k2_tarski(D_180,E_185),C_183)) = k2_xboole_0(k3_enumset1(A_181,B_182,C_184,D_180,E_185),C_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_4])).

tff(c_537,plain,(
    ! [A_181,A_29,C_184,D_32,B_182,C_31,B_30] : k2_xboole_0(k3_enumset1(A_181,B_182,C_184,A_29,B_30),k2_tarski(C_31,D_32)) = k2_xboole_0(k1_enumset1(A_181,B_182,C_184),k2_enumset1(A_29,B_30,C_31,D_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_507])).

tff(c_542,plain,(
    ! [A_181,A_29,C_184,D_32,B_182,C_31,B_30] : k2_xboole_0(k3_enumset1(A_181,B_182,C_184,A_29,B_30),k2_tarski(C_31,D_32)) = k5_enumset1(A_181,B_182,C_184,A_29,B_30,C_31,D_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_537])).

tff(c_10,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),k1_tarski(B_21)) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_251,plain,(
    ! [E_115,A_113,C_114,D_111,F_110,B_112] : k2_xboole_0(k3_enumset1(A_113,B_112,C_114,D_111,E_115),k1_tarski(F_110)) = k4_enumset1(A_113,B_112,C_114,D_111,E_115,F_110) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_626,plain,(
    ! [B_212,C_209,E_206,F_210,D_211,C_207,A_208] : k2_xboole_0(k3_enumset1(A_208,B_212,C_209,D_211,E_206),k2_xboole_0(k1_tarski(F_210),C_207)) = k2_xboole_0(k4_enumset1(A_208,B_212,C_209,D_211,E_206,F_210),C_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_4])).

tff(c_665,plain,(
    ! [B_212,C_209,E_206,A_20,B_21,D_211,A_208] : k2_xboole_0(k4_enumset1(A_208,B_212,C_209,D_211,E_206,A_20),k1_tarski(B_21)) = k2_xboole_0(k3_enumset1(A_208,B_212,C_209,D_211,E_206),k2_tarski(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_626])).

tff(c_669,plain,(
    ! [B_212,C_209,E_206,A_20,B_21,D_211,A_208] : k2_xboole_0(k4_enumset1(A_208,B_212,C_209,D_211,E_206,A_20),k1_tarski(B_21)) = k5_enumset1(A_208,B_212,C_209,D_211,E_206,A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_665])).

tff(c_28,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tarski('#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:41:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  
% 2.91/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.91/1.41  
% 2.91/1.41  %Foreground sorts:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Background operators:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Foreground operators:
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.91/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.41  
% 2.91/1.42  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 2.91/1.42  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 2.91/1.42  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 2.91/1.42  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.91/1.42  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.91/1.42  tff(f_49, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 2.91/1.42  tff(f_54, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.91/1.42  tff(c_26, plain, (![G_60, C_56, E_58, F_59, D_57, B_55, A_54]: (k2_xboole_0(k1_enumset1(A_54, B_55, C_56), k2_enumset1(D_57, E_58, F_59, G_60))=k5_enumset1(A_54, B_55, C_56, D_57, E_58, F_59, G_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.91/1.42  tff(c_16, plain, (![A_29, B_30, C_31, D_32]: (k2_xboole_0(k2_tarski(A_29, B_30), k2_tarski(C_31, D_32))=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.91/1.42  tff(c_149, plain, (![A_87, E_88, D_91, B_89, C_90]: (k2_xboole_0(k1_enumset1(A_87, B_89, C_90), k2_tarski(D_91, E_88))=k3_enumset1(A_87, B_89, C_90, D_91, E_88))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.42  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.42  tff(c_507, plain, (![A_181, E_185, C_184, C_183, B_182, D_180]: (k2_xboole_0(k1_enumset1(A_181, B_182, C_184), k2_xboole_0(k2_tarski(D_180, E_185), C_183))=k2_xboole_0(k3_enumset1(A_181, B_182, C_184, D_180, E_185), C_183))), inference(superposition, [status(thm), theory('equality')], [c_149, c_4])).
% 2.91/1.42  tff(c_537, plain, (![A_181, A_29, C_184, D_32, B_182, C_31, B_30]: (k2_xboole_0(k3_enumset1(A_181, B_182, C_184, A_29, B_30), k2_tarski(C_31, D_32))=k2_xboole_0(k1_enumset1(A_181, B_182, C_184), k2_enumset1(A_29, B_30, C_31, D_32)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_507])).
% 2.91/1.42  tff(c_542, plain, (![A_181, A_29, C_184, D_32, B_182, C_31, B_30]: (k2_xboole_0(k3_enumset1(A_181, B_182, C_184, A_29, B_30), k2_tarski(C_31, D_32))=k5_enumset1(A_181, B_182, C_184, A_29, B_30, C_31, D_32))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_537])).
% 2.91/1.42  tff(c_10, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(B_21))=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.42  tff(c_251, plain, (![E_115, A_113, C_114, D_111, F_110, B_112]: (k2_xboole_0(k3_enumset1(A_113, B_112, C_114, D_111, E_115), k1_tarski(F_110))=k4_enumset1(A_113, B_112, C_114, D_111, E_115, F_110))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.42  tff(c_626, plain, (![B_212, C_209, E_206, F_210, D_211, C_207, A_208]: (k2_xboole_0(k3_enumset1(A_208, B_212, C_209, D_211, E_206), k2_xboole_0(k1_tarski(F_210), C_207))=k2_xboole_0(k4_enumset1(A_208, B_212, C_209, D_211, E_206, F_210), C_207))), inference(superposition, [status(thm), theory('equality')], [c_251, c_4])).
% 2.91/1.42  tff(c_665, plain, (![B_212, C_209, E_206, A_20, B_21, D_211, A_208]: (k2_xboole_0(k4_enumset1(A_208, B_212, C_209, D_211, E_206, A_20), k1_tarski(B_21))=k2_xboole_0(k3_enumset1(A_208, B_212, C_209, D_211, E_206), k2_tarski(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_626])).
% 2.91/1.42  tff(c_669, plain, (![B_212, C_209, E_206, A_20, B_21, D_211, A_208]: (k2_xboole_0(k4_enumset1(A_208, B_212, C_209, D_211, E_206, A_20), k1_tarski(B_21))=k5_enumset1(A_208, B_212, C_209, D_211, E_206, A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_665])).
% 2.91/1.42  tff(c_28, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tarski('#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.91/1.42  tff(c_672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_669, c_28])).
% 2.91/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  Inference rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Ref     : 0
% 2.91/1.42  #Sup     : 171
% 2.91/1.42  #Fact    : 0
% 2.91/1.42  #Define  : 0
% 2.91/1.42  #Split   : 0
% 2.91/1.42  #Chain   : 0
% 2.91/1.42  #Close   : 0
% 2.91/1.42  
% 2.91/1.42  Ordering : KBO
% 2.91/1.42  
% 2.91/1.42  Simplification rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Subsume      : 0
% 2.91/1.42  #Demod        : 79
% 2.91/1.42  #Tautology    : 88
% 2.91/1.42  #SimpNegUnit  : 0
% 2.91/1.42  #BackRed      : 1
% 2.91/1.42  
% 2.91/1.42  #Partial instantiations: 0
% 2.91/1.42  #Strategies tried      : 1
% 2.91/1.42  
% 2.91/1.42  Timing (in seconds)
% 2.91/1.42  ----------------------
% 2.91/1.42  Preprocessing        : 0.30
% 2.91/1.42  Parsing              : 0.17
% 2.91/1.42  CNF conversion       : 0.02
% 2.91/1.42  Main loop            : 0.36
% 2.91/1.42  Inferencing          : 0.16
% 2.91/1.42  Reduction            : 0.12
% 2.91/1.42  Demodulation         : 0.10
% 2.91/1.42  BG Simplification    : 0.03
% 2.91/1.43  Subsumption          : 0.04
% 2.91/1.43  Abstraction          : 0.03
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.68
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
