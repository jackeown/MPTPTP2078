%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:11 EST 2020

% Result     : Theorem 10.20s
% Output     : CNFRefutation 10.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  42 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_enumset1(A,B,C),k4_enumset1(D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9,I_12,H_11] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k3_enumset1(E_8,F_9,G_10,H_11,I_12)) = k7_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10,H_11,I_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k3_enumset1(B_14,C_15,D_16,E_17,F_18)) = k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_30,B_31,C_32,D_33] : k4_enumset1(A_30,A_30,A_30,B_31,C_32,D_33) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [E_54,B_53,C_52,D_50,A_51] : k4_enumset1(A_51,A_51,B_53,C_52,D_50,E_54) = k3_enumset1(A_51,B_53,C_52,D_50,E_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_34,B_35,C_36] : k4_enumset1(A_34,A_34,A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [C_52,D_50,E_54] : k3_enumset1(C_52,C_52,C_52,D_50,E_54) = k1_enumset1(C_52,D_50,E_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_121,plain,(
    ! [A_65,D_67,C_62,B_64,F_66,E_63] : k2_xboole_0(k3_enumset1(A_65,B_64,C_62,D_67,E_63),k1_tarski(F_66)) = k4_enumset1(A_65,B_64,C_62,D_67,E_63,F_66) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_364,plain,(
    ! [B_111,A_113,C_114,D_108,C_109,F_110,E_112] : k2_xboole_0(k3_enumset1(A_113,B_111,C_109,D_108,E_112),k2_xboole_0(k1_tarski(F_110),C_114)) = k2_xboole_0(k4_enumset1(A_113,B_111,C_109,D_108,E_112,F_110),C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_2])).

tff(c_394,plain,(
    ! [C_114,E_54,C_52,F_110,D_50] : k2_xboole_0(k4_enumset1(C_52,C_52,C_52,D_50,E_54,F_110),C_114) = k2_xboole_0(k1_enumset1(C_52,D_50,E_54),k2_xboole_0(k1_tarski(F_110),C_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_364])).

tff(c_423,plain,(
    ! [C_121,D_119,F_123,C_122,E_120] : k2_xboole_0(k1_enumset1(C_121,D_119,E_120),k2_xboole_0(k1_tarski(F_123),C_122)) = k2_xboole_0(k2_enumset1(C_121,D_119,E_120,F_123),C_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_394])).

tff(c_453,plain,(
    ! [C_121,E_17,F_18,A_13,D_119,B_14,C_15,E_120,D_16] : k2_xboole_0(k2_enumset1(C_121,D_119,E_120,A_13),k3_enumset1(B_14,C_15,D_16,E_17,F_18)) = k2_xboole_0(k1_enumset1(C_121,D_119,E_120),k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_423])).

tff(c_458,plain,(
    ! [C_121,E_17,F_18,A_13,D_119,B_14,C_15,E_120,D_16] : k2_xboole_0(k1_enumset1(C_121,D_119,E_120),k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18)) = k7_enumset1(C_121,D_119,E_120,A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_453])).

tff(c_16,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k4_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:51:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.20/3.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.79  
% 10.20/3.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.79  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 10.20/3.79  
% 10.20/3.79  %Foreground sorts:
% 10.20/3.79  
% 10.20/3.79  
% 10.20/3.79  %Background operators:
% 10.20/3.79  
% 10.20/3.79  
% 10.20/3.79  %Foreground operators:
% 10.20/3.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.20/3.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.20/3.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.20/3.79  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.20/3.79  tff('#skF_7', type, '#skF_7': $i).
% 10.20/3.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.20/3.79  tff('#skF_5', type, '#skF_5': $i).
% 10.20/3.79  tff('#skF_6', type, '#skF_6': $i).
% 10.20/3.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.20/3.79  tff('#skF_2', type, '#skF_2': $i).
% 10.20/3.79  tff('#skF_3', type, '#skF_3': $i).
% 10.20/3.79  tff('#skF_1', type, '#skF_1': $i).
% 10.20/3.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.20/3.79  tff('#skF_9', type, '#skF_9': $i).
% 10.20/3.79  tff('#skF_8', type, '#skF_8': $i).
% 10.20/3.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.20/3.79  tff('#skF_4', type, '#skF_4': $i).
% 10.20/3.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.20/3.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.20/3.79  
% 10.20/3.80  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_enumset1(A, B, C, D), k3_enumset1(E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l142_enumset1)).
% 10.20/3.80  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 10.20/3.80  tff(f_37, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 10.20/3.80  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 10.20/3.80  tff(f_39, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 10.20/3.80  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 10.20/3.80  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 10.20/3.80  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_enumset1(A, B, C), k4_enumset1(D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 10.20/3.80  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9, I_12, H_11]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k3_enumset1(E_8, F_9, G_10, H_11, I_12))=k7_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10, H_11, I_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.20/3.80  tff(c_6, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k3_enumset1(B_14, C_15, D_16, E_17, F_18))=k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.20/3.80  tff(c_12, plain, (![A_30, B_31, C_32, D_33]: (k4_enumset1(A_30, A_30, A_30, B_31, C_32, D_33)=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.20/3.80  tff(c_69, plain, (![E_54, B_53, C_52, D_50, A_51]: (k4_enumset1(A_51, A_51, B_53, C_52, D_50, E_54)=k3_enumset1(A_51, B_53, C_52, D_50, E_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.20/3.80  tff(c_14, plain, (![A_34, B_35, C_36]: (k4_enumset1(A_34, A_34, A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.20/3.80  tff(c_80, plain, (![C_52, D_50, E_54]: (k3_enumset1(C_52, C_52, C_52, D_50, E_54)=k1_enumset1(C_52, D_50, E_54))), inference(superposition, [status(thm), theory('equality')], [c_69, c_14])).
% 10.20/3.80  tff(c_121, plain, (![A_65, D_67, C_62, B_64, F_66, E_63]: (k2_xboole_0(k3_enumset1(A_65, B_64, C_62, D_67, E_63), k1_tarski(F_66))=k4_enumset1(A_65, B_64, C_62, D_67, E_63, F_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.20/3.80  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.20/3.80  tff(c_364, plain, (![B_111, A_113, C_114, D_108, C_109, F_110, E_112]: (k2_xboole_0(k3_enumset1(A_113, B_111, C_109, D_108, E_112), k2_xboole_0(k1_tarski(F_110), C_114))=k2_xboole_0(k4_enumset1(A_113, B_111, C_109, D_108, E_112, F_110), C_114))), inference(superposition, [status(thm), theory('equality')], [c_121, c_2])).
% 10.20/3.80  tff(c_394, plain, (![C_114, E_54, C_52, F_110, D_50]: (k2_xboole_0(k4_enumset1(C_52, C_52, C_52, D_50, E_54, F_110), C_114)=k2_xboole_0(k1_enumset1(C_52, D_50, E_54), k2_xboole_0(k1_tarski(F_110), C_114)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_364])).
% 10.20/3.80  tff(c_423, plain, (![C_121, D_119, F_123, C_122, E_120]: (k2_xboole_0(k1_enumset1(C_121, D_119, E_120), k2_xboole_0(k1_tarski(F_123), C_122))=k2_xboole_0(k2_enumset1(C_121, D_119, E_120, F_123), C_122))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_394])).
% 10.20/3.80  tff(c_453, plain, (![C_121, E_17, F_18, A_13, D_119, B_14, C_15, E_120, D_16]: (k2_xboole_0(k2_enumset1(C_121, D_119, E_120, A_13), k3_enumset1(B_14, C_15, D_16, E_17, F_18))=k2_xboole_0(k1_enumset1(C_121, D_119, E_120), k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_423])).
% 10.20/3.80  tff(c_458, plain, (![C_121, E_17, F_18, A_13, D_119, B_14, C_15, E_120, D_16]: (k2_xboole_0(k1_enumset1(C_121, D_119, E_120), k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))=k7_enumset1(C_121, D_119, E_120, A_13, B_14, C_15, D_16, E_17, F_18))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_453])).
% 10.20/3.80  tff(c_16, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k4_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.20/3.80  tff(c_8262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_16])).
% 10.20/3.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.80  
% 10.20/3.80  Inference rules
% 10.20/3.80  ----------------------
% 10.20/3.80  #Ref     : 0
% 10.20/3.80  #Sup     : 2134
% 10.20/3.80  #Fact    : 0
% 10.20/3.80  #Define  : 0
% 10.20/3.80  #Split   : 0
% 10.20/3.80  #Chain   : 0
% 10.20/3.80  #Close   : 0
% 10.20/3.80  
% 10.20/3.80  Ordering : KBO
% 10.20/3.80  
% 10.20/3.80  Simplification rules
% 10.20/3.80  ----------------------
% 10.20/3.80  #Subsume      : 457
% 10.20/3.80  #Demod        : 1791
% 10.20/3.80  #Tautology    : 715
% 10.20/3.80  #SimpNegUnit  : 0
% 10.20/3.80  #BackRed      : 1
% 10.20/3.80  
% 10.20/3.80  #Partial instantiations: 0
% 10.20/3.80  #Strategies tried      : 1
% 10.20/3.80  
% 10.20/3.80  Timing (in seconds)
% 10.20/3.80  ----------------------
% 10.20/3.81  Preprocessing        : 0.38
% 10.20/3.81  Parsing              : 0.19
% 10.20/3.81  CNF conversion       : 0.03
% 10.20/3.81  Main loop            : 2.64
% 10.20/3.81  Inferencing          : 0.78
% 10.20/3.81  Reduction            : 1.48
% 10.20/3.81  Demodulation         : 1.36
% 10.20/3.81  BG Simplification    : 0.11
% 10.20/3.81  Subsumption          : 0.21
% 10.20/3.81  Abstraction          : 0.18
% 10.20/3.81  MUC search           : 0.00
% 10.20/3.81  Cooper               : 0.00
% 10.20/3.81  Total                : 3.04
% 10.20/3.81  Index Insertion      : 0.00
% 10.20/3.81  Index Deletion       : 0.00
% 10.20/3.81  Index Matching       : 0.00
% 10.20/3.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
