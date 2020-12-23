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
% DateTime   : Thu Dec  3 09:46:41 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   45 (  73 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   28 (  56 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_19,B_20,C_21,D_22] : k3_enumset1(A_19,A_19,B_20,C_21,D_22) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : k4_enumset1(A_23,A_23,B_24,C_25,D_26,E_27) = k3_enumset1(A_23,B_24,C_25,D_26,E_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] : k5_enumset1(A_28,A_28,B_29,C_30,D_31,E_32,F_33) = k4_enumset1(A_28,B_29,C_30,D_31,E_32,F_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_128,plain,(
    ! [D_74,F_79,G_78,B_75,A_77,E_80,C_76] : k2_xboole_0(k3_enumset1(A_77,B_75,C_76,D_74,E_80),k2_tarski(F_79,G_78)) = k5_enumset1(A_77,B_75,C_76,D_74,E_80,F_79,G_78) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_137,plain,(
    ! [A_19,F_79,G_78,C_21,D_22,B_20] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,F_79,G_78) = k2_xboole_0(k2_enumset1(A_19,B_20,C_21,D_22),k2_tarski(F_79,G_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_128])).

tff(c_147,plain,(
    ! [D_85,B_83,G_86,F_81,A_84,C_82] : k2_xboole_0(k2_enumset1(A_84,B_83,C_82,D_85),k2_tarski(F_81,G_86)) = k4_enumset1(A_84,B_83,C_82,D_85,F_81,G_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_137])).

tff(c_156,plain,(
    ! [C_18,B_17,A_16,G_86,F_81] : k4_enumset1(A_16,A_16,B_17,C_18,F_81,G_86) = k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k2_tarski(F_81,G_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_166,plain,(
    ! [B_87,F_89,C_91,G_88,A_90] : k2_xboole_0(k1_enumset1(A_90,B_87,C_91),k2_tarski(F_89,G_88)) = k3_enumset1(A_90,B_87,C_91,F_89,G_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_156])).

tff(c_175,plain,(
    ! [A_14,B_15,F_89,G_88] : k3_enumset1(A_14,A_14,B_15,F_89,G_88) = k2_xboole_0(k2_tarski(A_14,B_15),k2_tarski(F_89,G_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_166])).

tff(c_185,plain,(
    ! [A_92,B_93,F_94,G_95] : k2_xboole_0(k2_tarski(A_92,B_93),k2_tarski(F_94,G_95)) = k2_enumset1(A_92,B_93,F_94,G_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_175])).

tff(c_301,plain,(
    ! [A_111,B_112,B_113,A_114] : k2_xboole_0(k2_tarski(A_111,B_112),k2_tarski(B_113,A_114)) = k2_enumset1(A_111,B_112,A_114,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_185])).

tff(c_194,plain,(
    ! [B_6,A_5,F_94,G_95] : k2_xboole_0(k2_tarski(B_6,A_5),k2_tarski(F_94,G_95)) = k2_enumset1(A_5,B_6,F_94,G_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_185])).

tff(c_337,plain,(
    ! [B_115,A_116,B_117,A_118] : k2_enumset1(B_115,A_116,B_117,A_118) = k2_enumset1(A_116,B_115,A_118,B_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_194])).

tff(c_414,plain,(
    ! [B_119,B_120,A_121] : k2_enumset1(B_119,B_119,B_120,A_121) = k1_enumset1(B_119,A_121,B_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_12])).

tff(c_429,plain,(
    ! [B_119,B_120,A_121] : k1_enumset1(B_119,B_120,A_121) = k1_enumset1(B_119,A_121,B_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_12])).

tff(c_22,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_22])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.29  
% 2.13/1.30  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.13/1.30  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.13/1.30  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.13/1.30  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.13/1.30  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.13/1.30  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.13/1.30  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 2.13/1.30  tff(f_48, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 2.13/1.30  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.30  tff(c_14, plain, (![A_19, B_20, C_21, D_22]: (k3_enumset1(A_19, A_19, B_20, C_21, D_22)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.30  tff(c_10, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.30  tff(c_16, plain, (![A_23, B_24, D_26, C_25, E_27]: (k4_enumset1(A_23, A_23, B_24, C_25, D_26, E_27)=k3_enumset1(A_23, B_24, C_25, D_26, E_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.30  tff(c_12, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.30  tff(c_18, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (k5_enumset1(A_28, A_28, B_29, C_30, D_31, E_32, F_33)=k4_enumset1(A_28, B_29, C_30, D_31, E_32, F_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.30  tff(c_128, plain, (![D_74, F_79, G_78, B_75, A_77, E_80, C_76]: (k2_xboole_0(k3_enumset1(A_77, B_75, C_76, D_74, E_80), k2_tarski(F_79, G_78))=k5_enumset1(A_77, B_75, C_76, D_74, E_80, F_79, G_78))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.30  tff(c_137, plain, (![A_19, F_79, G_78, C_21, D_22, B_20]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, F_79, G_78)=k2_xboole_0(k2_enumset1(A_19, B_20, C_21, D_22), k2_tarski(F_79, G_78)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_128])).
% 2.13/1.30  tff(c_147, plain, (![D_85, B_83, G_86, F_81, A_84, C_82]: (k2_xboole_0(k2_enumset1(A_84, B_83, C_82, D_85), k2_tarski(F_81, G_86))=k4_enumset1(A_84, B_83, C_82, D_85, F_81, G_86))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_137])).
% 2.13/1.30  tff(c_156, plain, (![C_18, B_17, A_16, G_86, F_81]: (k4_enumset1(A_16, A_16, B_17, C_18, F_81, G_86)=k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k2_tarski(F_81, G_86)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_147])).
% 2.13/1.30  tff(c_166, plain, (![B_87, F_89, C_91, G_88, A_90]: (k2_xboole_0(k1_enumset1(A_90, B_87, C_91), k2_tarski(F_89, G_88))=k3_enumset1(A_90, B_87, C_91, F_89, G_88))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_156])).
% 2.13/1.30  tff(c_175, plain, (![A_14, B_15, F_89, G_88]: (k3_enumset1(A_14, A_14, B_15, F_89, G_88)=k2_xboole_0(k2_tarski(A_14, B_15), k2_tarski(F_89, G_88)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_166])).
% 2.13/1.30  tff(c_185, plain, (![A_92, B_93, F_94, G_95]: (k2_xboole_0(k2_tarski(A_92, B_93), k2_tarski(F_94, G_95))=k2_enumset1(A_92, B_93, F_94, G_95))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_175])).
% 2.13/1.30  tff(c_301, plain, (![A_111, B_112, B_113, A_114]: (k2_xboole_0(k2_tarski(A_111, B_112), k2_tarski(B_113, A_114))=k2_enumset1(A_111, B_112, A_114, B_113))), inference(superposition, [status(thm), theory('equality')], [c_6, c_185])).
% 2.13/1.30  tff(c_194, plain, (![B_6, A_5, F_94, G_95]: (k2_xboole_0(k2_tarski(B_6, A_5), k2_tarski(F_94, G_95))=k2_enumset1(A_5, B_6, F_94, G_95))), inference(superposition, [status(thm), theory('equality')], [c_6, c_185])).
% 2.13/1.30  tff(c_337, plain, (![B_115, A_116, B_117, A_118]: (k2_enumset1(B_115, A_116, B_117, A_118)=k2_enumset1(A_116, B_115, A_118, B_117))), inference(superposition, [status(thm), theory('equality')], [c_301, c_194])).
% 2.13/1.30  tff(c_414, plain, (![B_119, B_120, A_121]: (k2_enumset1(B_119, B_119, B_120, A_121)=k1_enumset1(B_119, A_121, B_120))), inference(superposition, [status(thm), theory('equality')], [c_337, c_12])).
% 2.13/1.30  tff(c_429, plain, (![B_119, B_120, A_121]: (k1_enumset1(B_119, B_120, A_121)=k1_enumset1(B_119, A_121, B_120))), inference(superposition, [status(thm), theory('equality')], [c_414, c_12])).
% 2.13/1.30  tff(c_22, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.30  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_429, c_22])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 111
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 0
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 1
% 2.13/1.30  #Demod        : 19
% 2.13/1.30  #Tautology    : 67
% 2.13/1.30  #SimpNegUnit  : 0
% 2.13/1.30  #BackRed      : 1
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.30  Preprocessing        : 0.29
% 2.13/1.30  Parsing              : 0.15
% 2.13/1.30  CNF conversion       : 0.02
% 2.13/1.30  Main loop            : 0.25
% 2.13/1.30  Inferencing          : 0.10
% 2.13/1.30  Reduction            : 0.09
% 2.13/1.30  Demodulation         : 0.08
% 2.13/1.31  BG Simplification    : 0.02
% 2.13/1.31  Subsumption          : 0.03
% 2.13/1.31  Abstraction          : 0.02
% 2.13/1.31  MUC search           : 0.00
% 2.13/1.31  Cooper               : 0.00
% 2.13/1.31  Total                : 0.56
% 2.13/1.31  Index Insertion      : 0.00
% 2.13/1.31  Index Deletion       : 0.00
% 2.13/1.31  Index Matching       : 0.00
% 2.13/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
