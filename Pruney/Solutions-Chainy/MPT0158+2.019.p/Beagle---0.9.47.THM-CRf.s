%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:21 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k2_enumset1(A_1,B_2,C_3,D_4),k2_tarski(E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_36,B_37,C_38,D_39] : k3_enumset1(A_36,A_36,B_37,C_38,D_39) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [G_13,D_10,A_7,F_12,B_8,E_11,C_9] : k2_xboole_0(k1_tarski(A_7),k4_enumset1(B_8,C_9,D_10,E_11,F_12,G_13)) = k5_enumset1(A_7,B_8,C_9,D_10,E_11,F_12,G_13) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_283,plain,(
    ! [G_107,E_104,C_108,A_110,H_103,F_105,B_109,D_106] : k2_xboole_0(k2_tarski(A_110,B_109),k4_enumset1(C_108,D_106,E_104,F_105,G_107,H_103)) = k6_enumset1(A_110,B_109,C_108,D_106,E_104,F_105,G_107,H_103) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_295,plain,(
    ! [G_107,E_104,C_108,H_103,F_105,A_30,D_106] : k6_enumset1(A_30,A_30,C_108,D_106,E_104,F_105,G_107,H_103) = k2_xboole_0(k1_tarski(A_30),k4_enumset1(C_108,D_106,E_104,F_105,G_107,H_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_283])).

tff(c_298,plain,(
    ! [G_107,E_104,C_108,H_103,F_105,A_30,D_106] : k6_enumset1(A_30,A_30,C_108,D_106,E_104,F_105,G_107,H_103) = k5_enumset1(A_30,C_108,D_106,E_104,F_105,G_107,H_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_295])).

tff(c_18,plain,(
    ! [E_44,C_42,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,E_44) = k3_enumset1(A_40,B_41,C_42,D_43,E_44) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_216,plain,(
    ! [G_93,D_95,E_91,F_92,B_96,A_89,C_90,H_94] : k2_xboole_0(k4_enumset1(A_89,B_96,C_90,D_95,E_91,F_92),k2_tarski(G_93,H_94)) = k6_enumset1(A_89,B_96,C_90,D_95,E_91,F_92,G_93,H_94) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_225,plain,(
    ! [E_44,C_42,G_93,A_40,D_43,H_94,B_41] : k6_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,G_93,H_94) = k2_xboole_0(k3_enumset1(A_40,B_41,C_42,D_43,E_44),k2_tarski(G_93,H_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_216])).

tff(c_1720,plain,(
    ! [G_194,B_200,C_199,A_197,D_198,H_195,E_196] : k2_xboole_0(k3_enumset1(A_197,B_200,C_199,D_198,E_196),k2_tarski(G_194,H_195)) = k5_enumset1(A_197,B_200,C_199,D_198,E_196,G_194,H_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_225])).

tff(c_1744,plain,(
    ! [G_194,D_39,A_36,H_195,C_38,B_37] : k5_enumset1(A_36,A_36,B_37,C_38,D_39,G_194,H_195) = k2_xboole_0(k2_enumset1(A_36,B_37,C_38,D_39),k2_tarski(G_194,H_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1720])).

tff(c_1752,plain,(
    ! [G_194,D_39,A_36,H_195,C_38,B_37] : k5_enumset1(A_36,A_36,B_37,C_38,D_39,G_194,H_195) = k4_enumset1(A_36,B_37,C_38,D_39,G_194,H_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1744])).

tff(c_20,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.80  
% 4.63/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.80  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.63/1.80  
% 4.63/1.80  %Foreground sorts:
% 4.63/1.80  
% 4.63/1.80  
% 4.63/1.80  %Background operators:
% 4.63/1.80  
% 4.63/1.80  
% 4.63/1.80  %Foreground operators:
% 4.63/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.63/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.63/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.63/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.63/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.63/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.63/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.63/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.80  
% 4.63/1.82  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 4.63/1.82  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.63/1.82  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 4.63/1.82  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.63/1.82  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 4.63/1.82  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.63/1.82  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 4.63/1.82  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.63/1.82  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k2_enumset1(A_1, B_2, C_3, D_4), k2_tarski(E_5, F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.63/1.82  tff(c_16, plain, (![A_36, B_37, C_38, D_39]: (k3_enumset1(A_36, A_36, B_37, C_38, D_39)=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.82  tff(c_4, plain, (![G_13, D_10, A_7, F_12, B_8, E_11, C_9]: (k2_xboole_0(k1_tarski(A_7), k4_enumset1(B_8, C_9, D_10, E_11, F_12, G_13))=k5_enumset1(A_7, B_8, C_9, D_10, E_11, F_12, G_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.63/1.82  tff(c_10, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.82  tff(c_283, plain, (![G_107, E_104, C_108, A_110, H_103, F_105, B_109, D_106]: (k2_xboole_0(k2_tarski(A_110, B_109), k4_enumset1(C_108, D_106, E_104, F_105, G_107, H_103))=k6_enumset1(A_110, B_109, C_108, D_106, E_104, F_105, G_107, H_103))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.82  tff(c_295, plain, (![G_107, E_104, C_108, H_103, F_105, A_30, D_106]: (k6_enumset1(A_30, A_30, C_108, D_106, E_104, F_105, G_107, H_103)=k2_xboole_0(k1_tarski(A_30), k4_enumset1(C_108, D_106, E_104, F_105, G_107, H_103)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_283])).
% 4.63/1.82  tff(c_298, plain, (![G_107, E_104, C_108, H_103, F_105, A_30, D_106]: (k6_enumset1(A_30, A_30, C_108, D_106, E_104, F_105, G_107, H_103)=k5_enumset1(A_30, C_108, D_106, E_104, F_105, G_107, H_103))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_295])).
% 4.63/1.82  tff(c_18, plain, (![E_44, C_42, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, E_44)=k3_enumset1(A_40, B_41, C_42, D_43, E_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.82  tff(c_216, plain, (![G_93, D_95, E_91, F_92, B_96, A_89, C_90, H_94]: (k2_xboole_0(k4_enumset1(A_89, B_96, C_90, D_95, E_91, F_92), k2_tarski(G_93, H_94))=k6_enumset1(A_89, B_96, C_90, D_95, E_91, F_92, G_93, H_94))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.63/1.82  tff(c_225, plain, (![E_44, C_42, G_93, A_40, D_43, H_94, B_41]: (k6_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, G_93, H_94)=k2_xboole_0(k3_enumset1(A_40, B_41, C_42, D_43, E_44), k2_tarski(G_93, H_94)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_216])).
% 4.63/1.82  tff(c_1720, plain, (![G_194, B_200, C_199, A_197, D_198, H_195, E_196]: (k2_xboole_0(k3_enumset1(A_197, B_200, C_199, D_198, E_196), k2_tarski(G_194, H_195))=k5_enumset1(A_197, B_200, C_199, D_198, E_196, G_194, H_195))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_225])).
% 4.63/1.82  tff(c_1744, plain, (![G_194, D_39, A_36, H_195, C_38, B_37]: (k5_enumset1(A_36, A_36, B_37, C_38, D_39, G_194, H_195)=k2_xboole_0(k2_enumset1(A_36, B_37, C_38, D_39), k2_tarski(G_194, H_195)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1720])).
% 4.63/1.82  tff(c_1752, plain, (![G_194, D_39, A_36, H_195, C_38, B_37]: (k5_enumset1(A_36, A_36, B_37, C_38, D_39, G_194, H_195)=k4_enumset1(A_36, B_37, C_38, D_39, G_194, H_195))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1744])).
% 4.63/1.82  tff(c_20, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.63/1.82  tff(c_2805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1752, c_20])).
% 4.63/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.82  
% 4.63/1.82  Inference rules
% 4.63/1.82  ----------------------
% 4.63/1.82  #Ref     : 0
% 4.63/1.82  #Sup     : 667
% 4.63/1.82  #Fact    : 0
% 4.63/1.82  #Define  : 0
% 4.63/1.82  #Split   : 0
% 4.63/1.82  #Chain   : 0
% 4.63/1.82  #Close   : 0
% 4.63/1.82  
% 4.63/1.82  Ordering : KBO
% 4.63/1.82  
% 4.63/1.82  Simplification rules
% 4.63/1.82  ----------------------
% 4.63/1.82  #Subsume      : 107
% 4.63/1.82  #Demod        : 698
% 4.63/1.82  #Tautology    : 420
% 4.63/1.82  #SimpNegUnit  : 0
% 4.63/1.82  #BackRed      : 1
% 4.63/1.82  
% 4.63/1.82  #Partial instantiations: 0
% 4.63/1.82  #Strategies tried      : 1
% 4.63/1.82  
% 4.63/1.82  Timing (in seconds)
% 4.63/1.82  ----------------------
% 4.63/1.82  Preprocessing        : 0.29
% 4.63/1.82  Parsing              : 0.15
% 4.63/1.82  CNF conversion       : 0.02
% 4.63/1.82  Main loop            : 0.76
% 4.63/1.82  Inferencing          : 0.28
% 4.63/1.82  Reduction            : 0.34
% 4.63/1.82  Demodulation         : 0.30
% 4.63/1.82  BG Simplification    : 0.03
% 4.63/1.82  Subsumption          : 0.07
% 4.63/1.82  Abstraction          : 0.05
% 4.63/1.82  MUC search           : 0.00
% 4.63/1.82  Cooper               : 0.00
% 4.63/1.82  Total                : 1.09
% 4.63/1.82  Index Insertion      : 0.00
% 4.63/1.82  Index Deletion       : 0.00
% 4.63/1.82  Index Matching       : 0.00
% 4.63/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
