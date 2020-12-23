%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:27 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(c_10,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k1_tarski(A_1),k1_enumset1(B_2,C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k5_enumset1(A_22,A_22,B_23,C_24,D_25,E_26,F_27) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_258,plain,(
    ! [B_62,G_61,D_59,E_65,C_63,F_60,A_64] : k2_xboole_0(k1_enumset1(A_64,B_62,C_63),k2_enumset1(D_59,E_65,F_60,G_61)) = k5_enumset1(A_64,B_62,C_63,D_59,E_65,F_60,G_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_282,plain,(
    ! [G_61,D_59,A_13,E_65,B_14,F_60] : k5_enumset1(A_13,A_13,B_14,D_59,E_65,F_60,G_61) = k2_xboole_0(k2_tarski(A_13,B_14),k2_enumset1(D_59,E_65,F_60,G_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_258])).

tff(c_465,plain,(
    ! [E_83,F_84,A_81,G_80,B_79,D_82] : k2_xboole_0(k2_tarski(A_81,B_79),k2_enumset1(D_82,E_83,F_84,G_80)) = k4_enumset1(A_81,B_79,D_82,E_83,F_84,G_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_282])).

tff(c_988,plain,(
    ! [D_109,A_110,G_108,E_112,F_111] : k4_enumset1(A_110,A_110,D_109,E_112,F_111,G_108) = k2_xboole_0(k1_tarski(A_110),k2_enumset1(D_109,E_112,F_111,G_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_465])).

tff(c_1066,plain,(
    ! [A_110,A_15,B_16,C_17] : k4_enumset1(A_110,A_110,A_15,A_15,B_16,C_17) = k2_xboole_0(k1_tarski(A_110),k1_enumset1(A_15,B_16,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_988])).

tff(c_1085,plain,(
    ! [A_110,A_15,B_16,C_17] : k4_enumset1(A_110,A_110,A_15,A_15,B_16,C_17) = k2_enumset1(A_110,A_15,B_16,C_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1066])).

tff(c_16,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1087,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_16])).

tff(c_1090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1087])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.86/1.45  
% 2.86/1.45  %Foreground sorts:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Background operators:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Foreground operators:
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.45  
% 2.86/1.46  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.86/1.46  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.86/1.46  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.86/1.46  tff(f_39, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.86/1.46  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.86/1.46  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.86/1.46  tff(f_42, negated_conjecture, ~(![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 2.86/1.46  tff(c_10, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.46  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k1_tarski(A_1), k1_enumset1(B_2, C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.46  tff(c_6, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.46  tff(c_14, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k5_enumset1(A_22, A_22, B_23, C_24, D_25, E_26, F_27)=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.46  tff(c_8, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.46  tff(c_258, plain, (![B_62, G_61, D_59, E_65, C_63, F_60, A_64]: (k2_xboole_0(k1_enumset1(A_64, B_62, C_63), k2_enumset1(D_59, E_65, F_60, G_61))=k5_enumset1(A_64, B_62, C_63, D_59, E_65, F_60, G_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.46  tff(c_282, plain, (![G_61, D_59, A_13, E_65, B_14, F_60]: (k5_enumset1(A_13, A_13, B_14, D_59, E_65, F_60, G_61)=k2_xboole_0(k2_tarski(A_13, B_14), k2_enumset1(D_59, E_65, F_60, G_61)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_258])).
% 2.86/1.46  tff(c_465, plain, (![E_83, F_84, A_81, G_80, B_79, D_82]: (k2_xboole_0(k2_tarski(A_81, B_79), k2_enumset1(D_82, E_83, F_84, G_80))=k4_enumset1(A_81, B_79, D_82, E_83, F_84, G_80))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_282])).
% 2.86/1.46  tff(c_988, plain, (![D_109, A_110, G_108, E_112, F_111]: (k4_enumset1(A_110, A_110, D_109, E_112, F_111, G_108)=k2_xboole_0(k1_tarski(A_110), k2_enumset1(D_109, E_112, F_111, G_108)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_465])).
% 2.86/1.46  tff(c_1066, plain, (![A_110, A_15, B_16, C_17]: (k4_enumset1(A_110, A_110, A_15, A_15, B_16, C_17)=k2_xboole_0(k1_tarski(A_110), k1_enumset1(A_15, B_16, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_988])).
% 2.86/1.46  tff(c_1085, plain, (![A_110, A_15, B_16, C_17]: (k4_enumset1(A_110, A_110, A_15, A_15, B_16, C_17)=k2_enumset1(A_110, A_15, B_16, C_17))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1066])).
% 2.86/1.46  tff(c_16, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.86/1.46  tff(c_1087, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_16])).
% 2.86/1.46  tff(c_1090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1087])).
% 2.86/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.46  
% 2.86/1.46  Inference rules
% 2.86/1.46  ----------------------
% 2.86/1.46  #Ref     : 0
% 2.86/1.46  #Sup     : 253
% 2.86/1.46  #Fact    : 0
% 2.86/1.46  #Define  : 0
% 2.86/1.46  #Split   : 0
% 2.86/1.46  #Chain   : 0
% 2.86/1.46  #Close   : 0
% 2.86/1.46  
% 2.86/1.46  Ordering : KBO
% 2.86/1.46  
% 2.86/1.46  Simplification rules
% 2.86/1.46  ----------------------
% 2.86/1.46  #Subsume      : 31
% 2.86/1.46  #Demod        : 236
% 2.86/1.46  #Tautology    : 184
% 2.86/1.46  #SimpNegUnit  : 0
% 2.86/1.46  #BackRed      : 1
% 2.86/1.46  
% 2.86/1.46  #Partial instantiations: 0
% 2.86/1.46  #Strategies tried      : 1
% 2.86/1.46  
% 2.86/1.46  Timing (in seconds)
% 2.86/1.46  ----------------------
% 2.86/1.46  Preprocessing        : 0.27
% 2.86/1.46  Parsing              : 0.14
% 2.86/1.46  CNF conversion       : 0.02
% 2.86/1.46  Main loop            : 0.36
% 2.86/1.46  Inferencing          : 0.16
% 2.86/1.46  Reduction            : 0.14
% 2.86/1.46  Demodulation         : 0.11
% 2.86/1.46  BG Simplification    : 0.02
% 2.86/1.46  Subsumption          : 0.03
% 2.86/1.46  Abstraction          : 0.03
% 2.86/1.46  MUC search           : 0.00
% 2.86/1.46  Cooper               : 0.00
% 2.86/1.46  Total                : 0.65
% 2.86/1.46  Index Insertion      : 0.00
% 2.86/1.46  Index Deletion       : 0.00
% 2.86/1.46  Index Matching       : 0.00
% 2.86/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
