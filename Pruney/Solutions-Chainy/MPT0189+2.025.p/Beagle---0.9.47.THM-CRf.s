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
% DateTime   : Thu Dec  3 09:46:53 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  62 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  46 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_4,plain,(
    ! [B_10,C_11,A_9] : k1_enumset1(B_10,C_11,A_9) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_27,B_28,C_29,D_30] : k3_enumset1(A_27,A_27,B_28,C_29,D_30) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,A_24,B_25,C_26) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_287,plain,(
    ! [D_81,B_78,E_79,A_80,C_82] : k2_xboole_0(k2_enumset1(A_80,B_78,C_82,D_81),k1_tarski(E_79)) = k3_enumset1(A_80,B_78,C_82,D_81,E_79) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_305,plain,(
    ! [A_24,B_25,C_26,E_79] : k3_enumset1(A_24,A_24,B_25,C_26,E_79) = k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k1_tarski(E_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_287])).

tff(c_318,plain,(
    ! [A_89,B_90,C_91,E_92] : k2_xboole_0(k1_enumset1(A_89,B_90,C_91),k1_tarski(E_92)) = k2_enumset1(A_89,B_90,C_91,E_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_305])).

tff(c_429,plain,(
    ! [A_112,B_113,C_114,E_115] : k2_xboole_0(k1_enumset1(A_112,B_113,C_114),k1_tarski(E_115)) = k2_enumset1(B_113,C_114,A_112,E_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_318])).

tff(c_308,plain,(
    ! [A_24,B_25,C_26,E_79] : k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k1_tarski(E_79)) = k2_enumset1(A_24,B_25,C_26,E_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_305])).

tff(c_435,plain,(
    ! [B_113,C_114,A_112,E_115] : k2_enumset1(B_113,C_114,A_112,E_115) = k2_enumset1(A_112,B_113,C_114,E_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_308])).

tff(c_6,plain,(
    ! [A_12,C_14,B_13,D_15] : k2_enumset1(A_12,C_14,B_13,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_435,c_25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:44:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.18/1.27  
% 2.18/1.27  %Foreground sorts:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Background operators:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Foreground operators:
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.27  
% 2.18/1.28  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 2.18/1.28  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.18/1.28  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.18/1.28  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.18/1.28  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 2.18/1.28  tff(f_50, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 2.18/1.28  tff(c_4, plain, (![B_10, C_11, A_9]: (k1_enumset1(B_10, C_11, A_9)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.28  tff(c_16, plain, (![A_27, B_28, C_29, D_30]: (k3_enumset1(A_27, A_27, B_28, C_29, D_30)=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.28  tff(c_14, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, A_24, B_25, C_26)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.28  tff(c_287, plain, (![D_81, B_78, E_79, A_80, C_82]: (k2_xboole_0(k2_enumset1(A_80, B_78, C_82, D_81), k1_tarski(E_79))=k3_enumset1(A_80, B_78, C_82, D_81, E_79))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.28  tff(c_305, plain, (![A_24, B_25, C_26, E_79]: (k3_enumset1(A_24, A_24, B_25, C_26, E_79)=k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k1_tarski(E_79)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_287])).
% 2.18/1.28  tff(c_318, plain, (![A_89, B_90, C_91, E_92]: (k2_xboole_0(k1_enumset1(A_89, B_90, C_91), k1_tarski(E_92))=k2_enumset1(A_89, B_90, C_91, E_92))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_305])).
% 2.18/1.28  tff(c_429, plain, (![A_112, B_113, C_114, E_115]: (k2_xboole_0(k1_enumset1(A_112, B_113, C_114), k1_tarski(E_115))=k2_enumset1(B_113, C_114, A_112, E_115))), inference(superposition, [status(thm), theory('equality')], [c_4, c_318])).
% 2.18/1.28  tff(c_308, plain, (![A_24, B_25, C_26, E_79]: (k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k1_tarski(E_79))=k2_enumset1(A_24, B_25, C_26, E_79))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_305])).
% 2.18/1.28  tff(c_435, plain, (![B_113, C_114, A_112, E_115]: (k2_enumset1(B_113, C_114, A_112, E_115)=k2_enumset1(A_112, B_113, C_114, E_115))), inference(superposition, [status(thm), theory('equality')], [c_429, c_308])).
% 2.18/1.28  tff(c_6, plain, (![A_12, C_14, B_13, D_15]: (k2_enumset1(A_12, C_14, B_13, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.28  tff(c_24, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.28  tff(c_25, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_24])).
% 2.18/1.28  tff(c_465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_435, c_435, c_25])).
% 2.18/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  Inference rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Ref     : 0
% 2.18/1.28  #Sup     : 102
% 2.18/1.28  #Fact    : 0
% 2.18/1.28  #Define  : 0
% 2.18/1.28  #Split   : 0
% 2.18/1.28  #Chain   : 0
% 2.18/1.28  #Close   : 0
% 2.18/1.28  
% 2.18/1.28  Ordering : KBO
% 2.18/1.28  
% 2.18/1.28  Simplification rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Subsume      : 4
% 2.18/1.28  #Demod        : 62
% 2.18/1.28  #Tautology    : 82
% 2.18/1.28  #SimpNegUnit  : 0
% 2.18/1.28  #BackRed      : 1
% 2.18/1.28  
% 2.18/1.28  #Partial instantiations: 0
% 2.18/1.28  #Strategies tried      : 1
% 2.18/1.28  
% 2.18/1.28  Timing (in seconds)
% 2.18/1.28  ----------------------
% 2.18/1.28  Preprocessing        : 0.30
% 2.18/1.28  Parsing              : 0.16
% 2.18/1.28  CNF conversion       : 0.02
% 2.18/1.28  Main loop            : 0.22
% 2.18/1.28  Inferencing          : 0.09
% 2.18/1.28  Reduction            : 0.09
% 2.18/1.28  Demodulation         : 0.07
% 2.18/1.28  BG Simplification    : 0.02
% 2.18/1.28  Subsumption          : 0.03
% 2.18/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.55
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
