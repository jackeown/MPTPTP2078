%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:20 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  24 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_460,plain,(
    ! [C_123,D_124,B_125,A_126] : k2_enumset1(C_123,D_124,B_125,A_126) = k2_enumset1(A_126,B_125,C_123,D_124) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [A_80,B_81,C_82] : k2_enumset1(A_80,A_80,B_81,C_82) = k1_enumset1(A_80,B_81,C_82) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_875,plain,(
    ! [A_138,B_139,D_140] : k2_enumset1(A_138,B_139,D_140,D_140) = k1_enumset1(D_140,B_139,A_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_40])).

tff(c_516,plain,(
    ! [C_123,D_124,B_125] : k2_enumset1(C_123,D_124,B_125,B_125) = k1_enumset1(B_125,C_123,D_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_40])).

tff(c_887,plain,(
    ! [D_140,B_139,A_138] : k1_enumset1(D_140,B_139,A_138) = k1_enumset1(D_140,A_138,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_516])).

tff(c_16,plain,(
    ! [B_21,D_23,C_22,A_20] : k2_enumset1(B_21,D_23,C_22,A_20) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_47,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_48,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16,c_16,c_47])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:33:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.46  
% 2.81/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.46  %$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.81/1.46  
% 2.81/1.46  %Foreground sorts:
% 2.81/1.46  
% 2.81/1.46  
% 2.81/1.46  %Background operators:
% 2.81/1.46  
% 2.81/1.46  
% 2.81/1.46  %Foreground operators:
% 2.81/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.46  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.46  
% 3.12/1.47  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_enumset1)).
% 3.12/1.47  tff(f_65, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.12/1.47  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.12/1.47  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.12/1.47  tff(f_72, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.12/1.47  tff(c_460, plain, (![C_123, D_124, B_125, A_126]: (k2_enumset1(C_123, D_124, B_125, A_126)=k2_enumset1(A_126, B_125, C_123, D_124))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.12/1.47  tff(c_40, plain, (![A_80, B_81, C_82]: (k2_enumset1(A_80, A_80, B_81, C_82)=k1_enumset1(A_80, B_81, C_82))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.12/1.47  tff(c_875, plain, (![A_138, B_139, D_140]: (k2_enumset1(A_138, B_139, D_140, D_140)=k1_enumset1(D_140, B_139, A_138))), inference(superposition, [status(thm), theory('equality')], [c_460, c_40])).
% 3.12/1.47  tff(c_516, plain, (![C_123, D_124, B_125]: (k2_enumset1(C_123, D_124, B_125, B_125)=k1_enumset1(B_125, C_123, D_124))), inference(superposition, [status(thm), theory('equality')], [c_460, c_40])).
% 3.12/1.47  tff(c_887, plain, (![D_140, B_139, A_138]: (k1_enumset1(D_140, B_139, A_138)=k1_enumset1(D_140, A_138, B_139))), inference(superposition, [status(thm), theory('equality')], [c_875, c_516])).
% 3.12/1.47  tff(c_16, plain, (![B_21, D_23, C_22, A_20]: (k2_enumset1(B_21, D_23, C_22, A_20)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.47  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.47  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.12/1.47  tff(c_47, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 3.12/1.47  tff(c_48, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16, c_16, c_47])).
% 3.12/1.47  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_887, c_48])).
% 3.12/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.47  
% 3.12/1.47  Inference rules
% 3.12/1.47  ----------------------
% 3.12/1.47  #Ref     : 0
% 3.12/1.47  #Sup     : 246
% 3.12/1.47  #Fact    : 0
% 3.12/1.47  #Define  : 0
% 3.12/1.47  #Split   : 0
% 3.12/1.47  #Chain   : 0
% 3.12/1.47  #Close   : 0
% 3.12/1.47  
% 3.12/1.47  Ordering : KBO
% 3.12/1.47  
% 3.12/1.47  Simplification rules
% 3.12/1.47  ----------------------
% 3.12/1.47  #Subsume      : 7
% 3.12/1.47  #Demod        : 57
% 3.12/1.47  #Tautology    : 108
% 3.12/1.47  #SimpNegUnit  : 0
% 3.12/1.47  #BackRed      : 1
% 3.12/1.47  
% 3.12/1.47  #Partial instantiations: 0
% 3.12/1.47  #Strategies tried      : 1
% 3.12/1.47  
% 3.12/1.47  Timing (in seconds)
% 3.12/1.47  ----------------------
% 3.17/1.47  Preprocessing        : 0.35
% 3.17/1.47  Parsing              : 0.19
% 3.17/1.47  CNF conversion       : 0.02
% 3.17/1.47  Main loop            : 0.33
% 3.17/1.47  Inferencing          : 0.11
% 3.17/1.47  Reduction            : 0.14
% 3.17/1.47  Demodulation         : 0.12
% 3.17/1.47  BG Simplification    : 0.03
% 3.17/1.47  Subsumption          : 0.05
% 3.17/1.47  Abstraction          : 0.02
% 3.17/1.47  MUC search           : 0.00
% 3.17/1.47  Cooper               : 0.00
% 3.17/1.47  Total                : 0.70
% 3.17/1.47  Index Insertion      : 0.00
% 3.17/1.47  Index Deletion       : 0.00
% 3.17/1.47  Index Matching       : 0.00
% 3.17/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
