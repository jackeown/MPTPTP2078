%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:17 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  27 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_309,plain,(
    ! [D_93,C_94,B_95,A_96] : k2_enumset1(D_93,C_94,B_95,A_96) = k2_enumset1(A_96,B_95,C_94,D_93) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_151,plain,(
    ! [A_82,D_83,C_84,B_85] : k2_enumset1(A_82,D_83,C_84,B_85) = k2_enumset1(A_82,B_85,C_84,D_83) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_61,B_62,C_63] : k2_enumset1(A_61,A_61,B_62,C_63) = k1_enumset1(A_61,B_62,C_63) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_167,plain,(
    ! [B_85,D_83,C_84] : k2_enumset1(B_85,D_83,C_84,B_85) = k1_enumset1(B_85,C_84,D_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_32])).

tff(c_1044,plain,(
    ! [A_125,B_126,C_127] : k2_enumset1(A_125,B_126,C_127,A_125) = k1_enumset1(A_125,B_126,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_167])).

tff(c_1078,plain,(
    ! [A_125,C_127,B_126] : k1_enumset1(A_125,C_127,B_126) = k1_enumset1(A_125,B_126,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_167])).

tff(c_14,plain,(
    ! [B_21,D_23,C_22,A_20] : k2_enumset1(B_21,D_23,C_22,A_20) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_38,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14,c_14,c_37])).

tff(c_1172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.53  
% 3.21/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.53  %$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.21/1.53  
% 3.21/1.53  %Foreground sorts:
% 3.21/1.53  
% 3.21/1.53  
% 3.21/1.53  %Background operators:
% 3.21/1.53  
% 3.21/1.53  
% 3.21/1.53  %Foreground operators:
% 3.21/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.53  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.21/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.53  
% 3.21/1.54  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.21/1.54  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 3.21/1.54  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.21/1.54  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 3.21/1.54  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.21/1.54  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.21/1.54  tff(c_309, plain, (![D_93, C_94, B_95, A_96]: (k2_enumset1(D_93, C_94, B_95, A_96)=k2_enumset1(A_96, B_95, C_94, D_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.54  tff(c_151, plain, (![A_82, D_83, C_84, B_85]: (k2_enumset1(A_82, D_83, C_84, B_85)=k2_enumset1(A_82, B_85, C_84, D_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.54  tff(c_32, plain, (![A_61, B_62, C_63]: (k2_enumset1(A_61, A_61, B_62, C_63)=k1_enumset1(A_61, B_62, C_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.54  tff(c_167, plain, (![B_85, D_83, C_84]: (k2_enumset1(B_85, D_83, C_84, B_85)=k1_enumset1(B_85, C_84, D_83))), inference(superposition, [status(thm), theory('equality')], [c_151, c_32])).
% 3.21/1.54  tff(c_1044, plain, (![A_125, B_126, C_127]: (k2_enumset1(A_125, B_126, C_127, A_125)=k1_enumset1(A_125, B_126, C_127))), inference(superposition, [status(thm), theory('equality')], [c_309, c_167])).
% 3.21/1.54  tff(c_1078, plain, (![A_125, C_127, B_126]: (k1_enumset1(A_125, C_127, B_126)=k1_enumset1(A_125, B_126, C_127))), inference(superposition, [status(thm), theory('equality')], [c_1044, c_167])).
% 3.21/1.54  tff(c_14, plain, (![B_21, D_23, C_22, A_20]: (k2_enumset1(B_21, D_23, C_22, A_20)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.54  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.21/1.54  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.21/1.54  tff(c_37, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 3.21/1.54  tff(c_38, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14, c_14, c_37])).
% 3.21/1.54  tff(c_1172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1078, c_38])).
% 3.21/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.54  
% 3.21/1.54  Inference rules
% 3.21/1.54  ----------------------
% 3.21/1.54  #Ref     : 0
% 3.21/1.54  #Sup     : 284
% 3.21/1.54  #Fact    : 0
% 3.21/1.54  #Define  : 0
% 3.21/1.54  #Split   : 0
% 3.21/1.54  #Chain   : 0
% 3.21/1.54  #Close   : 0
% 3.21/1.54  
% 3.21/1.54  Ordering : KBO
% 3.21/1.54  
% 3.21/1.54  Simplification rules
% 3.21/1.54  ----------------------
% 3.21/1.54  #Subsume      : 19
% 3.21/1.54  #Demod        : 110
% 3.21/1.54  #Tautology    : 158
% 3.21/1.54  #SimpNegUnit  : 0
% 3.21/1.54  #BackRed      : 1
% 3.21/1.54  
% 3.21/1.54  #Partial instantiations: 0
% 3.21/1.54  #Strategies tried      : 1
% 3.21/1.54  
% 3.21/1.54  Timing (in seconds)
% 3.21/1.54  ----------------------
% 3.21/1.54  Preprocessing        : 0.34
% 3.21/1.54  Parsing              : 0.19
% 3.21/1.54  CNF conversion       : 0.02
% 3.21/1.54  Main loop            : 0.36
% 3.21/1.54  Inferencing          : 0.13
% 3.21/1.54  Reduction            : 0.15
% 3.21/1.54  Demodulation         : 0.12
% 3.21/1.54  BG Simplification    : 0.02
% 3.21/1.54  Subsumption          : 0.05
% 3.21/1.54  Abstraction          : 0.02
% 3.21/1.54  MUC search           : 0.00
% 3.21/1.54  Cooper               : 0.00
% 3.21/1.54  Total                : 0.72
% 3.21/1.54  Index Insertion      : 0.00
% 3.21/1.54  Index Deletion       : 0.00
% 3.21/1.54  Index Matching       : 0.00
% 3.21/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
