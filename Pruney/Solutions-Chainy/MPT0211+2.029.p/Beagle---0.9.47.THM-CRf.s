%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:18 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  27 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_18,plain,(
    ! [A_30,C_32,B_31,D_33] : k2_enumset1(A_30,C_32,B_31,D_33) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_73,B_74,C_75] : k2_enumset1(A_73,A_73,B_74,C_75) = k1_enumset1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_450,plain,(
    ! [B_116,D_117,C_118,A_119] : k2_enumset1(B_116,D_117,C_118,A_119) = k2_enumset1(A_119,B_116,C_118,D_117) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_659,plain,(
    ! [A_123,C_124,B_125] : k2_enumset1(A_123,C_124,B_125,A_123) = k1_enumset1(A_123,B_125,C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_450])).

tff(c_999,plain,(
    ! [D_134,B_135,C_136] : k2_enumset1(D_134,B_135,C_136,D_134) = k1_enumset1(D_134,B_135,C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_659])).

tff(c_564,plain,(
    ! [A_73,C_75,B_74] : k2_enumset1(A_73,C_75,B_74,A_73) = k1_enumset1(A_73,B_74,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_450])).

tff(c_1011,plain,(
    ! [D_134,C_136,B_135] : k1_enumset1(D_134,C_136,B_135) = k1_enumset1(D_134,B_135,C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_564])).

tff(c_24,plain,(
    ! [D_45,C_44,B_43,A_42] : k2_enumset1(D_45,C_44,B_43,A_42) = k2_enumset1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(C_23,D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_45,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_46,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_18,c_24,c_45])).

tff(c_1120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:19:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.46  
% 3.14/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.46  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.14/1.46  
% 3.14/1.46  %Foreground sorts:
% 3.14/1.46  
% 3.14/1.46  
% 3.14/1.46  %Background operators:
% 3.14/1.46  
% 3.14/1.46  
% 3.14/1.46  %Foreground operators:
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.46  
% 3.30/1.47  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 3.30/1.47  tff(f_63, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.30/1.47  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.30/1.47  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.30/1.47  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.30/1.47  tff(f_70, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.30/1.47  tff(c_18, plain, (![A_30, C_32, B_31, D_33]: (k2_enumset1(A_30, C_32, B_31, D_33)=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.47  tff(c_38, plain, (![A_73, B_74, C_75]: (k2_enumset1(A_73, A_73, B_74, C_75)=k1_enumset1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.30/1.47  tff(c_450, plain, (![B_116, D_117, C_118, A_119]: (k2_enumset1(B_116, D_117, C_118, A_119)=k2_enumset1(A_119, B_116, C_118, D_117))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.47  tff(c_659, plain, (![A_123, C_124, B_125]: (k2_enumset1(A_123, C_124, B_125, A_123)=k1_enumset1(A_123, B_125, C_124))), inference(superposition, [status(thm), theory('equality')], [c_38, c_450])).
% 3.30/1.47  tff(c_999, plain, (![D_134, B_135, C_136]: (k2_enumset1(D_134, B_135, C_136, D_134)=k1_enumset1(D_134, B_135, C_136))), inference(superposition, [status(thm), theory('equality')], [c_18, c_659])).
% 3.30/1.47  tff(c_564, plain, (![A_73, C_75, B_74]: (k2_enumset1(A_73, C_75, B_74, A_73)=k1_enumset1(A_73, B_74, C_75))), inference(superposition, [status(thm), theory('equality')], [c_38, c_450])).
% 3.30/1.47  tff(c_1011, plain, (![D_134, C_136, B_135]: (k1_enumset1(D_134, C_136, B_135)=k1_enumset1(D_134, B_135, C_136))), inference(superposition, [status(thm), theory('equality')], [c_999, c_564])).
% 3.30/1.47  tff(c_24, plain, (![D_45, C_44, B_43, A_42]: (k2_enumset1(D_45, C_44, B_43, A_42)=k2_enumset1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.30/1.47  tff(c_14, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(C_23, D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.47  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.30/1.47  tff(c_45, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 3.30/1.47  tff(c_46, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_18, c_24, c_45])).
% 3.30/1.47  tff(c_1120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1011, c_46])).
% 3.30/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.47  
% 3.30/1.47  Inference rules
% 3.30/1.47  ----------------------
% 3.30/1.47  #Ref     : 0
% 3.30/1.47  #Sup     : 274
% 3.30/1.47  #Fact    : 0
% 3.30/1.47  #Define  : 0
% 3.30/1.47  #Split   : 0
% 3.30/1.47  #Chain   : 0
% 3.30/1.47  #Close   : 0
% 3.30/1.47  
% 3.30/1.47  Ordering : KBO
% 3.30/1.47  
% 3.30/1.47  Simplification rules
% 3.30/1.47  ----------------------
% 3.30/1.47  #Subsume      : 7
% 3.30/1.47  #Demod        : 92
% 3.30/1.47  #Tautology    : 143
% 3.30/1.47  #SimpNegUnit  : 0
% 3.30/1.47  #BackRed      : 1
% 3.30/1.47  
% 3.30/1.47  #Partial instantiations: 0
% 3.30/1.47  #Strategies tried      : 1
% 3.30/1.47  
% 3.30/1.47  Timing (in seconds)
% 3.30/1.47  ----------------------
% 3.30/1.48  Preprocessing        : 0.34
% 3.30/1.48  Parsing              : 0.18
% 3.30/1.48  CNF conversion       : 0.02
% 3.30/1.48  Main loop            : 0.36
% 3.30/1.48  Inferencing          : 0.12
% 3.30/1.48  Reduction            : 0.15
% 3.30/1.48  Demodulation         : 0.13
% 3.30/1.48  BG Simplification    : 0.03
% 3.30/1.48  Subsumption          : 0.05
% 3.30/1.48  Abstraction          : 0.02
% 3.30/1.48  MUC search           : 0.00
% 3.30/1.48  Cooper               : 0.00
% 3.30/1.48  Total                : 0.73
% 3.30/1.48  Index Insertion      : 0.00
% 3.30/1.48  Index Deletion       : 0.00
% 3.30/1.48  Index Matching       : 0.00
% 3.30/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
