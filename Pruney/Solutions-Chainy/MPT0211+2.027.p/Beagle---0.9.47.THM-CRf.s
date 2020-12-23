%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:18 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  32 expanded)
%              Number of equality atoms :   20 (  31 expanded)
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

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_24,plain,(
    ! [D_38,C_37,B_36,A_35] : k2_enumset1(D_38,C_37,B_36,A_35) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    ! [A_84,B_85,C_86] : k2_enumset1(A_84,A_84,B_85,C_86) = k1_enumset1(A_84,B_85,C_86) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_698,plain,(
    ! [B_133,D_134,C_135,A_136] : k2_enumset1(B_133,D_134,C_135,A_136) = k2_enumset1(A_136,B_133,C_135,D_134) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_919,plain,(
    ! [C_139,A_140,B_141] : k2_enumset1(C_139,A_140,B_141,A_140) = k1_enumset1(A_140,B_141,C_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_698])).

tff(c_975,plain,(
    ! [D_38,C_37,A_35] : k2_enumset1(D_38,C_37,D_38,A_35) = k1_enumset1(D_38,C_37,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_919])).

tff(c_14,plain,(
    ! [C_16,B_15,A_14,D_17] : k2_enumset1(C_16,B_15,A_14,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1016,plain,(
    ! [C_142,D_143,A_144] : k2_enumset1(C_142,D_143,A_144,D_143) = k1_enumset1(D_143,C_142,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_919])).

tff(c_847,plain,(
    ! [C_86,A_84,B_85] : k2_enumset1(C_86,A_84,B_85,A_84) = k1_enumset1(A_84,B_85,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_698])).

tff(c_1022,plain,(
    ! [D_143,C_142,A_144] : k1_enumset1(D_143,C_142,A_144) = k1_enumset1(D_143,A_144,C_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_847])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20,D_21] : k2_xboole_0(k2_tarski(A_18,B_19),k2_tarski(C_20,D_21)) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_49,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_50,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_49])).

tff(c_1126,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_50])).

tff(c_1467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_1126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.40/1.53  
% 3.40/1.53  %Foreground sorts:
% 3.40/1.53  
% 3.40/1.53  
% 3.40/1.53  %Background operators:
% 3.40/1.53  
% 3.40/1.53  
% 3.40/1.53  %Foreground operators:
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.53  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.40/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.53  
% 3.61/1.54  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.61/1.54  tff(f_69, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.61/1.54  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.61/1.54  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l129_enumset1)).
% 3.61/1.54  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.61/1.54  tff(f_74, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.61/1.54  tff(c_24, plain, (![D_38, C_37, B_36, A_35]: (k2_enumset1(D_38, C_37, B_36, A_35)=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.61/1.54  tff(c_44, plain, (![A_84, B_85, C_86]: (k2_enumset1(A_84, A_84, B_85, C_86)=k1_enumset1(A_84, B_85, C_86))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.61/1.54  tff(c_698, plain, (![B_133, D_134, C_135, A_136]: (k2_enumset1(B_133, D_134, C_135, A_136)=k2_enumset1(A_136, B_133, C_135, D_134))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.61/1.54  tff(c_919, plain, (![C_139, A_140, B_141]: (k2_enumset1(C_139, A_140, B_141, A_140)=k1_enumset1(A_140, B_141, C_139))), inference(superposition, [status(thm), theory('equality')], [c_44, c_698])).
% 3.61/1.54  tff(c_975, plain, (![D_38, C_37, A_35]: (k2_enumset1(D_38, C_37, D_38, A_35)=k1_enumset1(D_38, C_37, A_35))), inference(superposition, [status(thm), theory('equality')], [c_24, c_919])).
% 3.61/1.54  tff(c_14, plain, (![C_16, B_15, A_14, D_17]: (k2_enumset1(C_16, B_15, A_14, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.61/1.54  tff(c_1016, plain, (![C_142, D_143, A_144]: (k2_enumset1(C_142, D_143, A_144, D_143)=k1_enumset1(D_143, C_142, A_144))), inference(superposition, [status(thm), theory('equality')], [c_14, c_919])).
% 3.61/1.54  tff(c_847, plain, (![C_86, A_84, B_85]: (k2_enumset1(C_86, A_84, B_85, A_84)=k1_enumset1(A_84, B_85, C_86))), inference(superposition, [status(thm), theory('equality')], [c_44, c_698])).
% 3.61/1.54  tff(c_1022, plain, (![D_143, C_142, A_144]: (k1_enumset1(D_143, C_142, A_144)=k1_enumset1(D_143, A_144, C_142))), inference(superposition, [status(thm), theory('equality')], [c_1016, c_847])).
% 3.61/1.54  tff(c_16, plain, (![A_18, B_19, C_20, D_21]: (k2_xboole_0(k2_tarski(A_18, B_19), k2_tarski(C_20, D_21))=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.61/1.54  tff(c_48, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.61/1.54  tff(c_49, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48])).
% 3.61/1.54  tff(c_50, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_49])).
% 3.61/1.54  tff(c_1126, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_50])).
% 3.61/1.54  tff(c_1467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_975, c_1126])).
% 3.61/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.54  
% 3.61/1.54  Inference rules
% 3.61/1.54  ----------------------
% 3.61/1.54  #Ref     : 0
% 3.61/1.54  #Sup     : 354
% 3.61/1.54  #Fact    : 0
% 3.61/1.54  #Define  : 0
% 3.61/1.54  #Split   : 0
% 3.61/1.54  #Chain   : 0
% 3.61/1.54  #Close   : 0
% 3.61/1.54  
% 3.61/1.54  Ordering : KBO
% 3.61/1.54  
% 3.61/1.54  Simplification rules
% 3.61/1.54  ----------------------
% 3.61/1.54  #Subsume      : 16
% 3.61/1.54  #Demod        : 164
% 3.61/1.54  #Tautology    : 200
% 3.61/1.54  #SimpNegUnit  : 0
% 3.61/1.54  #BackRed      : 2
% 3.61/1.54  
% 3.61/1.54  #Partial instantiations: 0
% 3.61/1.54  #Strategies tried      : 1
% 3.61/1.54  
% 3.61/1.54  Timing (in seconds)
% 3.61/1.54  ----------------------
% 3.61/1.54  Preprocessing        : 0.34
% 3.61/1.54  Parsing              : 0.18
% 3.61/1.54  CNF conversion       : 0.02
% 3.61/1.54  Main loop            : 0.43
% 3.61/1.54  Inferencing          : 0.15
% 3.61/1.54  Reduction            : 0.18
% 3.61/1.54  Demodulation         : 0.15
% 3.61/1.54  BG Simplification    : 0.03
% 3.61/1.54  Subsumption          : 0.06
% 3.61/1.54  Abstraction          : 0.03
% 3.61/1.54  MUC search           : 0.00
% 3.61/1.54  Cooper               : 0.00
% 3.61/1.54  Total                : 0.80
% 3.61/1.54  Index Insertion      : 0.00
% 3.61/1.54  Index Deletion       : 0.00
% 3.61/1.54  Index Matching       : 0.00
% 3.61/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
