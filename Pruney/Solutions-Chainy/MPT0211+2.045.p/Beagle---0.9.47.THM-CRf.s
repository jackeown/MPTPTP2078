%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:20 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  32 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_379,plain,(
    ! [D_108,C_109,B_110,A_111] : k2_enumset1(D_108,C_109,B_110,A_111) = k2_enumset1(A_111,B_110,C_109,D_108) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_68,B_69,C_70] : k2_enumset1(A_68,A_68,B_69,C_70) = k1_enumset1(A_68,B_69,C_70) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_209,plain,(
    ! [B_98,D_99,C_100,A_101] : k2_enumset1(B_98,D_99,C_100,A_101) = k2_enumset1(A_101,B_98,C_100,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_271,plain,(
    ! [A_68,C_70,B_69] : k2_enumset1(A_68,C_70,B_69,A_68) = k1_enumset1(A_68,B_69,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_209])).

tff(c_993,plain,(
    ! [A_133,B_134,C_135] : k2_enumset1(A_133,B_134,C_135,A_133) = k1_enumset1(A_133,B_134,C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_271])).

tff(c_1019,plain,(
    ! [A_133,C_135,B_134] : k1_enumset1(A_133,C_135,B_134) = k1_enumset1(A_133,B_134,C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_271])).

tff(c_162,plain,(
    ! [D_94,B_95,C_96,A_97] : k2_enumset1(D_94,B_95,C_96,A_97) = k2_enumset1(A_97,B_95,C_96,D_94) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [D_94,B_95,C_96] : k2_enumset1(D_94,B_95,C_96,B_95) = k1_enumset1(B_95,C_96,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_36])).

tff(c_460,plain,(
    ! [B_95,C_96,D_94] : k2_enumset1(B_95,C_96,B_95,D_94) = k1_enumset1(B_95,C_96,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_379])).

tff(c_20,plain,(
    ! [D_31,C_30,B_29,A_28] : k2_enumset1(D_31,C_30,B_29,A_28) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_44,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_43])).

tff(c_880,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_44])).

tff(c_1096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_880])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:40:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.42  %$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.88/1.42  
% 2.88/1.42  %Foreground sorts:
% 2.88/1.42  
% 2.88/1.42  
% 2.88/1.42  %Background operators:
% 2.88/1.42  
% 2.88/1.42  
% 2.88/1.42  %Foreground operators:
% 2.88/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.88/1.42  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.88/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.42  
% 2.88/1.42  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 2.88/1.42  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.88/1.42  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 2.88/1.42  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 2.88/1.42  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.88/1.42  tff(f_68, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 2.88/1.42  tff(c_379, plain, (![D_108, C_109, B_110, A_111]: (k2_enumset1(D_108, C_109, B_110, A_111)=k2_enumset1(A_111, B_110, C_109, D_108))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.88/1.42  tff(c_36, plain, (![A_68, B_69, C_70]: (k2_enumset1(A_68, A_68, B_69, C_70)=k1_enumset1(A_68, B_69, C_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.42  tff(c_209, plain, (![B_98, D_99, C_100, A_101]: (k2_enumset1(B_98, D_99, C_100, A_101)=k2_enumset1(A_101, B_98, C_100, D_99))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.42  tff(c_271, plain, (![A_68, C_70, B_69]: (k2_enumset1(A_68, C_70, B_69, A_68)=k1_enumset1(A_68, B_69, C_70))), inference(superposition, [status(thm), theory('equality')], [c_36, c_209])).
% 2.88/1.42  tff(c_993, plain, (![A_133, B_134, C_135]: (k2_enumset1(A_133, B_134, C_135, A_133)=k1_enumset1(A_133, B_134, C_135))), inference(superposition, [status(thm), theory('equality')], [c_379, c_271])).
% 2.88/1.42  tff(c_1019, plain, (![A_133, C_135, B_134]: (k1_enumset1(A_133, C_135, B_134)=k1_enumset1(A_133, B_134, C_135))), inference(superposition, [status(thm), theory('equality')], [c_993, c_271])).
% 2.88/1.42  tff(c_162, plain, (![D_94, B_95, C_96, A_97]: (k2_enumset1(D_94, B_95, C_96, A_97)=k2_enumset1(A_97, B_95, C_96, D_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.42  tff(c_178, plain, (![D_94, B_95, C_96]: (k2_enumset1(D_94, B_95, C_96, B_95)=k1_enumset1(B_95, C_96, D_94))), inference(superposition, [status(thm), theory('equality')], [c_162, c_36])).
% 2.88/1.42  tff(c_460, plain, (![B_95, C_96, D_94]: (k2_enumset1(B_95, C_96, B_95, D_94)=k1_enumset1(B_95, C_96, D_94))), inference(superposition, [status(thm), theory('equality')], [c_178, c_379])).
% 2.88/1.42  tff(c_20, plain, (![D_31, C_30, B_29, A_28]: (k2_enumset1(D_31, C_30, B_29, A_28)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.88/1.42  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.42  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.88/1.42  tff(c_43, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 2.88/1.42  tff(c_44, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_43])).
% 2.88/1.42  tff(c_880, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_44])).
% 2.88/1.42  tff(c_1096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1019, c_880])).
% 2.88/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.42  
% 2.88/1.42  Inference rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Ref     : 0
% 2.88/1.42  #Sup     : 268
% 2.88/1.42  #Fact    : 0
% 2.88/1.42  #Define  : 0
% 2.88/1.42  #Split   : 0
% 2.88/1.42  #Chain   : 0
% 2.88/1.42  #Close   : 0
% 2.88/1.42  
% 2.88/1.42  Ordering : KBO
% 2.88/1.42  
% 2.88/1.42  Simplification rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Subsume      : 19
% 2.88/1.42  #Demod        : 93
% 2.88/1.42  #Tautology    : 143
% 2.88/1.42  #SimpNegUnit  : 0
% 2.88/1.42  #BackRed      : 2
% 2.88/1.42  
% 2.88/1.42  #Partial instantiations: 0
% 2.88/1.42  #Strategies tried      : 1
% 2.88/1.42  
% 2.88/1.42  Timing (in seconds)
% 2.88/1.43  ----------------------
% 2.88/1.43  Preprocessing        : 0.33
% 2.88/1.43  Parsing              : 0.17
% 2.88/1.43  CNF conversion       : 0.02
% 2.88/1.43  Main loop            : 0.35
% 2.88/1.43  Inferencing          : 0.12
% 2.88/1.43  Reduction            : 0.15
% 2.88/1.43  Demodulation         : 0.12
% 2.88/1.43  BG Simplification    : 0.02
% 2.88/1.43  Subsumption          : 0.05
% 2.88/1.43  Abstraction          : 0.02
% 2.88/1.43  MUC search           : 0.00
% 2.88/1.43  Cooper               : 0.00
% 2.88/1.43  Total                : 0.70
% 2.88/1.43  Index Insertion      : 0.00
% 2.88/1.43  Index Deletion       : 0.00
% 2.88/1.43  Index Matching       : 0.00
% 2.88/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
