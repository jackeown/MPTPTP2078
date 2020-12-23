%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:20 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   38 (  58 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  40 expanded)
%              Number of equality atoms :   19 (  39 expanded)
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

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_34,plain,(
    ! [A_60,B_61,C_62] : k2_enumset1(A_60,A_60,B_61,C_62) = k1_enumset1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_205,plain,(
    ! [C_96,D_97,B_98,A_99] : k2_enumset1(C_96,D_97,B_98,A_99) = k2_enumset1(A_99,B_98,C_96,D_97) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_484,plain,(
    ! [C_111,B_112,A_113] : k2_enumset1(C_111,B_112,A_113,A_113) = k1_enumset1(A_113,B_112,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_205])).

tff(c_233,plain,(
    ! [C_96,D_97,B_98] : k2_enumset1(C_96,D_97,B_98,B_98) = k1_enumset1(B_98,C_96,D_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_34])).

tff(c_490,plain,(
    ! [A_113,C_111,B_112] : k1_enumset1(A_113,C_111,B_112) = k1_enumset1(A_113,B_112,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_233])).

tff(c_16,plain,(
    ! [B_21,D_23,C_22,A_20] : k2_enumset1(B_21,D_23,C_22,A_20) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_503,plain,(
    ! [A_113,C_111,B_112] : k2_enumset1(A_113,C_111,A_113,B_112) = k1_enumset1(A_113,B_112,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_16])).

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

tff(c_712,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_44])).

tff(c_1300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_503,c_712])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:55:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.54  
% 3.03/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.54  %$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.03/1.54  
% 3.03/1.54  %Foreground sorts:
% 3.03/1.54  
% 3.03/1.54  
% 3.03/1.54  %Background operators:
% 3.03/1.54  
% 3.03/1.54  
% 3.03/1.54  %Foreground operators:
% 3.03/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.03/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.03/1.54  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.03/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.03/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.03/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.03/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.54  
% 3.03/1.55  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.03/1.55  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 3.03/1.55  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 3.03/1.55  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.03/1.55  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.03/1.55  tff(f_68, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.03/1.55  tff(c_34, plain, (![A_60, B_61, C_62]: (k2_enumset1(A_60, A_60, B_61, C_62)=k1_enumset1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.03/1.55  tff(c_205, plain, (![C_96, D_97, B_98, A_99]: (k2_enumset1(C_96, D_97, B_98, A_99)=k2_enumset1(A_99, B_98, C_96, D_97))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.03/1.55  tff(c_484, plain, (![C_111, B_112, A_113]: (k2_enumset1(C_111, B_112, A_113, A_113)=k1_enumset1(A_113, B_112, C_111))), inference(superposition, [status(thm), theory('equality')], [c_34, c_205])).
% 3.03/1.55  tff(c_233, plain, (![C_96, D_97, B_98]: (k2_enumset1(C_96, D_97, B_98, B_98)=k1_enumset1(B_98, C_96, D_97))), inference(superposition, [status(thm), theory('equality')], [c_205, c_34])).
% 3.03/1.55  tff(c_490, plain, (![A_113, C_111, B_112]: (k1_enumset1(A_113, C_111, B_112)=k1_enumset1(A_113, B_112, C_111))), inference(superposition, [status(thm), theory('equality')], [c_484, c_233])).
% 3.03/1.55  tff(c_16, plain, (![B_21, D_23, C_22, A_20]: (k2_enumset1(B_21, D_23, C_22, A_20)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.03/1.55  tff(c_503, plain, (![A_113, C_111, B_112]: (k2_enumset1(A_113, C_111, A_113, B_112)=k1_enumset1(A_113, B_112, C_111))), inference(superposition, [status(thm), theory('equality')], [c_484, c_16])).
% 3.03/1.55  tff(c_20, plain, (![D_31, C_30, B_29, A_28]: (k2_enumset1(D_31, C_30, B_29, A_28)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.03/1.55  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.03/1.55  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.03/1.55  tff(c_43, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 3.03/1.55  tff(c_44, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_43])).
% 3.03/1.55  tff(c_712, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_44])).
% 3.03/1.55  tff(c_1300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_490, c_503, c_712])).
% 3.03/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.55  
% 3.03/1.55  Inference rules
% 3.03/1.55  ----------------------
% 3.03/1.55  #Ref     : 0
% 3.03/1.55  #Sup     : 320
% 3.03/1.55  #Fact    : 0
% 3.03/1.55  #Define  : 0
% 3.03/1.55  #Split   : 0
% 3.03/1.55  #Chain   : 0
% 3.03/1.55  #Close   : 0
% 3.03/1.55  
% 3.03/1.55  Ordering : KBO
% 3.03/1.55  
% 3.03/1.55  Simplification rules
% 3.03/1.55  ----------------------
% 3.03/1.55  #Subsume      : 12
% 3.03/1.55  #Demod        : 126
% 3.03/1.55  #Tautology    : 163
% 3.03/1.55  #SimpNegUnit  : 0
% 3.03/1.55  #BackRed      : 1
% 3.03/1.55  
% 3.03/1.55  #Partial instantiations: 0
% 3.03/1.55  #Strategies tried      : 1
% 3.03/1.55  
% 3.03/1.55  Timing (in seconds)
% 3.03/1.55  ----------------------
% 3.03/1.55  Preprocessing        : 0.31
% 3.03/1.55  Parsing              : 0.17
% 3.03/1.55  CNF conversion       : 0.02
% 3.03/1.55  Main loop            : 0.38
% 3.03/1.55  Inferencing          : 0.13
% 3.03/1.55  Reduction            : 0.16
% 3.03/1.55  Demodulation         : 0.13
% 3.03/1.55  BG Simplification    : 0.03
% 3.03/1.55  Subsumption          : 0.05
% 3.03/1.55  Abstraction          : 0.02
% 3.03/1.55  MUC search           : 0.00
% 3.03/1.55  Cooper               : 0.00
% 3.03/1.55  Total                : 0.71
% 3.03/1.55  Index Insertion      : 0.00
% 3.03/1.55  Index Deletion       : 0.00
% 3.03/1.55  Index Matching       : 0.00
% 3.03/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
