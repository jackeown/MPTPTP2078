%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:17 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  35 expanded)
%              Number of equality atoms :   21 (  34 expanded)
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

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_311,plain,(
    ! [D_98,C_99,B_100,A_101] : k2_enumset1(D_98,C_99,B_100,A_101) = k2_enumset1(A_101,B_100,C_99,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_61,B_62,C_63] : k2_enumset1(A_61,A_61,B_62,C_63) = k1_enumset1(A_61,B_62,C_63) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_359,plain,(
    ! [D_98,C_99,B_100] : k2_enumset1(D_98,C_99,B_100,B_100) = k1_enumset1(B_100,C_99,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_32])).

tff(c_565,plain,(
    ! [B_108,D_109,C_110,A_111] : k2_enumset1(B_108,D_109,C_110,A_111) = k2_enumset1(A_111,B_108,C_110,D_109) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1075,plain,(
    ! [B_134,D_135,C_136] : k2_enumset1(B_134,D_135,B_134,C_136) = k1_enumset1(B_134,C_136,D_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_565])).

tff(c_14,plain,(
    ! [D_22,B_20,C_21,A_19] : k2_enumset1(D_22,B_20,C_21,A_19) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_482,plain,(
    ! [D_105,C_106,B_107] : k2_enumset1(D_105,C_106,B_107,B_107) = k1_enumset1(B_107,C_106,D_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_32])).

tff(c_550,plain,(
    ! [A_19,B_20,D_22] : k2_enumset1(A_19,B_20,A_19,D_22) = k1_enumset1(A_19,B_20,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_482])).

tff(c_1085,plain,(
    ! [B_134,D_135,C_136] : k1_enumset1(B_134,D_135,C_136) = k1_enumset1(B_134,C_136,D_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_550])).

tff(c_16,plain,(
    ! [D_26,C_25,B_24,A_23] : k2_enumset1(D_26,C_25,B_24,A_23) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_40,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_39])).

tff(c_818,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_40])).

tff(c_1202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:29:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.45  
% 2.88/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.45  %$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.88/1.45  
% 2.88/1.45  %Foreground sorts:
% 2.88/1.45  
% 2.88/1.45  
% 2.88/1.45  %Background operators:
% 2.88/1.45  
% 2.88/1.45  
% 2.88/1.45  %Foreground operators:
% 2.88/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.88/1.45  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.88/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.88/1.45  
% 2.88/1.46  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 2.88/1.46  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.88/1.46  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 2.88/1.46  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 2.88/1.46  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.88/1.46  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 2.88/1.46  tff(c_311, plain, (![D_98, C_99, B_100, A_101]: (k2_enumset1(D_98, C_99, B_100, A_101)=k2_enumset1(A_101, B_100, C_99, D_98))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.46  tff(c_32, plain, (![A_61, B_62, C_63]: (k2_enumset1(A_61, A_61, B_62, C_63)=k1_enumset1(A_61, B_62, C_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.88/1.46  tff(c_359, plain, (![D_98, C_99, B_100]: (k2_enumset1(D_98, C_99, B_100, B_100)=k1_enumset1(B_100, C_99, D_98))), inference(superposition, [status(thm), theory('equality')], [c_311, c_32])).
% 2.88/1.46  tff(c_565, plain, (![B_108, D_109, C_110, A_111]: (k2_enumset1(B_108, D_109, C_110, A_111)=k2_enumset1(A_111, B_108, C_110, D_109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.46  tff(c_1075, plain, (![B_134, D_135, C_136]: (k2_enumset1(B_134, D_135, B_134, C_136)=k1_enumset1(B_134, C_136, D_135))), inference(superposition, [status(thm), theory('equality')], [c_359, c_565])).
% 2.88/1.46  tff(c_14, plain, (![D_22, B_20, C_21, A_19]: (k2_enumset1(D_22, B_20, C_21, A_19)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.46  tff(c_482, plain, (![D_105, C_106, B_107]: (k2_enumset1(D_105, C_106, B_107, B_107)=k1_enumset1(B_107, C_106, D_105))), inference(superposition, [status(thm), theory('equality')], [c_311, c_32])).
% 2.88/1.46  tff(c_550, plain, (![A_19, B_20, D_22]: (k2_enumset1(A_19, B_20, A_19, D_22)=k1_enumset1(A_19, B_20, D_22))), inference(superposition, [status(thm), theory('equality')], [c_14, c_482])).
% 2.88/1.46  tff(c_1085, plain, (![B_134, D_135, C_136]: (k1_enumset1(B_134, D_135, C_136)=k1_enumset1(B_134, C_136, D_135))), inference(superposition, [status(thm), theory('equality')], [c_1075, c_550])).
% 2.88/1.46  tff(c_16, plain, (![D_26, C_25, B_24, A_23]: (k2_enumset1(D_26, C_25, B_24, A_23)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.46  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.46  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.88/1.46  tff(c_39, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_38])).
% 2.88/1.46  tff(c_40, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_39])).
% 2.88/1.46  tff(c_818, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_40])).
% 2.88/1.46  tff(c_1202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1085, c_818])).
% 2.88/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.46  
% 2.88/1.46  Inference rules
% 2.88/1.46  ----------------------
% 2.88/1.46  #Ref     : 0
% 2.88/1.46  #Sup     : 288
% 2.88/1.46  #Fact    : 0
% 2.88/1.46  #Define  : 0
% 2.88/1.46  #Split   : 0
% 2.88/1.46  #Chain   : 0
% 2.88/1.46  #Close   : 0
% 2.88/1.46  
% 2.88/1.46  Ordering : KBO
% 2.88/1.46  
% 2.88/1.46  Simplification rules
% 2.88/1.46  ----------------------
% 2.88/1.46  #Subsume      : 19
% 2.88/1.46  #Demod        : 122
% 2.88/1.46  #Tautology    : 168
% 2.88/1.46  #SimpNegUnit  : 0
% 2.88/1.46  #BackRed      : 2
% 2.88/1.46  
% 2.88/1.46  #Partial instantiations: 0
% 2.88/1.46  #Strategies tried      : 1
% 2.88/1.46  
% 2.88/1.46  Timing (in seconds)
% 2.88/1.46  ----------------------
% 2.88/1.46  Preprocessing        : 0.32
% 2.88/1.46  Parsing              : 0.17
% 2.88/1.46  CNF conversion       : 0.02
% 2.88/1.46  Main loop            : 0.38
% 2.88/1.46  Inferencing          : 0.13
% 2.88/1.46  Reduction            : 0.16
% 2.88/1.46  Demodulation         : 0.13
% 2.88/1.46  BG Simplification    : 0.03
% 2.88/1.46  Subsumption          : 0.05
% 2.88/1.46  Abstraction          : 0.03
% 3.17/1.46  MUC search           : 0.00
% 3.17/1.46  Cooper               : 0.00
% 3.17/1.46  Total                : 0.73
% 3.17/1.46  Index Insertion      : 0.00
% 3.17/1.47  Index Deletion       : 0.00
% 3.17/1.47  Index Matching       : 0.00
% 3.17/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
