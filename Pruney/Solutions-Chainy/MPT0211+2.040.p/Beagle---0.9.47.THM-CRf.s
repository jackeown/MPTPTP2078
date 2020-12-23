%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:20 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  17 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_18,plain,(
    ! [B_26,D_28,C_27,A_25] : k2_enumset1(B_26,D_28,C_27,A_25) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_360,plain,(
    ! [D_98,C_99,B_100,A_101] : k2_enumset1(D_98,C_99,B_100,A_101) = k2_enumset1(A_101,B_100,C_99,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [A_53,B_54,C_55] : k2_enumset1(A_53,A_53,B_54,C_55) = k1_enumset1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_459,plain,(
    ! [D_102,C_103,B_104] : k2_enumset1(D_102,C_103,B_104,B_104) = k1_enumset1(B_104,C_103,D_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_32])).

tff(c_513,plain,(
    ! [A_25,B_26,D_28] : k2_enumset1(A_25,B_26,A_25,D_28) = k1_enumset1(A_25,D_28,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_459])).

tff(c_20,plain,(
    ! [D_32,C_31,B_30,A_29] : k2_enumset1(D_32,C_31,B_30,A_29) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_42,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_41])).

tff(c_726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.69/1.39  
% 2.69/1.39  %Foreground sorts:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Background operators:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Foreground operators:
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.39  
% 2.69/1.40  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 2.69/1.40  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 2.69/1.40  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.69/1.40  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.69/1.40  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 2.69/1.40  tff(c_18, plain, (![B_26, D_28, C_27, A_25]: (k2_enumset1(B_26, D_28, C_27, A_25)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.40  tff(c_360, plain, (![D_98, C_99, B_100, A_101]: (k2_enumset1(D_98, C_99, B_100, A_101)=k2_enumset1(A_101, B_100, C_99, D_98))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.40  tff(c_32, plain, (![A_53, B_54, C_55]: (k2_enumset1(A_53, A_53, B_54, C_55)=k1_enumset1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.40  tff(c_459, plain, (![D_102, C_103, B_104]: (k2_enumset1(D_102, C_103, B_104, B_104)=k1_enumset1(B_104, C_103, D_102))), inference(superposition, [status(thm), theory('equality')], [c_360, c_32])).
% 2.69/1.40  tff(c_513, plain, (![A_25, B_26, D_28]: (k2_enumset1(A_25, B_26, A_25, D_28)=k1_enumset1(A_25, D_28, B_26))), inference(superposition, [status(thm), theory('equality')], [c_18, c_459])).
% 2.69/1.40  tff(c_20, plain, (![D_32, C_31, B_30, A_29]: (k2_enumset1(D_32, C_31, B_30, A_29)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.40  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.40  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.40  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 2.69/1.40  tff(c_42, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_41])).
% 2.69/1.40  tff(c_726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_513, c_42])).
% 2.69/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  Inference rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Ref     : 0
% 2.69/1.40  #Sup     : 174
% 2.69/1.40  #Fact    : 0
% 2.69/1.40  #Define  : 0
% 2.69/1.40  #Split   : 0
% 2.69/1.40  #Chain   : 0
% 2.69/1.40  #Close   : 0
% 2.69/1.40  
% 2.69/1.40  Ordering : KBO
% 2.69/1.40  
% 2.69/1.40  Simplification rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Subsume      : 5
% 2.69/1.40  #Demod        : 44
% 2.69/1.40  #Tautology    : 97
% 2.69/1.40  #SimpNegUnit  : 0
% 2.69/1.40  #BackRed      : 1
% 2.69/1.40  
% 2.69/1.40  #Partial instantiations: 0
% 2.69/1.40  #Strategies tried      : 1
% 2.69/1.40  
% 2.69/1.40  Timing (in seconds)
% 2.69/1.40  ----------------------
% 2.69/1.40  Preprocessing        : 0.31
% 2.69/1.40  Parsing              : 0.17
% 2.69/1.40  CNF conversion       : 0.02
% 2.69/1.40  Main loop            : 0.28
% 2.69/1.40  Inferencing          : 0.10
% 2.69/1.40  Reduction            : 0.11
% 2.69/1.40  Demodulation         : 0.10
% 2.69/1.40  BG Simplification    : 0.02
% 2.69/1.40  Subsumption          : 0.04
% 2.69/1.40  Abstraction          : 0.02
% 2.69/1.40  MUC search           : 0.00
% 2.69/1.40  Cooper               : 0.00
% 2.69/1.40  Total                : 0.62
% 2.69/1.40  Index Insertion      : 0.00
% 2.69/1.40  Index Deletion       : 0.00
% 2.69/1.40  Index Matching       : 0.00
% 2.69/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
