%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:14 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_tarski(A_3,B_4),k1_tarski(C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_10,B_11,D_22] : k2_xboole_0(k2_tarski(A_10,B_11),k1_tarski(D_22)) = k2_enumset1(A_10,A_10,B_11,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_56,plain,(
    ! [A_10,B_11,D_22] : k2_enumset1(A_10,A_10,B_11,D_22) = k1_enumset1(A_10,B_11,D_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.13  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.61/1.13  
% 1.61/1.13  %Foreground sorts:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Background operators:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Foreground operators:
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.61/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.61/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.61/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.61/1.13  
% 1.61/1.14  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.61/1.14  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.61/1.14  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.61/1.14  tff(f_36, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.61/1.14  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_tarski(A_3, B_4), k1_tarski(C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.14  tff(c_8, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.14  tff(c_44, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.14  tff(c_53, plain, (![A_10, B_11, D_22]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_tarski(D_22))=k2_enumset1(A_10, A_10, B_11, D_22))), inference(superposition, [status(thm), theory('equality')], [c_8, c_44])).
% 1.61/1.14  tff(c_56, plain, (![A_10, B_11, D_22]: (k2_enumset1(A_10, A_10, B_11, D_22)=k1_enumset1(A_10, B_11, D_22))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_53])).
% 1.61/1.14  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.14  tff(c_59, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_10])).
% 1.61/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  
% 1.61/1.14  Inference rules
% 1.61/1.14  ----------------------
% 1.61/1.14  #Ref     : 0
% 1.61/1.14  #Sup     : 11
% 1.61/1.14  #Fact    : 0
% 1.61/1.14  #Define  : 0
% 1.61/1.14  #Split   : 0
% 1.61/1.14  #Chain   : 0
% 1.61/1.14  #Close   : 0
% 1.61/1.14  
% 1.61/1.14  Ordering : KBO
% 1.61/1.14  
% 1.61/1.14  Simplification rules
% 1.61/1.14  ----------------------
% 1.61/1.14  #Subsume      : 0
% 1.61/1.14  #Demod        : 2
% 1.61/1.14  #Tautology    : 8
% 1.61/1.14  #SimpNegUnit  : 0
% 1.61/1.14  #BackRed      : 1
% 1.61/1.14  
% 1.61/1.14  #Partial instantiations: 0
% 1.61/1.14  #Strategies tried      : 1
% 1.61/1.14  
% 1.61/1.14  Timing (in seconds)
% 1.61/1.14  ----------------------
% 1.61/1.14  Preprocessing        : 0.26
% 1.61/1.14  Parsing              : 0.14
% 1.61/1.14  CNF conversion       : 0.01
% 1.61/1.14  Main loop            : 0.07
% 1.61/1.14  Inferencing          : 0.03
% 1.61/1.14  Reduction            : 0.02
% 1.61/1.14  Demodulation         : 0.02
% 1.61/1.14  BG Simplification    : 0.01
% 1.61/1.14  Subsumption          : 0.01
% 1.61/1.14  Abstraction          : 0.00
% 1.61/1.14  MUC search           : 0.00
% 1.61/1.14  Cooper               : 0.00
% 1.61/1.14  Total                : 0.35
% 1.73/1.14  Index Insertion      : 0.00
% 1.73/1.14  Index Deletion       : 0.00
% 1.73/1.14  Index Matching       : 0.00
% 1.73/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
