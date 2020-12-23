%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:46 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  11 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_13,B_14,C_15,D_16] : k2_xboole_0(k2_tarski(A_13,B_14),k2_tarski(C_15,D_16)) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [A_21,B_22,B_23,A_24] : k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(B_23,A_24)) = k2_enumset1(A_21,B_22,A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_21,B_22,B_23,A_24] : k2_enumset1(A_21,B_22,B_23,A_24) = k2_enumset1(A_21,B_22,A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_4])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 19:11:38 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.13  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.75/1.13  
% 1.75/1.13  %Foreground sorts:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Background operators:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Foreground operators:
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.13  
% 1.75/1.14  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.75/1.14  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.75/1.14  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 1.75/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.14  tff(c_51, plain, (![A_13, B_14, C_15, D_16]: (k2_xboole_0(k2_tarski(A_13, B_14), k2_tarski(C_15, D_16))=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.14  tff(c_101, plain, (![A_21, B_22, B_23, A_24]: (k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(B_23, A_24))=k2_enumset1(A_21, B_22, A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_2, c_51])).
% 1.75/1.14  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.14  tff(c_110, plain, (![A_21, B_22, B_23, A_24]: (k2_enumset1(A_21, B_22, B_23, A_24)=k2_enumset1(A_21, B_22, A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_101, c_4])).
% 1.75/1.14  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.75/1.14  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_8])).
% 1.75/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  Inference rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Ref     : 0
% 1.75/1.14  #Sup     : 42
% 1.75/1.14  #Fact    : 0
% 1.75/1.14  #Define  : 0
% 1.75/1.14  #Split   : 0
% 1.75/1.14  #Chain   : 0
% 1.75/1.14  #Close   : 0
% 1.75/1.14  
% 1.75/1.14  Ordering : KBO
% 1.75/1.14  
% 1.75/1.14  Simplification rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Subsume      : 0
% 1.75/1.14  #Demod        : 5
% 1.75/1.14  #Tautology    : 28
% 1.75/1.14  #SimpNegUnit  : 0
% 1.75/1.14  #BackRed      : 1
% 1.75/1.14  
% 1.75/1.14  #Partial instantiations: 0
% 1.75/1.14  #Strategies tried      : 1
% 1.75/1.14  
% 1.75/1.14  Timing (in seconds)
% 1.75/1.14  ----------------------
% 1.75/1.14  Preprocessing        : 0.26
% 1.75/1.14  Parsing              : 0.13
% 1.75/1.14  CNF conversion       : 0.01
% 1.75/1.14  Main loop            : 0.13
% 1.75/1.14  Inferencing          : 0.05
% 1.75/1.14  Reduction            : 0.05
% 1.75/1.14  Demodulation         : 0.04
% 1.75/1.14  BG Simplification    : 0.01
% 1.75/1.14  Subsumption          : 0.02
% 1.75/1.14  Abstraction          : 0.01
% 1.75/1.14  MUC search           : 0.00
% 1.75/1.14  Cooper               : 0.00
% 1.75/1.14  Total                : 0.42
% 1.75/1.14  Index Insertion      : 0.00
% 1.75/1.14  Index Deletion       : 0.00
% 1.75/1.14  Index Matching       : 0.00
% 1.75/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
