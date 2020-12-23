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
% DateTime   : Thu Dec  3 09:46:13 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
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

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_tarski(A_1,B_2),k1_tarski(C_3)) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_12,B_13,D_22] : k2_xboole_0(k2_tarski(A_12,B_13),k1_tarski(D_22)) = k2_enumset1(A_12,A_12,B_13,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_29])).

tff(c_41,plain,(
    ! [A_12,B_13,D_22] : k2_enumset1(A_12,A_12,B_13,D_22) = k1_enumset1(A_12,B_13,D_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:30:21 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.05  
% 1.51/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.05  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.51/1.05  
% 1.51/1.05  %Foreground sorts:
% 1.51/1.05  
% 1.51/1.05  
% 1.51/1.05  %Background operators:
% 1.51/1.05  
% 1.51/1.05  
% 1.51/1.05  %Foreground operators:
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.51/1.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.51/1.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.51/1.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.51/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.51/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.51/1.05  
% 1.61/1.06  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.61/1.06  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.61/1.06  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.61/1.06  tff(f_36, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.61/1.06  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_tarski(A_1, B_2), k1_tarski(C_3))=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.06  tff(c_8, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.06  tff(c_29, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.06  tff(c_38, plain, (![A_12, B_13, D_22]: (k2_xboole_0(k2_tarski(A_12, B_13), k1_tarski(D_22))=k2_enumset1(A_12, A_12, B_13, D_22))), inference(superposition, [status(thm), theory('equality')], [c_8, c_29])).
% 1.61/1.06  tff(c_41, plain, (![A_12, B_13, D_22]: (k2_enumset1(A_12, A_12, B_13, D_22)=k1_enumset1(A_12, B_13, D_22))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 1.61/1.06  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.06  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_10])).
% 1.61/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.06  
% 1.61/1.06  Inference rules
% 1.61/1.06  ----------------------
% 1.61/1.06  #Ref     : 0
% 1.61/1.06  #Sup     : 7
% 1.61/1.06  #Fact    : 0
% 1.61/1.06  #Define  : 0
% 1.61/1.06  #Split   : 0
% 1.61/1.06  #Chain   : 0
% 1.61/1.06  #Close   : 0
% 1.61/1.06  
% 1.61/1.06  Ordering : KBO
% 1.61/1.06  
% 1.61/1.06  Simplification rules
% 1.61/1.06  ----------------------
% 1.61/1.06  #Subsume      : 0
% 1.61/1.06  #Demod        : 2
% 1.61/1.06  #Tautology    : 6
% 1.61/1.06  #SimpNegUnit  : 0
% 1.61/1.06  #BackRed      : 1
% 1.61/1.06  
% 1.61/1.06  #Partial instantiations: 0
% 1.61/1.06  #Strategies tried      : 1
% 1.61/1.06  
% 1.61/1.06  Timing (in seconds)
% 1.61/1.06  ----------------------
% 1.61/1.06  Preprocessing        : 0.26
% 1.61/1.06  Parsing              : 0.14
% 1.61/1.06  CNF conversion       : 0.01
% 1.61/1.06  Main loop            : 0.06
% 1.61/1.06  Inferencing          : 0.03
% 1.61/1.06  Reduction            : 0.02
% 1.61/1.06  Demodulation         : 0.02
% 1.61/1.06  BG Simplification    : 0.01
% 1.61/1.06  Subsumption          : 0.01
% 1.61/1.06  Abstraction          : 0.00
% 1.61/1.06  MUC search           : 0.00
% 1.61/1.06  Cooper               : 0.00
% 1.61/1.06  Total                : 0.34
% 1.61/1.06  Index Insertion      : 0.00
% 1.61/1.06  Index Deletion       : 0.00
% 1.61/1.06  Index Matching       : 0.00
% 1.61/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
