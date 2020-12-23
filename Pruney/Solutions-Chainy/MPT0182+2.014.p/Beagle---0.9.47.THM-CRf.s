%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:44 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  11 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [B_29,A_30,C_31] : k2_xboole_0(k2_tarski(B_29,A_30),k1_tarski(C_31)) = k1_enumset1(A_30,B_29,C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_tarski(A_3,B_4),k1_tarski(C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [B_29,A_30,C_31] : k1_enumset1(B_29,A_30,C_31) = k1_enumset1(A_30,B_29,C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_4])).

tff(c_14,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:59:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.17  
% 1.75/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.17  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.75/1.17  
% 1.75/1.17  %Foreground sorts:
% 1.75/1.17  
% 1.75/1.17  
% 1.75/1.17  %Background operators:
% 1.75/1.17  
% 1.75/1.17  
% 1.75/1.17  %Foreground operators:
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.75/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.17  
% 1.75/1.18  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.75/1.18  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.75/1.18  tff(f_40, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 1.75/1.18  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.18  tff(c_75, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.18  tff(c_103, plain, (![B_29, A_30, C_31]: (k2_xboole_0(k2_tarski(B_29, A_30), k1_tarski(C_31))=k1_enumset1(A_30, B_29, C_31))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 1.75/1.18  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_tarski(A_3, B_4), k1_tarski(C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.18  tff(c_109, plain, (![B_29, A_30, C_31]: (k1_enumset1(B_29, A_30, C_31)=k1_enumset1(A_30, B_29, C_31))), inference(superposition, [status(thm), theory('equality')], [c_103, c_4])).
% 1.75/1.18  tff(c_14, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.75/1.18  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_14])).
% 1.75/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.18  
% 1.75/1.18  Inference rules
% 1.75/1.18  ----------------------
% 1.75/1.18  #Ref     : 0
% 1.75/1.18  #Sup     : 28
% 1.75/1.18  #Fact    : 0
% 1.75/1.18  #Define  : 0
% 1.75/1.18  #Split   : 0
% 1.75/1.18  #Chain   : 0
% 1.75/1.18  #Close   : 0
% 1.75/1.18  
% 1.75/1.18  Ordering : KBO
% 1.75/1.18  
% 1.75/1.18  Simplification rules
% 1.75/1.18  ----------------------
% 1.75/1.18  #Subsume      : 0
% 1.75/1.18  #Demod        : 6
% 1.75/1.18  #Tautology    : 23
% 1.75/1.18  #SimpNegUnit  : 0
% 1.75/1.18  #BackRed      : 1
% 1.75/1.18  
% 1.75/1.18  #Partial instantiations: 0
% 1.75/1.18  #Strategies tried      : 1
% 1.75/1.18  
% 1.75/1.18  Timing (in seconds)
% 1.75/1.18  ----------------------
% 1.75/1.18  Preprocessing        : 0.27
% 1.75/1.18  Parsing              : 0.14
% 1.75/1.18  CNF conversion       : 0.01
% 1.75/1.18  Main loop            : 0.15
% 1.75/1.18  Inferencing          : 0.06
% 1.75/1.19  Reduction            : 0.05
% 1.75/1.19  Demodulation         : 0.05
% 1.75/1.19  BG Simplification    : 0.01
% 1.75/1.19  Subsumption          : 0.02
% 1.75/1.19  Abstraction          : 0.01
% 1.75/1.19  MUC search           : 0.00
% 1.75/1.19  Cooper               : 0.00
% 1.75/1.19  Total                : 0.44
% 1.75/1.19  Index Insertion      : 0.00
% 1.75/1.19  Index Deletion       : 0.00
% 1.75/1.19  Index Matching       : 0.00
% 1.75/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
