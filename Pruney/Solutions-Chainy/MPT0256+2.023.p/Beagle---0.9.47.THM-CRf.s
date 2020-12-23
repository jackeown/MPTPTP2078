%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:05 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_18,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_19,C_20,B_21] :
      ( r2_hidden(A_19,C_20)
      | ~ r1_tarski(k2_tarski(A_19,B_21),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_22,C_23] :
      ( r2_hidden(A_22,C_23)
      | ~ r1_tarski(k1_tarski(A_22),C_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_47])).

tff(c_54,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.09  
% 1.59/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.09  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.59/1.09  
% 1.59/1.09  %Foreground sorts:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Background operators:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Foreground operators:
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.59/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.59/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.59/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.59/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.59/1.09  
% 1.59/1.10  tff(f_46, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.59/1.10  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.59/1.10  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.59/1.10  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.59/1.10  tff(c_18, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.59/1.10  tff(c_20, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.59/1.10  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.10  tff(c_34, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_2])).
% 1.59/1.10  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.10  tff(c_47, plain, (![A_19, C_20, B_21]: (r2_hidden(A_19, C_20) | ~r1_tarski(k2_tarski(A_19, B_21), C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.59/1.10  tff(c_51, plain, (![A_22, C_23]: (r2_hidden(A_22, C_23) | ~r1_tarski(k1_tarski(A_22), C_23))), inference(superposition, [status(thm), theory('equality')], [c_6, c_47])).
% 1.59/1.10  tff(c_54, plain, (r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_51])).
% 1.59/1.10  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_54])).
% 1.59/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  Inference rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Ref     : 0
% 1.59/1.10  #Sup     : 9
% 1.59/1.10  #Fact    : 0
% 1.59/1.10  #Define  : 0
% 1.59/1.10  #Split   : 0
% 1.59/1.10  #Chain   : 0
% 1.59/1.10  #Close   : 0
% 1.59/1.10  
% 1.59/1.10  Ordering : KBO
% 1.59/1.10  
% 1.59/1.10  Simplification rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Subsume      : 0
% 1.59/1.10  #Demod        : 0
% 1.59/1.10  #Tautology    : 6
% 1.59/1.10  #SimpNegUnit  : 1
% 1.59/1.10  #BackRed      : 0
% 1.59/1.10  
% 1.59/1.10  #Partial instantiations: 0
% 1.59/1.10  #Strategies tried      : 1
% 1.59/1.10  
% 1.59/1.10  Timing (in seconds)
% 1.59/1.10  ----------------------
% 1.59/1.10  Preprocessing        : 0.27
% 1.59/1.10  Parsing              : 0.14
% 1.59/1.10  CNF conversion       : 0.02
% 1.59/1.10  Main loop            : 0.07
% 1.59/1.10  Inferencing          : 0.03
% 1.59/1.10  Reduction            : 0.02
% 1.59/1.11  Demodulation         : 0.01
% 1.59/1.11  BG Simplification    : 0.01
% 1.59/1.11  Subsumption          : 0.01
% 1.59/1.11  Abstraction          : 0.01
% 1.59/1.11  MUC search           : 0.00
% 1.59/1.11  Cooper               : 0.00
% 1.59/1.11  Total                : 0.36
% 1.59/1.11  Index Insertion      : 0.00
% 1.59/1.11  Index Deletion       : 0.00
% 1.59/1.11  Index Matching       : 0.00
% 1.59/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
