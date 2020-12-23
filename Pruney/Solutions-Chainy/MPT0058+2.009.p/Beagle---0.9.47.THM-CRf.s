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
% DateTime   : Thu Dec  3 09:43:03 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),A_19) = A_19 ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = A_19 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [A_27,B_28] : k2_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    ! [A_9,B_10] : k2_xboole_0(k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = k2_xboole_0(k3_xboole_0(A_9,B_10),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_117])).

tff(c_132,plain,(
    ! [A_9,B_10] : k2_xboole_0(k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2,c_126])).

tff(c_14,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.13  
% 1.66/1.14  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.66/1.14  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.66/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.66/1.14  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.66/1.14  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.66/1.14  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.66/1.14  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.14  tff(c_49, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.14  tff(c_54, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), A_19)=A_19)), inference(resolution, [status(thm)], [c_6, c_49])).
% 1.66/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.14  tff(c_60, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k3_xboole_0(A_19, B_20))=A_19)), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 1.66/1.14  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.14  tff(c_117, plain, (![A_27, B_28]: (k2_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.14  tff(c_126, plain, (![A_9, B_10]: (k2_xboole_0(k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=k2_xboole_0(k3_xboole_0(A_9, B_10), A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_117])).
% 1.66/1.14  tff(c_132, plain, (![A_9, B_10]: (k2_xboole_0(k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2, c_126])).
% 1.66/1.14  tff(c_14, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.14  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_14])).
% 1.66/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  Inference rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Ref     : 0
% 1.66/1.14  #Sup     : 36
% 1.66/1.14  #Fact    : 0
% 1.66/1.14  #Define  : 0
% 1.66/1.14  #Split   : 0
% 1.66/1.14  #Chain   : 0
% 1.66/1.14  #Close   : 0
% 1.66/1.14  
% 1.66/1.14  Ordering : KBO
% 1.66/1.14  
% 1.66/1.14  Simplification rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Subsume      : 0
% 1.66/1.14  #Demod        : 17
% 1.66/1.14  #Tautology    : 29
% 1.66/1.14  #SimpNegUnit  : 0
% 1.66/1.14  #BackRed      : 1
% 1.66/1.14  
% 1.66/1.14  #Partial instantiations: 0
% 1.66/1.14  #Strategies tried      : 1
% 1.66/1.14  
% 1.66/1.14  Timing (in seconds)
% 1.66/1.14  ----------------------
% 1.66/1.14  Preprocessing        : 0.25
% 1.66/1.14  Parsing              : 0.14
% 1.66/1.14  CNF conversion       : 0.01
% 1.66/1.14  Main loop            : 0.13
% 1.66/1.14  Inferencing          : 0.05
% 1.66/1.14  Reduction            : 0.05
% 1.66/1.14  Demodulation         : 0.04
% 1.66/1.14  BG Simplification    : 0.01
% 1.66/1.14  Subsumption          : 0.02
% 1.66/1.14  Abstraction          : 0.01
% 1.66/1.14  MUC search           : 0.00
% 1.66/1.14  Cooper               : 0.00
% 1.66/1.14  Total                : 0.40
% 1.66/1.14  Index Insertion      : 0.00
% 1.66/1.14  Index Deletion       : 0.00
% 1.66/1.14  Index Matching       : 0.00
% 1.66/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
