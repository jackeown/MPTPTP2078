%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:05 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_18,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k1_tarski(A_10),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(k1_tarski(A_25),B_26) = k1_tarski(A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(B_27,k1_tarski(A_28)) = k1_tarski(A_28)
      | ~ r2_hidden(A_28,B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_16,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_16])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:36:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.14  
% 1.76/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.14  %$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.76/1.14  
% 1.76/1.14  %Foreground sorts:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Background operators:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Foreground operators:
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.76/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.14  
% 1.76/1.15  tff(f_46, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 1.76/1.15  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.76/1.15  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.76/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.76/1.15  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.15  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k1_tarski(A_10), B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.76/1.15  tff(c_76, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.15  tff(c_96, plain, (![A_25, B_26]: (k3_xboole_0(k1_tarski(A_25), B_26)=k1_tarski(A_25) | ~r2_hidden(A_25, B_26))), inference(resolution, [status(thm)], [c_14, c_76])).
% 1.76/1.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.76/1.15  tff(c_119, plain, (![B_27, A_28]: (k3_xboole_0(B_27, k1_tarski(A_28))=k1_tarski(A_28) | ~r2_hidden(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 1.76/1.15  tff(c_16, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.15  tff(c_135, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_119, c_16])).
% 1.76/1.15  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_135])).
% 1.76/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  Inference rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Ref     : 0
% 1.76/1.15  #Sup     : 33
% 1.76/1.15  #Fact    : 0
% 1.76/1.15  #Define  : 0
% 1.76/1.15  #Split   : 0
% 1.76/1.15  #Chain   : 0
% 1.76/1.15  #Close   : 0
% 1.76/1.15  
% 1.76/1.15  Ordering : KBO
% 1.76/1.15  
% 1.76/1.15  Simplification rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Subsume      : 2
% 1.76/1.15  #Demod        : 1
% 1.76/1.15  #Tautology    : 18
% 1.76/1.15  #SimpNegUnit  : 0
% 1.76/1.15  #BackRed      : 0
% 1.76/1.15  
% 1.76/1.15  #Partial instantiations: 0
% 1.76/1.15  #Strategies tried      : 1
% 1.76/1.15  
% 1.76/1.15  Timing (in seconds)
% 1.76/1.15  ----------------------
% 1.76/1.15  Preprocessing        : 0.28
% 1.76/1.15  Parsing              : 0.15
% 1.76/1.15  CNF conversion       : 0.01
% 1.76/1.15  Main loop            : 0.11
% 1.76/1.15  Inferencing          : 0.05
% 1.76/1.15  Reduction            : 0.03
% 1.76/1.15  Demodulation         : 0.03
% 1.76/1.15  BG Simplification    : 0.01
% 1.76/1.15  Subsumption          : 0.02
% 1.76/1.15  Abstraction          : 0.01
% 1.76/1.15  MUC search           : 0.00
% 1.76/1.15  Cooper               : 0.00
% 1.76/1.15  Total                : 0.41
% 1.76/1.15  Index Insertion      : 0.00
% 1.76/1.15  Index Deletion       : 0.00
% 1.76/1.15  Index Matching       : 0.00
% 1.76/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
