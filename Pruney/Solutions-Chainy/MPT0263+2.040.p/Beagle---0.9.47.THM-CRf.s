%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:19 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_139,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(B_33,k1_tarski(A_34)) = k1_tarski(A_34)
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_25,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_170,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_25])).

tff(c_172,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(k1_tarski(A_35),B_36) = k1_tarski(A_35)
      | r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_24])).

tff(c_178,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_77])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.20  
% 1.93/1.21  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.93/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.93/1.21  tff(f_53, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.93/1.21  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.93/1.21  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.93/1.21  tff(c_139, plain, (![B_33, A_34]: (k3_xboole_0(B_33, k1_tarski(A_34))=k1_tarski(A_34) | ~r2_hidden(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.21  tff(c_22, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.21  tff(c_25, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 1.93/1.21  tff(c_170, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_139, c_25])).
% 1.93/1.21  tff(c_172, plain, (![A_35, B_36]: (k4_xboole_0(k1_tarski(A_35), B_36)=k1_tarski(A_35) | r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.21  tff(c_69, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.21  tff(c_24, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.21  tff(c_77, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_69, c_24])).
% 1.93/1.21  tff(c_178, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_172, c_77])).
% 1.93/1.21  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_178])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 0
% 1.93/1.21  #Sup     : 38
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 0
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 0
% 1.93/1.21  #Demod        : 4
% 1.93/1.21  #Tautology    : 27
% 1.93/1.21  #SimpNegUnit  : 1
% 1.93/1.21  #BackRed      : 0
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 1.93/1.21  Preprocessing        : 0.30
% 1.93/1.21  Parsing              : 0.16
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.13
% 1.93/1.21  Inferencing          : 0.05
% 1.93/1.21  Reduction            : 0.04
% 1.93/1.21  Demodulation         : 0.03
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.02
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.45
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
