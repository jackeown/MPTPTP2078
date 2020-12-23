%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:18 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_60,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(k1_tarski(A_16),B_17)
      | r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_16])).

tff(c_74,plain,(
    ! [B_20,A_21] :
      ( k3_xboole_0(B_20,k1_tarski(A_21)) = k1_tarski(A_21)
      | ~ r2_hidden(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_17,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_17])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.19  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.76/1.19  
% 1.76/1.19  %Foreground sorts:
% 1.76/1.19  
% 1.76/1.19  
% 1.76/1.19  %Background operators:
% 1.76/1.19  
% 1.76/1.19  
% 1.76/1.19  %Foreground operators:
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.76/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.19  
% 1.76/1.19  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.76/1.19  tff(f_47, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.76/1.19  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.76/1.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.76/1.19  tff(c_60, plain, (![A_16, B_17]: (r1_xboole_0(k1_tarski(A_16), B_17) | r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.19  tff(c_16, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.76/1.19  tff(c_64, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_16])).
% 1.76/1.19  tff(c_74, plain, (![B_20, A_21]: (k3_xboole_0(B_20, k1_tarski(A_21))=k1_tarski(A_21) | ~r2_hidden(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.76/1.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.76/1.19  tff(c_14, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.76/1.19  tff(c_17, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 1.76/1.19  tff(c_86, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_74, c_17])).
% 1.76/1.19  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_86])).
% 1.76/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  Inference rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Ref     : 0
% 1.76/1.19  #Sup     : 20
% 1.76/1.19  #Fact    : 0
% 1.76/1.19  #Define  : 0
% 1.76/1.19  #Split   : 0
% 1.76/1.19  #Chain   : 0
% 1.76/1.19  #Close   : 0
% 1.76/1.19  
% 1.76/1.19  Ordering : KBO
% 1.76/1.19  
% 1.76/1.19  Simplification rules
% 1.76/1.20  ----------------------
% 1.76/1.20  #Subsume      : 0
% 1.76/1.20  #Demod        : 2
% 1.76/1.20  #Tautology    : 13
% 1.76/1.20  #SimpNegUnit  : 0
% 1.76/1.20  #BackRed      : 0
% 1.76/1.20  
% 1.76/1.20  #Partial instantiations: 0
% 1.76/1.20  #Strategies tried      : 1
% 1.76/1.20  
% 1.76/1.20  Timing (in seconds)
% 1.76/1.20  ----------------------
% 1.76/1.20  Preprocessing        : 0.29
% 1.76/1.20  Parsing              : 0.16
% 1.76/1.20  CNF conversion       : 0.02
% 1.76/1.20  Main loop            : 0.09
% 1.76/1.20  Inferencing          : 0.04
% 1.76/1.20  Reduction            : 0.03
% 1.76/1.20  Demodulation         : 0.02
% 1.76/1.20  BG Simplification    : 0.01
% 1.76/1.20  Subsumption          : 0.01
% 1.76/1.20  Abstraction          : 0.01
% 1.76/1.20  MUC search           : 0.00
% 1.76/1.20  Cooper               : 0.00
% 1.76/1.20  Total                : 0.40
% 1.76/1.20  Index Insertion      : 0.00
% 1.76/1.20  Index Deletion       : 0.00
% 1.76/1.20  Index Matching       : 0.00
% 1.76/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
