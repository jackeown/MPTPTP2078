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
% DateTime   : Thu Dec  3 09:52:17 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_60,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(k1_tarski(A_15),B_16)
      | r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_16])).

tff(c_89,plain,(
    ! [B_21,A_22] :
      ( k3_xboole_0(B_21,k1_tarski(A_22)) = k1_tarski(A_22)
      | ~ r2_hidden(A_22,B_21) ) ),
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

tff(c_101,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_17])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.35  % CPULimit   : 60
% 0.21/0.35  % DateTime   : Tue Dec  1 09:46:51 EST 2020
% 0.21/0.36  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.13  
% 1.60/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.13  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.60/1.13  
% 1.60/1.13  %Foreground sorts:
% 1.60/1.13  
% 1.60/1.13  
% 1.60/1.13  %Background operators:
% 1.60/1.13  
% 1.60/1.13  
% 1.60/1.13  %Foreground operators:
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.60/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.60/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.60/1.13  
% 1.60/1.14  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.60/1.14  tff(f_47, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.60/1.14  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.60/1.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.60/1.14  tff(c_60, plain, (![A_15, B_16]: (r1_xboole_0(k1_tarski(A_15), B_16) | r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.14  tff(c_16, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.60/1.14  tff(c_64, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_16])).
% 1.60/1.14  tff(c_89, plain, (![B_21, A_22]: (k3_xboole_0(B_21, k1_tarski(A_22))=k1_tarski(A_22) | ~r2_hidden(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.14  tff(c_14, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.60/1.14  tff(c_17, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 1.60/1.14  tff(c_101, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_17])).
% 1.60/1.14  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_101])).
% 1.60/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  Inference rules
% 1.60/1.14  ----------------------
% 1.60/1.14  #Ref     : 0
% 1.60/1.14  #Sup     : 24
% 1.60/1.14  #Fact    : 0
% 1.60/1.14  #Define  : 0
% 1.60/1.14  #Split   : 0
% 1.60/1.14  #Chain   : 0
% 1.60/1.14  #Close   : 0
% 1.60/1.14  
% 1.60/1.14  Ordering : KBO
% 1.60/1.14  
% 1.60/1.14  Simplification rules
% 1.60/1.14  ----------------------
% 1.60/1.14  #Subsume      : 0
% 1.60/1.14  #Demod        : 2
% 1.60/1.14  #Tautology    : 15
% 1.60/1.14  #SimpNegUnit  : 0
% 1.60/1.14  #BackRed      : 0
% 1.60/1.14  
% 1.60/1.14  #Partial instantiations: 0
% 1.60/1.14  #Strategies tried      : 1
% 1.60/1.14  
% 1.60/1.14  Timing (in seconds)
% 1.60/1.14  ----------------------
% 1.60/1.14  Preprocessing        : 0.27
% 1.60/1.14  Parsing              : 0.15
% 1.60/1.14  CNF conversion       : 0.01
% 1.60/1.14  Main loop            : 0.10
% 1.60/1.14  Inferencing          : 0.04
% 1.60/1.14  Reduction            : 0.03
% 1.60/1.14  Demodulation         : 0.02
% 1.60/1.14  BG Simplification    : 0.01
% 1.60/1.14  Subsumption          : 0.01
% 1.60/1.14  Abstraction          : 0.01
% 1.60/1.14  MUC search           : 0.00
% 1.60/1.14  Cooper               : 0.00
% 1.60/1.14  Total                : 0.38
% 1.60/1.14  Index Insertion      : 0.00
% 1.60/1.14  Index Deletion       : 0.00
% 1.60/1.14  Index Matching       : 0.00
% 1.60/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
