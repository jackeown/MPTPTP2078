%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:04 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_32,negated_conjecture,(
    ~ ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_16,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_23,plain,(
    ! [B_7] : k2_tarski(B_7,B_7) = k1_tarski(B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2])).

tff(c_6,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.03  
% 1.51/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.04  %$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.51/1.04  
% 1.51/1.04  %Foreground sorts:
% 1.51/1.04  
% 1.51/1.04  
% 1.51/1.04  %Background operators:
% 1.51/1.04  
% 1.51/1.04  
% 1.51/1.04  %Foreground operators:
% 1.51/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.51/1.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.51/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.51/1.04  
% 1.51/1.04  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.51/1.04  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.51/1.04  tff(f_32, negated_conjecture, ~(![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.51/1.04  tff(c_16, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.04  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.51/1.04  tff(c_23, plain, (![B_7]: (k2_tarski(B_7, B_7)=k1_tarski(B_7))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2])).
% 1.51/1.04  tff(c_6, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.51/1.04  tff(c_35, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23, c_6])).
% 1.51/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.04  
% 1.51/1.04  Inference rules
% 1.51/1.04  ----------------------
% 1.51/1.04  #Ref     : 0
% 1.51/1.04  #Sup     : 6
% 1.51/1.04  #Fact    : 0
% 1.51/1.04  #Define  : 0
% 1.51/1.04  #Split   : 0
% 1.51/1.04  #Chain   : 0
% 1.51/1.04  #Close   : 0
% 1.51/1.04  
% 1.51/1.04  Ordering : KBO
% 1.51/1.04  
% 1.51/1.04  Simplification rules
% 1.51/1.04  ----------------------
% 1.51/1.04  #Subsume      : 0
% 1.51/1.04  #Demod        : 1
% 1.51/1.04  #Tautology    : 4
% 1.51/1.04  #SimpNegUnit  : 0
% 1.51/1.04  #BackRed      : 1
% 1.51/1.04  
% 1.51/1.04  #Partial instantiations: 0
% 1.51/1.04  #Strategies tried      : 1
% 1.51/1.04  
% 1.51/1.04  Timing (in seconds)
% 1.51/1.04  ----------------------
% 1.51/1.04  Preprocessing        : 0.24
% 1.51/1.04  Parsing              : 0.13
% 1.51/1.04  CNF conversion       : 0.01
% 1.51/1.04  Main loop            : 0.06
% 1.51/1.04  Inferencing          : 0.03
% 1.51/1.04  Reduction            : 0.02
% 1.51/1.04  Demodulation         : 0.01
% 1.51/1.04  BG Simplification    : 0.01
% 1.51/1.05  Subsumption          : 0.01
% 1.51/1.05  Abstraction          : 0.00
% 1.51/1.05  MUC search           : 0.00
% 1.51/1.05  Cooper               : 0.00
% 1.51/1.05  Total                : 0.32
% 1.51/1.05  Index Insertion      : 0.00
% 1.51/1.05  Index Deletion       : 0.00
% 1.51/1.05  Index Matching       : 0.00
% 1.51/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
