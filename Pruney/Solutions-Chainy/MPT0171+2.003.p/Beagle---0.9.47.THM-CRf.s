%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:29 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

tff(c_10,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_16] : k2_enumset1(A_16,A_16,A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [A_36,D_37,E_35,B_34,C_38] : k2_xboole_0(k2_enumset1(A_36,B_34,C_38,D_37),k1_tarski(E_35)) = k3_enumset1(A_36,B_34,C_38,D_37,E_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_127,plain,(
    ! [A_16,E_35] : k3_enumset1(A_16,A_16,A_16,A_16,E_35) = k2_xboole_0(k1_tarski(A_16),k1_tarski(E_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_131,plain,(
    ! [A_16,E_35] : k3_enumset1(A_16,A_16,A_16,A_16,E_35) = k2_tarski(A_16,E_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_14,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_164,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_14])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.67/1.12  
% 1.67/1.12  %Foreground sorts:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Background operators:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Foreground operators:
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.67/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.12  
% 1.67/1.12  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.67/1.12  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.67/1.12  tff(f_37, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 1.67/1.12  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.67/1.12  tff(f_40, negated_conjecture, ~(![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 1.67/1.12  tff(c_10, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.12  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.12  tff(c_12, plain, (![A_16]: (k2_enumset1(A_16, A_16, A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.12  tff(c_115, plain, (![A_36, D_37, E_35, B_34, C_38]: (k2_xboole_0(k2_enumset1(A_36, B_34, C_38, D_37), k1_tarski(E_35))=k3_enumset1(A_36, B_34, C_38, D_37, E_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.12  tff(c_127, plain, (![A_16, E_35]: (k3_enumset1(A_16, A_16, A_16, A_16, E_35)=k2_xboole_0(k1_tarski(A_16), k1_tarski(E_35)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_115])).
% 1.67/1.12  tff(c_131, plain, (![A_16, E_35]: (k3_enumset1(A_16, A_16, A_16, A_16, E_35)=k2_tarski(A_16, E_35))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 1.67/1.12  tff(c_14, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.12  tff(c_164, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_14])).
% 1.67/1.12  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_164])).
% 1.67/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  Inference rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Ref     : 0
% 1.67/1.12  #Sup     : 34
% 1.67/1.12  #Fact    : 0
% 1.67/1.12  #Define  : 0
% 1.67/1.12  #Split   : 0
% 1.67/1.12  #Chain   : 0
% 1.67/1.12  #Close   : 0
% 1.67/1.12  
% 1.67/1.12  Ordering : KBO
% 1.67/1.12  
% 1.67/1.12  Simplification rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Subsume      : 0
% 1.67/1.12  #Demod        : 15
% 1.67/1.12  #Tautology    : 27
% 1.67/1.12  #SimpNegUnit  : 0
% 1.67/1.12  #BackRed      : 1
% 1.67/1.12  
% 1.67/1.12  #Partial instantiations: 0
% 1.67/1.12  #Strategies tried      : 1
% 1.67/1.12  
% 1.67/1.12  Timing (in seconds)
% 1.67/1.12  ----------------------
% 1.67/1.13  Preprocessing        : 0.26
% 1.67/1.13  Parsing              : 0.13
% 1.67/1.13  CNF conversion       : 0.01
% 1.67/1.13  Main loop            : 0.11
% 1.67/1.13  Inferencing          : 0.05
% 1.67/1.13  Reduction            : 0.04
% 1.67/1.13  Demodulation         : 0.03
% 1.67/1.13  BG Simplification    : 0.01
% 1.67/1.13  Subsumption          : 0.01
% 1.67/1.13  Abstraction          : 0.01
% 1.67/1.13  MUC search           : 0.00
% 1.67/1.13  Cooper               : 0.00
% 1.67/1.13  Total                : 0.40
% 1.67/1.13  Index Insertion      : 0.00
% 1.67/1.13  Index Deletion       : 0.00
% 1.67/1.13  Index Matching       : 0.00
% 1.67/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
