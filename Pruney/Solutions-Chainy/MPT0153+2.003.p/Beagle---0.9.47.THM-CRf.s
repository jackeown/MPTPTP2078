%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:03 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_29,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_19,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_15])).

tff(c_36,plain,(
    ! [B_12] : k2_tarski(B_12,B_12) = k1_tarski(B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_19])).

tff(c_12,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.08  
% 1.60/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.08  %$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.60/1.08  
% 1.60/1.08  %Foreground sorts:
% 1.60/1.08  
% 1.60/1.08  
% 1.60/1.08  %Background operators:
% 1.60/1.08  
% 1.60/1.08  
% 1.60/1.08  %Foreground operators:
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.60/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.08  
% 1.60/1.09  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.60/1.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.60/1.09  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.60/1.09  tff(f_40, negated_conjecture, ~(![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.60/1.09  tff(c_29, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.09  tff(c_15, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.09  tff(c_19, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_15])).
% 1.60/1.09  tff(c_36, plain, (![B_12]: (k2_tarski(B_12, B_12)=k1_tarski(B_12))), inference(superposition, [status(thm), theory('equality')], [c_29, c_19])).
% 1.60/1.09  tff(c_12, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.09  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_12])).
% 1.60/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.09  
% 1.60/1.09  Inference rules
% 1.60/1.09  ----------------------
% 1.60/1.09  #Ref     : 0
% 1.60/1.09  #Sup     : 8
% 1.60/1.09  #Fact    : 0
% 1.60/1.09  #Define  : 0
% 1.60/1.09  #Split   : 0
% 1.60/1.09  #Chain   : 0
% 1.60/1.09  #Close   : 0
% 1.60/1.09  
% 1.60/1.09  Ordering : KBO
% 1.60/1.09  
% 1.60/1.09  Simplification rules
% 1.60/1.09  ----------------------
% 1.60/1.09  #Subsume      : 0
% 1.60/1.09  #Demod        : 3
% 1.60/1.09  #Tautology    : 6
% 1.60/1.09  #SimpNegUnit  : 0
% 1.60/1.09  #BackRed      : 1
% 1.60/1.09  
% 1.60/1.09  #Partial instantiations: 0
% 1.60/1.09  #Strategies tried      : 1
% 1.60/1.09  
% 1.60/1.09  Timing (in seconds)
% 1.60/1.09  ----------------------
% 1.60/1.09  Preprocessing        : 0.26
% 1.60/1.09  Parsing              : 0.14
% 1.60/1.09  CNF conversion       : 0.02
% 1.60/1.09  Main loop            : 0.07
% 1.60/1.09  Inferencing          : 0.03
% 1.60/1.09  Reduction            : 0.02
% 1.60/1.09  Demodulation         : 0.02
% 1.60/1.09  BG Simplification    : 0.01
% 1.60/1.09  Subsumption          : 0.01
% 1.60/1.09  Abstraction          : 0.00
% 1.60/1.09  MUC search           : 0.00
% 1.60/1.09  Cooper               : 0.00
% 1.60/1.09  Total                : 0.35
% 1.60/1.09  Index Insertion      : 0.00
% 1.60/1.09  Index Deletion       : 0.00
% 1.60/1.09  Index Matching       : 0.00
% 1.60/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
