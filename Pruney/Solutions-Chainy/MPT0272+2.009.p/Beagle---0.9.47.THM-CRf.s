%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:07 EST 2020

% Result     : Theorem 6.35s
% Output     : CNFRefutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  48 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_36,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_158,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_167,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_363,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k3_xboole_0(A_78,B_79),k3_xboole_0(C_80,B_79)) = k3_xboole_0(k5_xboole_0(A_78,C_80),B_79) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_418,plain,(
    ! [A_5,C_80] : k5_xboole_0(A_5,k3_xboole_0(C_80,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_80),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_363])).

tff(c_428,plain,(
    ! [A_5,C_80] : k3_xboole_0(A_5,k5_xboole_0(A_5,C_80)) = k4_xboole_0(A_5,C_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_2,c_418])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_226,plain,(
    ! [B_67,A_68] :
      ( k1_tarski(B_67) = A_68
      | k1_xboole_0 = A_68
      | ~ r1_tarski(A_68,k1_tarski(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_245,plain,(
    ! [B_67,B_13] :
      ( k3_xboole_0(k1_tarski(B_67),B_13) = k1_tarski(B_67)
      | k3_xboole_0(k1_tarski(B_67),B_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_226])).

tff(c_430,plain,(
    ! [A_81,C_82] : k3_xboole_0(A_81,k5_xboole_0(A_81,C_82)) = k4_xboole_0(A_81,C_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_2,c_418])).

tff(c_465,plain,(
    ! [B_67,C_82] :
      ( k4_xboole_0(k1_tarski(B_67),C_82) = k1_tarski(B_67)
      | k3_xboole_0(k1_tarski(B_67),k5_xboole_0(k1_tarski(B_67),C_82)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_430])).

tff(c_5961,plain,(
    ! [B_201,C_202] :
      ( k4_xboole_0(k1_tarski(B_201),C_202) = k1_tarski(B_201)
      | k4_xboole_0(k1_tarski(B_201),C_202) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_465])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6077,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5961,c_34])).

tff(c_6120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_6077])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.35/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.28  
% 6.35/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.29  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.35/2.29  
% 6.35/2.29  %Foreground sorts:
% 6.35/2.29  
% 6.35/2.29  
% 6.35/2.29  %Background operators:
% 6.35/2.29  
% 6.35/2.29  
% 6.35/2.29  %Foreground operators:
% 6.35/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.35/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.35/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.35/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.35/2.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.35/2.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.35/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.35/2.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.35/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.35/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.35/2.29  tff('#skF_2', type, '#skF_2': $i).
% 6.35/2.29  tff('#skF_1', type, '#skF_1': $i).
% 6.35/2.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.35/2.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.35/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.35/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.35/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.35/2.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.35/2.29  
% 6.35/2.30  tff(f_62, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 6.35/2.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.35/2.30  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.35/2.30  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.35/2.30  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 6.35/2.30  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.35/2.30  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.35/2.30  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.35/2.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.35/2.30  tff(c_158, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.35/2.30  tff(c_167, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_158])).
% 6.35/2.30  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.35/2.30  tff(c_363, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k3_xboole_0(A_78, B_79), k3_xboole_0(C_80, B_79))=k3_xboole_0(k5_xboole_0(A_78, C_80), B_79))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.35/2.30  tff(c_418, plain, (![A_5, C_80]: (k5_xboole_0(A_5, k3_xboole_0(C_80, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_80), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_363])).
% 6.35/2.30  tff(c_428, plain, (![A_5, C_80]: (k3_xboole_0(A_5, k5_xboole_0(A_5, C_80))=k4_xboole_0(A_5, C_80))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_2, c_418])).
% 6.35/2.30  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.35/2.30  tff(c_226, plain, (![B_67, A_68]: (k1_tarski(B_67)=A_68 | k1_xboole_0=A_68 | ~r1_tarski(A_68, k1_tarski(B_67)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.35/2.30  tff(c_245, plain, (![B_67, B_13]: (k3_xboole_0(k1_tarski(B_67), B_13)=k1_tarski(B_67) | k3_xboole_0(k1_tarski(B_67), B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_226])).
% 6.35/2.30  tff(c_430, plain, (![A_81, C_82]: (k3_xboole_0(A_81, k5_xboole_0(A_81, C_82))=k4_xboole_0(A_81, C_82))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_2, c_418])).
% 6.35/2.30  tff(c_465, plain, (![B_67, C_82]: (k4_xboole_0(k1_tarski(B_67), C_82)=k1_tarski(B_67) | k3_xboole_0(k1_tarski(B_67), k5_xboole_0(k1_tarski(B_67), C_82))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_245, c_430])).
% 6.35/2.30  tff(c_5961, plain, (![B_201, C_202]: (k4_xboole_0(k1_tarski(B_201), C_202)=k1_tarski(B_201) | k4_xboole_0(k1_tarski(B_201), C_202)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_428, c_465])).
% 6.35/2.30  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.35/2.30  tff(c_6077, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5961, c_34])).
% 6.35/2.30  tff(c_6120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_6077])).
% 6.35/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.30  
% 6.35/2.30  Inference rules
% 6.35/2.30  ----------------------
% 6.35/2.30  #Ref     : 0
% 6.35/2.30  #Sup     : 1585
% 6.35/2.30  #Fact    : 2
% 6.35/2.30  #Define  : 0
% 6.35/2.30  #Split   : 1
% 6.35/2.30  #Chain   : 0
% 6.35/2.30  #Close   : 0
% 6.35/2.30  
% 6.35/2.30  Ordering : KBO
% 6.35/2.30  
% 6.35/2.30  Simplification rules
% 6.35/2.30  ----------------------
% 6.35/2.30  #Subsume      : 117
% 6.35/2.30  #Demod        : 1266
% 6.35/2.30  #Tautology    : 679
% 6.35/2.30  #SimpNegUnit  : 6
% 6.35/2.30  #BackRed      : 4
% 6.35/2.30  
% 6.35/2.30  #Partial instantiations: 0
% 6.35/2.30  #Strategies tried      : 1
% 6.64/2.30  
% 6.64/2.30  Timing (in seconds)
% 6.64/2.30  ----------------------
% 6.64/2.30  Preprocessing        : 0.34
% 6.64/2.30  Parsing              : 0.18
% 6.64/2.30  CNF conversion       : 0.02
% 6.64/2.30  Main loop            : 1.20
% 6.64/2.30  Inferencing          : 0.33
% 6.64/2.30  Reduction            : 0.59
% 6.64/2.30  Demodulation         : 0.50
% 6.64/2.30  BG Simplification    : 0.05
% 6.64/2.30  Subsumption          : 0.17
% 6.64/2.30  Abstraction          : 0.07
% 6.64/2.30  MUC search           : 0.00
% 6.64/2.30  Cooper               : 0.00
% 6.64/2.30  Total                : 1.56
% 6.64/2.30  Index Insertion      : 0.00
% 6.64/2.30  Index Deletion       : 0.00
% 6.64/2.30  Index Matching       : 0.00
% 6.64/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
