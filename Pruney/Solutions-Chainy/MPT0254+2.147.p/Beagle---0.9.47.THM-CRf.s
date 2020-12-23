%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:37 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   43 (  65 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  53 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_260,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_278,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_260])).

tff(c_287,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_278])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_108])).

tff(c_150,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_156,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_111,c_150])).

tff(c_162,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_156])).

tff(c_38,plain,(
    ! [B_48] : k4_xboole_0(k1_tarski(B_48),k1_tarski(B_48)) != k1_tarski(B_48) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_38])).

tff(c_181,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_162,c_175])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.22  
% 1.95/1.23  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.95/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.95/1.23  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.95/1.23  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.95/1.23  tff(f_72, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.95/1.23  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.95/1.23  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.95/1.23  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.95/1.23  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.23  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.23  tff(c_260, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.23  tff(c_278, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_260])).
% 1.95/1.23  tff(c_287, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_278])).
% 1.95/1.23  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.23  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.95/1.23  tff(c_108, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.23  tff(c_111, plain, (r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_108])).
% 1.95/1.23  tff(c_150, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.23  tff(c_156, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_111, c_150])).
% 1.95/1.23  tff(c_162, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_156])).
% 1.95/1.23  tff(c_38, plain, (![B_48]: (k4_xboole_0(k1_tarski(B_48), k1_tarski(B_48))!=k1_tarski(B_48))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.23  tff(c_175, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_162, c_38])).
% 1.95/1.23  tff(c_181, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_162, c_162, c_175])).
% 1.95/1.23  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_287, c_181])).
% 1.95/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  Inference rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Ref     : 0
% 1.95/1.23  #Sup     : 63
% 1.95/1.23  #Fact    : 0
% 1.95/1.23  #Define  : 0
% 1.95/1.23  #Split   : 0
% 1.95/1.23  #Chain   : 0
% 1.95/1.23  #Close   : 0
% 1.95/1.23  
% 1.95/1.23  Ordering : KBO
% 1.95/1.23  
% 1.95/1.23  Simplification rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Subsume      : 1
% 1.95/1.23  #Demod        : 23
% 1.95/1.23  #Tautology    : 47
% 1.95/1.23  #SimpNegUnit  : 0
% 1.95/1.23  #BackRed      : 4
% 1.95/1.23  
% 1.95/1.23  #Partial instantiations: 0
% 1.95/1.23  #Strategies tried      : 1
% 1.95/1.23  
% 1.95/1.23  Timing (in seconds)
% 1.95/1.23  ----------------------
% 1.95/1.23  Preprocessing        : 0.31
% 1.95/1.23  Parsing              : 0.17
% 1.95/1.23  CNF conversion       : 0.02
% 1.95/1.23  Main loop            : 0.15
% 1.95/1.23  Inferencing          : 0.05
% 1.95/1.23  Reduction            : 0.05
% 1.95/1.23  Demodulation         : 0.04
% 1.95/1.23  BG Simplification    : 0.01
% 1.95/1.23  Subsumption          : 0.02
% 1.95/1.23  Abstraction          : 0.01
% 1.95/1.23  MUC search           : 0.00
% 1.95/1.23  Cooper               : 0.00
% 1.95/1.23  Total                : 0.49
% 1.95/1.23  Index Insertion      : 0.00
% 1.95/1.23  Index Deletion       : 0.00
% 1.95/1.23  Index Matching       : 0.00
% 1.95/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
