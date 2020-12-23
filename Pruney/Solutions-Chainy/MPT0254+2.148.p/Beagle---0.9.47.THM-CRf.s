%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:37 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  35 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_225,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_234,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_237,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_234])).

tff(c_24,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( k1_xboole_0 = A_24
      | k2_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_54])).

tff(c_132,plain,(
    ! [B_32] : k4_xboole_0(k1_tarski(B_32),k1_tarski(B_32)) != k1_tarski(B_32) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_135,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_132])).

tff(c_139,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_135])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.24  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.24  
% 1.97/1.24  %Foreground sorts:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Background operators:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Foreground operators:
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.24  
% 1.97/1.25  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.97/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.97/1.25  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.97/1.25  tff(f_54, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.97/1.25  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.97/1.25  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.97/1.25  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.25  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.25  tff(c_225, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.25  tff(c_234, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_225])).
% 1.97/1.25  tff(c_237, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_234])).
% 1.97/1.25  tff(c_24, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.25  tff(c_54, plain, (![A_24, B_25]: (k1_xboole_0=A_24 | k2_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.25  tff(c_58, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_54])).
% 1.97/1.25  tff(c_132, plain, (![B_32]: (k4_xboole_0(k1_tarski(B_32), k1_tarski(B_32))!=k1_tarski(B_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.25  tff(c_135, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_58, c_132])).
% 1.97/1.25  tff(c_139, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_135])).
% 1.97/1.25  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237, c_139])).
% 1.97/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.25  
% 1.97/1.25  Inference rules
% 1.97/1.25  ----------------------
% 1.97/1.25  #Ref     : 0
% 1.97/1.25  #Sup     : 55
% 1.97/1.25  #Fact    : 0
% 1.97/1.25  #Define  : 0
% 1.97/1.25  #Split   : 1
% 1.97/1.25  #Chain   : 0
% 1.97/1.25  #Close   : 0
% 1.97/1.25  
% 1.97/1.25  Ordering : KBO
% 1.97/1.25  
% 1.97/1.25  Simplification rules
% 1.97/1.25  ----------------------
% 1.97/1.25  #Subsume      : 3
% 1.97/1.25  #Demod        : 16
% 1.97/1.25  #Tautology    : 41
% 1.97/1.25  #SimpNegUnit  : 0
% 1.97/1.25  #BackRed      : 3
% 1.97/1.25  
% 1.97/1.25  #Partial instantiations: 0
% 1.97/1.25  #Strategies tried      : 1
% 1.97/1.25  
% 1.97/1.25  Timing (in seconds)
% 1.97/1.25  ----------------------
% 1.97/1.25  Preprocessing        : 0.30
% 1.97/1.25  Parsing              : 0.16
% 1.97/1.26  CNF conversion       : 0.02
% 1.97/1.26  Main loop            : 0.14
% 1.97/1.26  Inferencing          : 0.06
% 1.97/1.26  Reduction            : 0.05
% 1.97/1.26  Demodulation         : 0.04
% 1.97/1.26  BG Simplification    : 0.01
% 1.97/1.26  Subsumption          : 0.02
% 1.97/1.26  Abstraction          : 0.01
% 1.97/1.26  MUC search           : 0.00
% 1.97/1.26  Cooper               : 0.00
% 1.97/1.26  Total                : 0.46
% 1.97/1.26  Index Insertion      : 0.00
% 1.97/1.26  Index Deletion       : 0.00
% 1.97/1.26  Index Matching       : 0.00
% 1.97/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
