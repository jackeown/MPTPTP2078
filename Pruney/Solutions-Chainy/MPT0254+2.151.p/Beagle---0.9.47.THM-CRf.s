%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:38 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  21 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_48,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_113,plain,(
    ! [A_81,B_82] :
      ( k1_xboole_0 = A_81
      | k2_xboole_0(A_81,B_82) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_117,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_113])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_173,plain,(
    ! [B_88] : k4_xboole_0(k1_tarski(B_88),k1_tarski(B_88)) != k1_tarski(B_88) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_176,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_173])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_8,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.16  
% 1.76/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.16  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.76/1.16  
% 1.76/1.16  %Foreground sorts:
% 1.76/1.16  
% 1.76/1.16  
% 1.76/1.16  %Background operators:
% 1.76/1.16  
% 1.76/1.16  
% 1.76/1.16  %Foreground operators:
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.76/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.76/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.76/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.76/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.16  
% 1.76/1.17  tff(f_78, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.76/1.17  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.76/1.17  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.76/1.17  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.76/1.17  tff(c_48, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.76/1.17  tff(c_113, plain, (![A_81, B_82]: (k1_xboole_0=A_81 | k2_xboole_0(A_81, B_82)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.76/1.17  tff(c_117, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_48, c_113])).
% 1.76/1.17  tff(c_8, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.76/1.17  tff(c_173, plain, (![B_88]: (k4_xboole_0(k1_tarski(B_88), k1_tarski(B_88))!=k1_tarski(B_88))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.76/1.17  tff(c_176, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117, c_173])).
% 1.76/1.17  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_8, c_176])).
% 1.76/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.17  
% 1.76/1.17  Inference rules
% 1.76/1.17  ----------------------
% 1.76/1.17  #Ref     : 0
% 1.76/1.17  #Sup     : 35
% 1.76/1.17  #Fact    : 0
% 1.76/1.17  #Define  : 0
% 1.76/1.17  #Split   : 0
% 1.76/1.17  #Chain   : 0
% 1.76/1.17  #Close   : 0
% 1.76/1.17  
% 1.76/1.17  Ordering : KBO
% 1.76/1.17  
% 1.76/1.17  Simplification rules
% 1.76/1.17  ----------------------
% 1.76/1.17  #Subsume      : 0
% 1.76/1.17  #Demod        : 4
% 1.76/1.17  #Tautology    : 30
% 1.76/1.17  #SimpNegUnit  : 0
% 1.76/1.17  #BackRed      : 1
% 1.76/1.17  
% 1.76/1.17  #Partial instantiations: 0
% 1.76/1.17  #Strategies tried      : 1
% 1.76/1.17  
% 1.76/1.17  Timing (in seconds)
% 1.76/1.17  ----------------------
% 1.99/1.17  Preprocessing        : 0.31
% 1.99/1.17  Parsing              : 0.16
% 1.99/1.17  CNF conversion       : 0.02
% 1.99/1.17  Main loop            : 0.11
% 1.99/1.17  Inferencing          : 0.03
% 1.99/1.17  Reduction            : 0.04
% 1.99/1.17  Demodulation         : 0.03
% 1.99/1.17  BG Simplification    : 0.02
% 1.99/1.17  Subsumption          : 0.01
% 1.99/1.17  Abstraction          : 0.01
% 1.99/1.17  MUC search           : 0.00
% 1.99/1.17  Cooper               : 0.00
% 1.99/1.17  Total                : 0.44
% 1.99/1.17  Index Insertion      : 0.00
% 1.99/1.17  Index Deletion       : 0.00
% 1.99/1.17  Index Matching       : 0.00
% 1.99/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
