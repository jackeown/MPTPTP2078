%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:24 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.00s
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

tff(f_72,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_140,plain,(
    ! [A_58,B_59] :
      ( k1_xboole_0 = A_58
      | k2_xboole_0(A_58,B_59) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_144,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_140])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    ! [B_60] : k4_xboole_0(k1_tarski(B_60),k1_tarski(B_60)) != k1_tarski(B_60) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_169,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_166])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_8,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.18  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.00/1.18  
% 2.00/1.18  %Foreground sorts:
% 2.00/1.18  
% 2.00/1.18  
% 2.00/1.18  %Background operators:
% 2.00/1.18  
% 2.00/1.18  
% 2.00/1.18  %Foreground operators:
% 2.00/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.18  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.18  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.18  
% 2.00/1.18  tff(f_72, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.00/1.18  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.00/1.18  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.00/1.18  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.00/1.18  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.18  tff(c_140, plain, (![A_58, B_59]: (k1_xboole_0=A_58 | k2_xboole_0(A_58, B_59)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.18  tff(c_144, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_140])).
% 2.00/1.18  tff(c_8, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.18  tff(c_166, plain, (![B_60]: (k4_xboole_0(k1_tarski(B_60), k1_tarski(B_60))!=k1_tarski(B_60))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.18  tff(c_169, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_144, c_166])).
% 2.00/1.18  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_8, c_169])).
% 2.00/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.18  
% 2.00/1.18  Inference rules
% 2.00/1.18  ----------------------
% 2.00/1.18  #Ref     : 0
% 2.00/1.18  #Sup     : 35
% 2.00/1.18  #Fact    : 0
% 2.00/1.18  #Define  : 0
% 2.00/1.18  #Split   : 0
% 2.00/1.18  #Chain   : 0
% 2.00/1.18  #Close   : 0
% 2.00/1.18  
% 2.00/1.18  Ordering : KBO
% 2.00/1.18  
% 2.00/1.18  Simplification rules
% 2.00/1.18  ----------------------
% 2.00/1.18  #Subsume      : 0
% 2.00/1.18  #Demod        : 3
% 2.00/1.18  #Tautology    : 31
% 2.00/1.18  #SimpNegUnit  : 0
% 2.00/1.18  #BackRed      : 1
% 2.00/1.18  
% 2.00/1.18  #Partial instantiations: 0
% 2.00/1.18  #Strategies tried      : 1
% 2.00/1.18  
% 2.00/1.18  Timing (in seconds)
% 2.00/1.18  ----------------------
% 2.00/1.19  Preprocessing        : 0.31
% 2.00/1.19  Parsing              : 0.17
% 2.00/1.19  CNF conversion       : 0.02
% 2.00/1.19  Main loop            : 0.11
% 2.00/1.19  Inferencing          : 0.04
% 2.00/1.19  Reduction            : 0.04
% 2.00/1.19  Demodulation         : 0.03
% 2.00/1.19  BG Simplification    : 0.01
% 2.00/1.19  Subsumption          : 0.01
% 2.00/1.19  Abstraction          : 0.01
% 2.00/1.19  MUC search           : 0.00
% 2.00/1.19  Cooper               : 0.00
% 2.00/1.19  Total                : 0.44
% 2.00/1.19  Index Insertion      : 0.00
% 2.00/1.19  Index Deletion       : 0.00
% 2.00/1.19  Index Matching       : 0.00
% 2.00/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
