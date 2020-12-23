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
% DateTime   : Thu Dec  3 09:52:46 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_315,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4212,plain,(
    ! [B_170,A_171] :
      ( k1_tarski(B_170) = A_171
      | k1_xboole_0 = A_171
      | k4_xboole_0(A_171,k1_tarski(B_170)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_315])).

tff(c_4230,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_4212])).

tff(c_4241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_4230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:11:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.93  
% 4.61/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.93  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.61/1.93  
% 4.61/1.93  %Foreground sorts:
% 4.61/1.93  
% 4.61/1.93  
% 4.61/1.93  %Background operators:
% 4.61/1.93  
% 4.61/1.93  
% 4.61/1.93  %Foreground operators:
% 4.61/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.61/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.61/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.61/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.61/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.61/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.61/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.93  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.93  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.61/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.61/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.61/1.93  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.93  
% 4.85/1.94  tff(f_79, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.85/1.94  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.85/1.94  tff(f_69, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 4.85/1.94  tff(c_48, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.85/1.94  tff(c_46, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.85/1.94  tff(c_50, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.85/1.94  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/1.94  tff(c_315, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.85/1.94  tff(c_4212, plain, (![B_170, A_171]: (k1_tarski(B_170)=A_171 | k1_xboole_0=A_171 | k4_xboole_0(A_171, k1_tarski(B_170))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_315])).
% 4.85/1.94  tff(c_4230, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_50, c_4212])).
% 4.85/1.94  tff(c_4241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_4230])).
% 4.85/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.94  
% 4.85/1.94  Inference rules
% 4.85/1.94  ----------------------
% 4.85/1.94  #Ref     : 0
% 4.85/1.94  #Sup     : 1051
% 4.85/1.94  #Fact    : 0
% 4.85/1.94  #Define  : 0
% 4.85/1.94  #Split   : 0
% 4.85/1.94  #Chain   : 0
% 4.85/1.94  #Close   : 0
% 4.85/1.94  
% 4.85/1.94  Ordering : KBO
% 4.85/1.94  
% 4.85/1.94  Simplification rules
% 4.85/1.94  ----------------------
% 4.85/1.94  #Subsume      : 20
% 4.85/1.94  #Demod        : 1017
% 4.85/1.94  #Tautology    : 657
% 4.85/1.94  #SimpNegUnit  : 1
% 4.85/1.94  #BackRed      : 0
% 4.85/1.94  
% 4.85/1.94  #Partial instantiations: 0
% 4.85/1.94  #Strategies tried      : 1
% 4.85/1.94  
% 4.85/1.94  Timing (in seconds)
% 4.85/1.94  ----------------------
% 4.85/1.94  Preprocessing        : 0.34
% 4.85/1.94  Parsing              : 0.19
% 4.85/1.94  CNF conversion       : 0.02
% 4.85/1.94  Main loop            : 0.81
% 4.85/1.94  Inferencing          : 0.25
% 4.85/1.94  Reduction            : 0.38
% 4.85/1.94  Demodulation         : 0.33
% 4.85/1.94  BG Simplification    : 0.03
% 4.85/1.94  Subsumption          : 0.10
% 4.85/1.94  Abstraction          : 0.04
% 4.85/1.94  MUC search           : 0.00
% 4.85/1.94  Cooper               : 0.00
% 4.85/1.94  Total                : 1.17
% 4.85/1.94  Index Insertion      : 0.00
% 4.85/1.95  Index Deletion       : 0.00
% 4.85/1.95  Index Matching       : 0.00
% 4.85/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
