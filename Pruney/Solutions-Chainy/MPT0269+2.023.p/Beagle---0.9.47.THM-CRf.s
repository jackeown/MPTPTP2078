%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:47 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.73s
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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

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

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_324,plain,(
    ! [B_81,A_82] :
      ( k1_tarski(B_81) = A_82
      | k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,k1_tarski(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4212,plain,(
    ! [B_170,A_171] :
      ( k1_tarski(B_170) = A_171
      | k1_xboole_0 = A_171
      | k4_xboole_0(A_171,k1_tarski(B_170)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_324])).

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
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.99  
% 4.73/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.99  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.73/1.99  
% 4.73/1.99  %Foreground sorts:
% 4.73/1.99  
% 4.73/1.99  
% 4.73/1.99  %Background operators:
% 4.73/1.99  
% 4.73/1.99  
% 4.73/1.99  %Foreground operators:
% 4.73/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.73/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.73/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.73/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.73/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.73/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.73/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.73/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.73/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.73/1.99  tff('#skF_1', type, '#skF_1': $i).
% 4.73/1.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.73/1.99  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.73/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.73/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.73/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.73/1.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.73/1.99  
% 4.73/2.00  tff(f_79, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.73/2.00  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 4.73/2.00  tff(f_69, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 4.73/2.00  tff(c_48, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.73/2.00  tff(c_46, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.73/2.00  tff(c_50, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.73/2.00  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.73/2.00  tff(c_324, plain, (![B_81, A_82]: (k1_tarski(B_81)=A_82 | k1_xboole_0=A_82 | ~r1_tarski(A_82, k1_tarski(B_81)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.73/2.00  tff(c_4212, plain, (![B_170, A_171]: (k1_tarski(B_170)=A_171 | k1_xboole_0=A_171 | k4_xboole_0(A_171, k1_tarski(B_170))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_324])).
% 4.73/2.00  tff(c_4230, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_50, c_4212])).
% 4.73/2.00  tff(c_4241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_4230])).
% 4.73/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/2.00  
% 4.73/2.00  Inference rules
% 4.73/2.00  ----------------------
% 4.73/2.00  #Ref     : 0
% 4.73/2.00  #Sup     : 1051
% 4.73/2.00  #Fact    : 0
% 4.73/2.00  #Define  : 0
% 4.73/2.00  #Split   : 0
% 4.73/2.00  #Chain   : 0
% 4.73/2.00  #Close   : 0
% 4.73/2.00  
% 4.73/2.00  Ordering : KBO
% 4.73/2.00  
% 4.73/2.00  Simplification rules
% 4.73/2.00  ----------------------
% 4.73/2.00  #Subsume      : 20
% 4.73/2.00  #Demod        : 1017
% 4.73/2.00  #Tautology    : 657
% 4.73/2.00  #SimpNegUnit  : 1
% 4.73/2.00  #BackRed      : 0
% 4.73/2.00  
% 4.73/2.00  #Partial instantiations: 0
% 4.73/2.00  #Strategies tried      : 1
% 4.73/2.00  
% 4.73/2.00  Timing (in seconds)
% 4.73/2.00  ----------------------
% 4.73/2.00  Preprocessing        : 0.32
% 4.73/2.00  Parsing              : 0.16
% 4.73/2.00  CNF conversion       : 0.02
% 4.73/2.00  Main loop            : 0.88
% 4.73/2.00  Inferencing          : 0.25
% 4.73/2.00  Reduction            : 0.43
% 4.73/2.00  Demodulation         : 0.38
% 4.73/2.00  BG Simplification    : 0.04
% 4.73/2.00  Subsumption          : 0.12
% 4.73/2.00  Abstraction          : 0.04
% 4.73/2.00  MUC search           : 0.00
% 4.73/2.00  Cooper               : 0.00
% 4.73/2.00  Total                : 1.22
% 4.73/2.00  Index Insertion      : 0.00
% 4.73/2.00  Index Deletion       : 0.00
% 4.73/2.01  Index Matching       : 0.00
% 4.73/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
