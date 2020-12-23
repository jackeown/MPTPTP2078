%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:12 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   45 (  49 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  53 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(k1_tarski(A_40),B_41) = k1_xboole_0
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_428,plain,(
    ! [A_93,B_94] :
      ( ~ r2_hidden(A_93,B_94)
      | k4_xboole_0(k1_tarski(A_93),B_94) != k1_tarski(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_456,plain,(
    ! [A_93] : ~ r2_hidden(A_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_428])).

tff(c_190,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | k4_xboole_0(k1_tarski(A_72),B_73) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_203,plain,(
    ! [A_72] :
      ( r2_hidden(A_72,k1_xboole_0)
      | k1_tarski(A_72) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_190])).

tff(c_457,plain,(
    ! [A_72] : k1_tarski(A_72) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_203])).

tff(c_42,plain,(
    ! [B_43,C_44] : r1_tarski(k1_tarski(B_43),k2_tarski(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_777,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_xboole_0 = A_113
      | ~ r1_xboole_0(B_114,C_115)
      | ~ r1_tarski(A_113,C_115)
      | ~ r1_tarski(A_113,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_782,plain,(
    ! [A_116] :
      ( k1_xboole_0 = A_116
      | ~ r1_tarski(A_116,'#skF_3')
      | ~ r1_tarski(A_116,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_777])).

tff(c_794,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_782])).

tff(c_807,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_794])).

tff(c_816,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_807])).

tff(c_826,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_816])).

tff(c_831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.37  
% 2.70/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.70/1.37  
% 2.70/1.37  %Foreground sorts:
% 2.70/1.37  
% 2.70/1.37  
% 2.70/1.37  %Background operators:
% 2.70/1.37  
% 2.70/1.37  
% 2.70/1.37  %Foreground operators:
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.37  
% 2.70/1.38  tff(f_87, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.70/1.38  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.70/1.38  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.70/1.38  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.70/1.38  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.70/1.38  tff(f_81, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.70/1.38  tff(f_43, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.70/1.38  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.38  tff(c_34, plain, (![A_40, B_41]: (k4_xboole_0(k1_tarski(A_40), B_41)=k1_xboole_0 | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.70/1.38  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.38  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.38  tff(c_428, plain, (![A_93, B_94]: (~r2_hidden(A_93, B_94) | k4_xboole_0(k1_tarski(A_93), B_94)!=k1_tarski(A_93))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.38  tff(c_456, plain, (![A_93]: (~r2_hidden(A_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_428])).
% 2.70/1.38  tff(c_190, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | k4_xboole_0(k1_tarski(A_72), B_73)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.70/1.38  tff(c_203, plain, (![A_72]: (r2_hidden(A_72, k1_xboole_0) | k1_tarski(A_72)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_190])).
% 2.70/1.38  tff(c_457, plain, (![A_72]: (k1_tarski(A_72)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_456, c_203])).
% 2.70/1.38  tff(c_42, plain, (![B_43, C_44]: (r1_tarski(k1_tarski(B_43), k2_tarski(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.70/1.38  tff(c_48, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.70/1.38  tff(c_777, plain, (![A_113, B_114, C_115]: (k1_xboole_0=A_113 | ~r1_xboole_0(B_114, C_115) | ~r1_tarski(A_113, C_115) | ~r1_tarski(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.38  tff(c_782, plain, (![A_116]: (k1_xboole_0=A_116 | ~r1_tarski(A_116, '#skF_3') | ~r1_tarski(A_116, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_48, c_777])).
% 2.70/1.38  tff(c_794, plain, (k1_tarski('#skF_1')=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_42, c_782])).
% 2.70/1.38  tff(c_807, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_457, c_794])).
% 2.70/1.38  tff(c_816, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_807])).
% 2.70/1.38  tff(c_826, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_816])).
% 2.70/1.38  tff(c_831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_826])).
% 2.70/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.38  
% 2.70/1.38  Inference rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Ref     : 0
% 2.70/1.38  #Sup     : 168
% 2.70/1.38  #Fact    : 0
% 2.70/1.38  #Define  : 0
% 2.70/1.38  #Split   : 0
% 2.70/1.38  #Chain   : 0
% 2.70/1.38  #Close   : 0
% 2.70/1.38  
% 2.70/1.38  Ordering : KBO
% 2.70/1.38  
% 2.70/1.38  Simplification rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Subsume      : 10
% 2.70/1.38  #Demod        : 78
% 2.70/1.38  #Tautology    : 115
% 2.70/1.38  #SimpNegUnit  : 25
% 2.70/1.38  #BackRed      : 1
% 2.70/1.38  
% 2.70/1.38  #Partial instantiations: 0
% 2.70/1.38  #Strategies tried      : 1
% 2.70/1.38  
% 2.70/1.38  Timing (in seconds)
% 2.70/1.38  ----------------------
% 2.70/1.39  Preprocessing        : 0.32
% 2.70/1.39  Parsing              : 0.17
% 2.70/1.39  CNF conversion       : 0.02
% 2.70/1.39  Main loop            : 0.30
% 2.70/1.39  Inferencing          : 0.12
% 2.70/1.39  Reduction            : 0.10
% 2.70/1.39  Demodulation         : 0.08
% 2.70/1.39  BG Simplification    : 0.02
% 2.70/1.39  Subsumption          : 0.05
% 2.70/1.39  Abstraction          : 0.02
% 2.70/1.39  MUC search           : 0.00
% 2.70/1.39  Cooper               : 0.00
% 2.70/1.39  Total                : 0.65
% 2.70/1.39  Index Insertion      : 0.00
% 2.70/1.39  Index Deletion       : 0.00
% 2.70/1.39  Index Matching       : 0.00
% 2.70/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
