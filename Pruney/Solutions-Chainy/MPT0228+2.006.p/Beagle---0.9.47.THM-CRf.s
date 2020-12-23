%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:52 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [B_73,C_74,A_75] :
      ( ~ r2_hidden(B_73,C_74)
      | k4_xboole_0(k2_tarski(A_75,B_73),C_74) = k1_tarski(A_75)
      | r2_hidden(A_75,C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_141,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_36])).

tff(c_153,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_141])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:27 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.22  
% 1.84/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.23  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.84/1.23  
% 1.84/1.23  %Foreground sorts:
% 1.84/1.23  
% 1.84/1.23  
% 1.84/1.23  %Background operators:
% 1.84/1.23  
% 1.84/1.23  
% 1.84/1.23  %Foreground operators:
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.84/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.84/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.84/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.84/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.84/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.23  
% 1.96/1.23  tff(f_61, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.96/1.23  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.96/1.23  tff(f_55, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.96/1.23  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.96/1.23  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.23  tff(c_129, plain, (![B_73, C_74, A_75]: (~r2_hidden(B_73, C_74) | k4_xboole_0(k2_tarski(A_75, B_73), C_74)=k1_tarski(A_75) | r2_hidden(A_75, C_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.23  tff(c_36, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.96/1.23  tff(c_141, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_36])).
% 1.96/1.23  tff(c_153, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_141])).
% 1.96/1.23  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.23  tff(c_157, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_153, c_2])).
% 1.96/1.23  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_157])).
% 1.96/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  Inference rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Ref     : 0
% 1.96/1.23  #Sup     : 25
% 1.96/1.23  #Fact    : 0
% 1.96/1.23  #Define  : 0
% 1.96/1.23  #Split   : 0
% 1.96/1.23  #Chain   : 0
% 1.96/1.23  #Close   : 0
% 1.96/1.23  
% 1.96/1.23  Ordering : KBO
% 1.96/1.23  
% 1.96/1.23  Simplification rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Subsume      : 1
% 1.96/1.23  #Demod        : 2
% 1.96/1.23  #Tautology    : 19
% 1.96/1.23  #SimpNegUnit  : 1
% 1.96/1.23  #BackRed      : 0
% 1.96/1.23  
% 1.96/1.23  #Partial instantiations: 0
% 1.96/1.23  #Strategies tried      : 1
% 1.96/1.23  
% 1.96/1.23  Timing (in seconds)
% 1.96/1.23  ----------------------
% 1.99/1.24  Preprocessing        : 0.29
% 1.99/1.24  Parsing              : 0.15
% 1.99/1.24  CNF conversion       : 0.02
% 1.99/1.24  Main loop            : 0.13
% 1.99/1.24  Inferencing          : 0.05
% 1.99/1.24  Reduction            : 0.04
% 1.99/1.24  Demodulation         : 0.03
% 1.99/1.24  BG Simplification    : 0.01
% 1.99/1.24  Subsumption          : 0.03
% 1.99/1.24  Abstraction          : 0.01
% 1.99/1.24  MUC search           : 0.00
% 1.99/1.24  Cooper               : 0.00
% 1.99/1.24  Total                : 0.45
% 1.99/1.24  Index Insertion      : 0.00
% 1.99/1.24  Index Deletion       : 0.00
% 1.99/1.24  Index Matching       : 0.00
% 1.99/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
