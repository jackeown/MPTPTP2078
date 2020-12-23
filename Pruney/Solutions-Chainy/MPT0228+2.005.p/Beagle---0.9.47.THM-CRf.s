%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:52 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_60,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2867,plain,(
    ! [B_1734,C_1735,A_1736] :
      ( ~ r2_hidden(B_1734,C_1735)
      | k4_xboole_0(k2_tarski(A_1736,B_1734),C_1735) = k1_tarski(A_1736)
      | r2_hidden(A_1736,C_1735) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_58,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2918,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2867,c_58])).

tff(c_2973,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2918])).

tff(c_22,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2988,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2973,c_22])).

tff(c_3027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:50:24 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/2.34  
% 5.09/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/2.34  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 5.09/2.34  
% 5.09/2.34  %Foreground sorts:
% 5.09/2.34  
% 5.09/2.34  
% 5.09/2.34  %Background operators:
% 5.09/2.34  
% 5.09/2.34  
% 5.09/2.34  %Foreground operators:
% 5.09/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.09/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.09/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.09/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.09/2.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.09/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.09/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.09/2.34  tff('#skF_5', type, '#skF_5': $i).
% 5.09/2.34  tff('#skF_6', type, '#skF_6': $i).
% 5.09/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.09/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/2.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.09/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.09/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.09/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.09/2.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.09/2.34  
% 5.09/2.35  tff(f_117, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 5.09/2.35  tff(f_82, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.09/2.35  tff(f_99, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 5.09/2.35  tff(c_60, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.09/2.35  tff(c_24, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.09/2.35  tff(c_2867, plain, (![B_1734, C_1735, A_1736]: (~r2_hidden(B_1734, C_1735) | k4_xboole_0(k2_tarski(A_1736, B_1734), C_1735)=k1_tarski(A_1736) | r2_hidden(A_1736, C_1735))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.09/2.35  tff(c_58, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.09/2.35  tff(c_2918, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2867, c_58])).
% 5.09/2.35  tff(c_2973, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2918])).
% 5.09/2.35  tff(c_22, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.09/2.35  tff(c_2988, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2973, c_22])).
% 5.09/2.35  tff(c_3027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2988])).
% 5.09/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/2.35  
% 5.09/2.35  Inference rules
% 5.09/2.35  ----------------------
% 5.09/2.35  #Ref     : 0
% 5.09/2.35  #Sup     : 452
% 5.09/2.35  #Fact    : 0
% 5.09/2.35  #Define  : 0
% 5.09/2.35  #Split   : 1
% 5.09/2.35  #Chain   : 0
% 5.09/2.35  #Close   : 0
% 5.09/2.35  
% 5.09/2.35  Ordering : KBO
% 5.09/2.35  
% 5.09/2.35  Simplification rules
% 5.09/2.35  ----------------------
% 5.09/2.35  #Subsume      : 49
% 5.09/2.35  #Demod        : 181
% 5.09/2.35  #Tautology    : 190
% 5.09/2.35  #SimpNegUnit  : 48
% 5.09/2.35  #BackRed      : 1
% 5.09/2.35  
% 5.09/2.35  #Partial instantiations: 975
% 5.09/2.35  #Strategies tried      : 1
% 5.09/2.35  
% 5.09/2.35  Timing (in seconds)
% 5.09/2.35  ----------------------
% 5.09/2.36  Preprocessing        : 0.57
% 5.09/2.36  Parsing              : 0.30
% 5.09/2.36  CNF conversion       : 0.04
% 5.09/2.36  Main loop            : 1.00
% 5.09/2.36  Inferencing          : 0.44
% 5.09/2.36  Reduction            : 0.28
% 5.09/2.36  Demodulation         : 0.19
% 5.09/2.36  BG Simplification    : 0.05
% 5.09/2.36  Subsumption          : 0.17
% 5.09/2.36  Abstraction          : 0.04
% 5.09/2.36  MUC search           : 0.00
% 5.09/2.36  Cooper               : 0.00
% 5.09/2.36  Total                : 1.60
% 5.09/2.36  Index Insertion      : 0.00
% 5.09/2.36  Index Deletion       : 0.00
% 5.09/2.36  Index Matching       : 0.00
% 5.09/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
