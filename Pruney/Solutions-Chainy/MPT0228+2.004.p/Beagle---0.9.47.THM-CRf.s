%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:52 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [B_53,C_54,A_55] :
      ( ~ r2_hidden(B_53,C_54)
      | k4_xboole_0(k2_tarski(A_55,B_53),C_54) = k1_tarski(A_55)
      | r2_hidden(A_55,C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_156,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_46])).

tff(c_168,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_156])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_172,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:32:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.18  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 1.99/1.18  
% 1.99/1.18  %Foreground sorts:
% 1.99/1.18  
% 1.99/1.18  
% 1.99/1.18  %Background operators:
% 1.99/1.18  
% 1.99/1.18  
% 1.99/1.18  %Foreground operators:
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.99/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.18  
% 1.99/1.19  tff(f_62, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.99/1.19  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.99/1.19  tff(f_56, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.99/1.19  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.19  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.19  tff(c_144, plain, (![B_53, C_54, A_55]: (~r2_hidden(B_53, C_54) | k4_xboole_0(k2_tarski(A_55, B_53), C_54)=k1_tarski(A_55) | r2_hidden(A_55, C_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.19  tff(c_46, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.19  tff(c_156, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_46])).
% 1.99/1.19  tff(c_168, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_156])).
% 1.99/1.19  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.19  tff(c_172, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_168, c_2])).
% 1.99/1.19  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_172])).
% 1.99/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  Inference rules
% 1.99/1.19  ----------------------
% 1.99/1.19  #Ref     : 0
% 1.99/1.19  #Sup     : 26
% 1.99/1.19  #Fact    : 0
% 1.99/1.19  #Define  : 0
% 1.99/1.19  #Split   : 0
% 1.99/1.19  #Chain   : 0
% 1.99/1.19  #Close   : 0
% 1.99/1.19  
% 1.99/1.19  Ordering : KBO
% 1.99/1.19  
% 1.99/1.19  Simplification rules
% 1.99/1.19  ----------------------
% 1.99/1.19  #Subsume      : 2
% 1.99/1.19  #Demod        : 4
% 1.99/1.19  #Tautology    : 19
% 1.99/1.19  #SimpNegUnit  : 1
% 1.99/1.19  #BackRed      : 0
% 1.99/1.19  
% 1.99/1.19  #Partial instantiations: 0
% 1.99/1.19  #Strategies tried      : 1
% 1.99/1.19  
% 1.99/1.19  Timing (in seconds)
% 1.99/1.19  ----------------------
% 1.99/1.19  Preprocessing        : 0.31
% 1.99/1.19  Parsing              : 0.15
% 1.99/1.19  CNF conversion       : 0.02
% 1.99/1.19  Main loop            : 0.16
% 1.99/1.19  Inferencing          : 0.05
% 1.99/1.19  Reduction            : 0.05
% 1.99/1.19  Demodulation         : 0.04
% 1.99/1.19  BG Simplification    : 0.01
% 1.99/1.19  Subsumption          : 0.03
% 1.99/1.19  Abstraction          : 0.01
% 1.99/1.19  MUC search           : 0.00
% 1.99/1.19  Cooper               : 0.00
% 1.99/1.19  Total                : 0.49
% 1.99/1.19  Index Insertion      : 0.00
% 1.99/1.19  Index Deletion       : 0.00
% 1.99/1.19  Index Matching       : 0.00
% 1.99/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
