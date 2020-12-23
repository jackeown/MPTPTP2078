%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:24 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [D_16,A_11] : r2_hidden(D_16,k2_tarski(A_11,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_216,plain,(
    ! [D_46,A_47,B_48] :
      ( r2_hidden(D_46,k3_xboole_0(A_47,B_48))
      | ~ r2_hidden(D_46,B_48)
      | ~ r2_hidden(D_46,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_321,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_54,'#skF_7')
      | ~ r2_hidden(D_54,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_216])).

tff(c_328,plain,
    ( r2_hidden('#skF_6',k1_tarski('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_321])).

tff(c_336,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_328])).

tff(c_42,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_183,plain,(
    ! [D_40,B_41,A_42] :
      ( D_40 = B_41
      | D_40 = A_42
      | ~ r2_hidden(D_40,k2_tarski(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_195,plain,(
    ! [D_40,A_17] :
      ( D_40 = A_17
      | D_40 = A_17
      | ~ r2_hidden(D_40,k1_tarski(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_183])).

tff(c_345,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_336,c_195])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.24  
% 1.84/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.24  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.84/1.24  
% 1.84/1.24  %Foreground sorts:
% 1.84/1.24  
% 1.84/1.24  
% 1.84/1.24  %Background operators:
% 1.84/1.24  
% 1.84/1.24  
% 1.84/1.24  %Foreground operators:
% 1.84/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.84/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.84/1.24  tff('#skF_7', type, '#skF_7': $i).
% 1.84/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.84/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.84/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.24  
% 1.84/1.25  tff(f_60, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 1.84/1.25  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.84/1.25  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.84/1.25  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.84/1.25  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.25  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.25  tff(c_26, plain, (![D_16, A_11]: (r2_hidden(D_16, k2_tarski(A_11, D_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.84/1.25  tff(c_50, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.25  tff(c_216, plain, (![D_46, A_47, B_48]: (r2_hidden(D_46, k3_xboole_0(A_47, B_48)) | ~r2_hidden(D_46, B_48) | ~r2_hidden(D_46, A_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.25  tff(c_321, plain, (![D_54]: (r2_hidden(D_54, k1_tarski('#skF_5')) | ~r2_hidden(D_54, '#skF_7') | ~r2_hidden(D_54, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_216])).
% 1.84/1.25  tff(c_328, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_26, c_321])).
% 1.84/1.25  tff(c_336, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_328])).
% 1.84/1.25  tff(c_42, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.25  tff(c_183, plain, (![D_40, B_41, A_42]: (D_40=B_41 | D_40=A_42 | ~r2_hidden(D_40, k2_tarski(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.84/1.25  tff(c_195, plain, (![D_40, A_17]: (D_40=A_17 | D_40=A_17 | ~r2_hidden(D_40, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_183])).
% 1.84/1.25  tff(c_345, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_336, c_195])).
% 1.84/1.25  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_345])).
% 1.84/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.25  
% 1.84/1.25  Inference rules
% 1.84/1.25  ----------------------
% 1.84/1.25  #Ref     : 0
% 1.84/1.25  #Sup     : 76
% 1.84/1.25  #Fact    : 0
% 1.84/1.25  #Define  : 0
% 1.84/1.25  #Split   : 0
% 1.84/1.25  #Chain   : 0
% 1.84/1.25  #Close   : 0
% 1.84/1.25  
% 1.84/1.25  Ordering : KBO
% 1.84/1.25  
% 1.84/1.25  Simplification rules
% 1.84/1.25  ----------------------
% 1.84/1.25  #Subsume      : 8
% 1.84/1.25  #Demod        : 15
% 1.84/1.25  #Tautology    : 45
% 1.84/1.25  #SimpNegUnit  : 3
% 1.84/1.25  #BackRed      : 0
% 1.84/1.25  
% 1.84/1.25  #Partial instantiations: 0
% 1.84/1.25  #Strategies tried      : 1
% 1.84/1.25  
% 1.84/1.25  Timing (in seconds)
% 1.84/1.25  ----------------------
% 1.84/1.26  Preprocessing        : 0.29
% 1.84/1.26  Parsing              : 0.14
% 1.84/1.26  CNF conversion       : 0.02
% 1.84/1.26  Main loop            : 0.21
% 1.84/1.26  Inferencing          : 0.07
% 1.84/1.26  Reduction            : 0.08
% 1.84/1.26  Demodulation         : 0.06
% 1.84/1.26  BG Simplification    : 0.02
% 1.84/1.26  Subsumption          : 0.04
% 1.84/1.26  Abstraction          : 0.01
% 1.84/1.26  MUC search           : 0.00
% 1.84/1.26  Cooper               : 0.00
% 1.84/1.26  Total                : 0.53
% 1.84/1.26  Index Insertion      : 0.00
% 1.84/1.26  Index Deletion       : 0.00
% 1.84/1.26  Index Matching       : 0.00
% 1.84/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
