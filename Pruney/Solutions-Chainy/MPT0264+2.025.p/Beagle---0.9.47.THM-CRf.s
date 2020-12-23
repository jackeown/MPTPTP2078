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
% DateTime   : Thu Dec  3 09:52:24 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.08s
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
%$ r2_hidden > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(c_262,plain,(
    ! [D_51] :
      ( r2_hidden(D_51,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_51,'#skF_7')
      | ~ r2_hidden(D_51,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_216])).

tff(c_269,plain,
    ( r2_hidden('#skF_6',k1_tarski('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_262])).

tff(c_277,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_269])).

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

tff(c_286,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_277,c_195])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_286])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.23  %$ r2_hidden > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.97/1.23  
% 1.97/1.23  %Foreground sorts:
% 1.97/1.23  
% 1.97/1.23  
% 1.97/1.23  %Background operators:
% 1.97/1.23  
% 1.97/1.23  
% 1.97/1.23  %Foreground operators:
% 1.97/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.97/1.23  tff('#skF_7', type, '#skF_7': $i).
% 1.97/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.97/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.23  
% 2.08/1.24  tff(f_60, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.08/1.24  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.08/1.24  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.08/1.24  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.24  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.08/1.24  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.08/1.24  tff(c_26, plain, (![D_16, A_11]: (r2_hidden(D_16, k2_tarski(A_11, D_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.24  tff(c_50, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.08/1.24  tff(c_216, plain, (![D_46, A_47, B_48]: (r2_hidden(D_46, k3_xboole_0(A_47, B_48)) | ~r2_hidden(D_46, B_48) | ~r2_hidden(D_46, A_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.08/1.24  tff(c_262, plain, (![D_51]: (r2_hidden(D_51, k1_tarski('#skF_5')) | ~r2_hidden(D_51, '#skF_7') | ~r2_hidden(D_51, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_216])).
% 2.08/1.24  tff(c_269, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_26, c_262])).
% 2.08/1.24  tff(c_277, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_269])).
% 2.08/1.24  tff(c_42, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.24  tff(c_183, plain, (![D_40, B_41, A_42]: (D_40=B_41 | D_40=A_42 | ~r2_hidden(D_40, k2_tarski(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.24  tff(c_195, plain, (![D_40, A_17]: (D_40=A_17 | D_40=A_17 | ~r2_hidden(D_40, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_183])).
% 2.08/1.24  tff(c_286, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_277, c_195])).
% 2.08/1.24  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_286])).
% 2.08/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  Inference rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Ref     : 0
% 2.08/1.24  #Sup     : 60
% 2.08/1.24  #Fact    : 0
% 2.08/1.24  #Define  : 0
% 2.08/1.24  #Split   : 0
% 2.08/1.24  #Chain   : 0
% 2.08/1.24  #Close   : 0
% 2.08/1.24  
% 2.08/1.24  Ordering : KBO
% 2.08/1.24  
% 2.08/1.24  Simplification rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Subsume      : 8
% 2.08/1.24  #Demod        : 8
% 2.08/1.24  #Tautology    : 34
% 2.08/1.24  #SimpNegUnit  : 3
% 2.08/1.24  #BackRed      : 0
% 2.08/1.24  
% 2.08/1.24  #Partial instantiations: 0
% 2.08/1.24  #Strategies tried      : 1
% 2.08/1.24  
% 2.08/1.24  Timing (in seconds)
% 2.08/1.24  ----------------------
% 2.08/1.24  Preprocessing        : 0.30
% 2.08/1.24  Parsing              : 0.15
% 2.08/1.24  CNF conversion       : 0.02
% 2.08/1.24  Main loop            : 0.18
% 2.08/1.25  Inferencing          : 0.06
% 2.08/1.25  Reduction            : 0.07
% 2.08/1.25  Demodulation         : 0.05
% 2.08/1.25  BG Simplification    : 0.01
% 2.08/1.25  Subsumption          : 0.04
% 2.08/1.25  Abstraction          : 0.01
% 2.08/1.25  MUC search           : 0.00
% 2.08/1.25  Cooper               : 0.00
% 2.08/1.25  Total                : 0.50
% 2.08/1.25  Index Insertion      : 0.00
% 2.08/1.25  Index Deletion       : 0.00
% 2.08/1.25  Index Matching       : 0.00
% 2.08/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
