%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:23 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_52,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_56,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [D_19,A_14] : r2_hidden(D_19,k2_tarski(A_14,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_385,plain,(
    ! [D_559,A_560,B_561] :
      ( r2_hidden(D_559,k3_xboole_0(A_560,B_561))
      | ~ r2_hidden(D_559,B_561)
      | ~ r2_hidden(D_559,A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_453,plain,(
    ! [D_692] :
      ( r2_hidden(D_692,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_692,'#skF_9')
      | ~ r2_hidden(D_692,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_385])).

tff(c_474,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_453])).

tff(c_482,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_474])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_491,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_482,c_22])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.34  
% 2.30/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.35  %$ r2_hidden > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.30/1.35  
% 2.30/1.35  %Foreground sorts:
% 2.30/1.35  
% 2.30/1.35  
% 2.30/1.35  %Background operators:
% 2.30/1.35  
% 2.30/1.35  
% 2.30/1.35  %Foreground operators:
% 2.30/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.35  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.30/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.30/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.30/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.30/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.30/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.30/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.30/1.35  
% 2.30/1.35  tff(f_65, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.30/1.35  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.30/1.35  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.30/1.35  tff(f_43, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.30/1.35  tff(c_56, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.30/1.35  tff(c_58, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.30/1.35  tff(c_36, plain, (![D_19, A_14]: (r2_hidden(D_19, k2_tarski(A_14, D_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.30/1.35  tff(c_60, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.30/1.35  tff(c_385, plain, (![D_559, A_560, B_561]: (r2_hidden(D_559, k3_xboole_0(A_560, B_561)) | ~r2_hidden(D_559, B_561) | ~r2_hidden(D_559, A_560))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.30/1.35  tff(c_453, plain, (![D_692]: (r2_hidden(D_692, k1_tarski('#skF_7')) | ~r2_hidden(D_692, '#skF_9') | ~r2_hidden(D_692, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_385])).
% 2.30/1.35  tff(c_474, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7')) | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_36, c_453])).
% 2.30/1.35  tff(c_482, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_474])).
% 2.30/1.35  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.35  tff(c_491, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_482, c_22])).
% 2.30/1.35  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_491])).
% 2.30/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.35  
% 2.30/1.35  Inference rules
% 2.30/1.35  ----------------------
% 2.30/1.35  #Ref     : 0
% 2.30/1.35  #Sup     : 69
% 2.30/1.35  #Fact    : 0
% 2.30/1.35  #Define  : 0
% 2.30/1.35  #Split   : 0
% 2.30/1.35  #Chain   : 0
% 2.30/1.35  #Close   : 0
% 2.30/1.35  
% 2.30/1.35  Ordering : KBO
% 2.30/1.35  
% 2.30/1.35  Simplification rules
% 2.30/1.35  ----------------------
% 2.30/1.35  #Subsume      : 10
% 2.30/1.35  #Demod        : 9
% 2.30/1.35  #Tautology    : 31
% 2.30/1.35  #SimpNegUnit  : 1
% 2.30/1.35  #BackRed      : 0
% 2.30/1.35  
% 2.30/1.35  #Partial instantiations: 338
% 2.30/1.35  #Strategies tried      : 1
% 2.30/1.35  
% 2.30/1.35  Timing (in seconds)
% 2.30/1.35  ----------------------
% 2.30/1.36  Preprocessing        : 0.32
% 2.30/1.36  Parsing              : 0.16
% 2.30/1.36  CNF conversion       : 0.02
% 2.30/1.36  Main loop            : 0.25
% 2.30/1.36  Inferencing          : 0.11
% 2.30/1.36  Reduction            : 0.07
% 2.30/1.36  Demodulation         : 0.06
% 2.30/1.36  BG Simplification    : 0.02
% 2.30/1.36  Subsumption          : 0.04
% 2.30/1.36  Abstraction          : 0.01
% 2.30/1.36  MUC search           : 0.00
% 2.30/1.36  Cooper               : 0.00
% 2.30/1.36  Total                : 0.59
% 2.30/1.36  Index Insertion      : 0.00
% 2.30/1.36  Index Deletion       : 0.00
% 2.30/1.36  Index Matching       : 0.00
% 2.30/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
