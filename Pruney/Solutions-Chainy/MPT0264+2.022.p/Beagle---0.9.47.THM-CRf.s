%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:23 EST 2020

% Result     : Theorem 4.97s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [D_23,A_18] : r2_hidden(D_23,k2_tarski(A_18,D_23)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_179,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_200,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_7')) = k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_179])).

tff(c_1155,plain,(
    ! [D_997,A_998,B_999] :
      ( r2_hidden(D_997,k4_xboole_0(A_998,B_999))
      | r2_hidden(D_997,B_999)
      | ~ r2_hidden(D_997,A_998) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2611,plain,(
    ! [D_1687] :
      ( r2_hidden(D_1687,k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9'))
      | r2_hidden(D_1687,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_1687,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_1155])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4573,plain,(
    ! [D_2296] :
      ( ~ r2_hidden(D_2296,'#skF_9')
      | r2_hidden(D_2296,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_2296,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2611,c_6])).

tff(c_4615,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_4573])).

tff(c_4628,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4615])).

tff(c_26,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4637,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4628,c_26])).

tff(c_4677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:35:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.97  
% 4.97/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.97  %$ r2_hidden > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 4.97/1.97  
% 4.97/1.97  %Foreground sorts:
% 4.97/1.97  
% 4.97/1.97  
% 4.97/1.97  %Background operators:
% 4.97/1.97  
% 4.97/1.97  
% 4.97/1.97  %Foreground operators:
% 4.97/1.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.97/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.97/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.97/1.97  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.97/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.97/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.97/1.97  tff('#skF_7', type, '#skF_7': $i).
% 4.97/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.97/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.97/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.97/1.97  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.97/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.97/1.97  tff('#skF_9', type, '#skF_9': $i).
% 4.97/1.97  tff('#skF_8', type, '#skF_8': $i).
% 4.97/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.97/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.97/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.97/1.97  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.97/1.97  
% 4.97/1.98  tff(f_70, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 4.97/1.98  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.97/1.98  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.97/1.98  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.97/1.98  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.97/1.98  tff(c_60, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.97/1.98  tff(c_62, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.97/1.98  tff(c_40, plain, (![D_23, A_18]: (r2_hidden(D_23, k2_tarski(A_18, D_23)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.97/1.98  tff(c_64, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.97/1.98  tff(c_179, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.97/1.98  tff(c_200, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_7'))=k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_64, c_179])).
% 4.97/1.98  tff(c_1155, plain, (![D_997, A_998, B_999]: (r2_hidden(D_997, k4_xboole_0(A_998, B_999)) | r2_hidden(D_997, B_999) | ~r2_hidden(D_997, A_998))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.97/1.98  tff(c_2611, plain, (![D_1687]: (r2_hidden(D_1687, k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')) | r2_hidden(D_1687, k1_tarski('#skF_7')) | ~r2_hidden(D_1687, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_200, c_1155])).
% 4.97/1.98  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.97/1.98  tff(c_4573, plain, (![D_2296]: (~r2_hidden(D_2296, '#skF_9') | r2_hidden(D_2296, k1_tarski('#skF_7')) | ~r2_hidden(D_2296, k2_tarski('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_2611, c_6])).
% 4.97/1.98  tff(c_4615, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_40, c_4573])).
% 4.97/1.98  tff(c_4628, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4615])).
% 4.97/1.98  tff(c_26, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.97/1.98  tff(c_4637, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_4628, c_26])).
% 4.97/1.98  tff(c_4677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_4637])).
% 4.97/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.98  
% 4.97/1.98  Inference rules
% 4.97/1.98  ----------------------
% 4.97/1.98  #Ref     : 0
% 4.97/1.98  #Sup     : 985
% 4.97/1.98  #Fact    : 0
% 4.97/1.98  #Define  : 0
% 4.97/1.98  #Split   : 2
% 4.97/1.98  #Chain   : 0
% 4.97/1.98  #Close   : 0
% 4.97/1.98  
% 4.97/1.98  Ordering : KBO
% 4.97/1.98  
% 4.97/1.98  Simplification rules
% 4.97/1.98  ----------------------
% 4.97/1.98  #Subsume      : 175
% 4.97/1.98  #Demod        : 1057
% 4.97/1.98  #Tautology    : 464
% 4.97/1.98  #SimpNegUnit  : 1
% 4.97/1.98  #BackRed      : 0
% 4.97/1.98  
% 4.97/1.98  #Partial instantiations: 1120
% 4.97/1.98  #Strategies tried      : 1
% 4.97/1.98  
% 4.97/1.98  Timing (in seconds)
% 4.97/1.98  ----------------------
% 5.24/1.98  Preprocessing        : 0.31
% 5.24/1.98  Parsing              : 0.16
% 5.24/1.98  CNF conversion       : 0.02
% 5.24/1.98  Main loop            : 0.91
% 5.24/1.98  Inferencing          : 0.31
% 5.24/1.98  Reduction            : 0.39
% 5.24/1.98  Demodulation         : 0.33
% 5.24/1.98  BG Simplification    : 0.03
% 5.24/1.98  Subsumption          : 0.13
% 5.24/1.98  Abstraction          : 0.04
% 5.24/1.98  MUC search           : 0.00
% 5.24/1.98  Cooper               : 0.00
% 5.24/1.98  Total                : 1.24
% 5.24/1.98  Index Insertion      : 0.00
% 5.24/1.98  Index Deletion       : 0.00
% 5.24/1.98  Index Matching       : 0.00
% 5.24/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
