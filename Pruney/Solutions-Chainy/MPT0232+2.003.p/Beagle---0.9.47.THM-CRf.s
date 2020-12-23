%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:20 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   45 (  53 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_66,plain,(
    ! [A_29,B_30] : r1_tarski(k1_tarski(A_29),k2_tarski(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [D_25,B_21] : r2_hidden(D_25,k2_tarski(D_25,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_8','#skF_7'),k1_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_70])).

tff(c_208,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_223,plain,(
    k3_xboole_0(k2_tarski('#skF_8','#skF_7'),k1_tarski('#skF_9')) = k2_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_208])).

tff(c_290,plain,(
    ! [D_58,B_59,A_60] :
      ( r2_hidden(D_58,B_59)
      | ~ r2_hidden(D_58,k3_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_419,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_71,k2_tarski('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_290])).

tff(c_428,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_419])).

tff(c_32,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_433,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_428,c_32])).

tff(c_68,plain,(
    k2_tarski('#skF_7','#skF_8') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_71,plain,(
    k2_tarski('#skF_8','#skF_7') != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_68])).

tff(c_253,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_259,plain,
    ( k2_tarski('#skF_8','#skF_7') = k1_tarski('#skF_9')
    | ~ r1_tarski(k1_tarski('#skF_9'),k2_tarski('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_72,c_253])).

tff(c_266,plain,(
    ~ r1_tarski(k1_tarski('#skF_9'),k2_tarski('#skF_8','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_259])).

tff(c_925,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),k2_tarski('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_266])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.38  
% 2.76/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.38  %$ r2_hidden > r1_tarski > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.76/1.38  
% 2.76/1.38  %Foreground sorts:
% 2.76/1.38  
% 2.76/1.38  
% 2.76/1.38  %Background operators:
% 2.76/1.38  
% 2.76/1.38  
% 2.76/1.38  %Foreground operators:
% 2.76/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.76/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.76/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.76/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.76/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.76/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.76/1.38  
% 2.76/1.39  tff(f_70, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.76/1.39  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.76/1.39  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.76/1.39  tff(f_75, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.76/1.39  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.76/1.39  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.76/1.39  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.76/1.39  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.39  tff(c_66, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), k2_tarski(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.76/1.39  tff(c_48, plain, (![D_25, B_21]: (r2_hidden(D_25, k2_tarski(D_25, B_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.76/1.39  tff(c_30, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.39  tff(c_70, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.39  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_8', '#skF_7'), k1_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_70])).
% 2.76/1.39  tff(c_208, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.39  tff(c_223, plain, (k3_xboole_0(k2_tarski('#skF_8', '#skF_7'), k1_tarski('#skF_9'))=k2_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_208])).
% 2.76/1.39  tff(c_290, plain, (![D_58, B_59, A_60]: (r2_hidden(D_58, B_59) | ~r2_hidden(D_58, k3_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.76/1.39  tff(c_419, plain, (![D_71]: (r2_hidden(D_71, k1_tarski('#skF_9')) | ~r2_hidden(D_71, k2_tarski('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_223, c_290])).
% 2.76/1.39  tff(c_428, plain, (r2_hidden('#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_419])).
% 2.76/1.39  tff(c_32, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.39  tff(c_433, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_428, c_32])).
% 2.76/1.39  tff(c_68, plain, (k2_tarski('#skF_7', '#skF_8')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.39  tff(c_71, plain, (k2_tarski('#skF_8', '#skF_7')!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_68])).
% 2.76/1.39  tff(c_253, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.39  tff(c_259, plain, (k2_tarski('#skF_8', '#skF_7')=k1_tarski('#skF_9') | ~r1_tarski(k1_tarski('#skF_9'), k2_tarski('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_253])).
% 2.76/1.39  tff(c_266, plain, (~r1_tarski(k1_tarski('#skF_9'), k2_tarski('#skF_8', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_71, c_259])).
% 2.76/1.39  tff(c_925, plain, (~r1_tarski(k1_tarski('#skF_8'), k2_tarski('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_266])).
% 2.76/1.39  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_925])).
% 2.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  Inference rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Ref     : 0
% 2.76/1.39  #Sup     : 127
% 2.76/1.39  #Fact    : 0
% 2.76/1.39  #Define  : 0
% 2.76/1.39  #Split   : 0
% 2.76/1.39  #Chain   : 0
% 2.76/1.39  #Close   : 0
% 2.76/1.39  
% 2.76/1.40  Ordering : KBO
% 2.76/1.40  
% 2.76/1.40  Simplification rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Subsume      : 9
% 2.76/1.40  #Demod        : 36
% 2.76/1.40  #Tautology    : 67
% 2.76/1.40  #SimpNegUnit  : 1
% 2.76/1.40  #BackRed      : 7
% 2.76/1.40  
% 2.76/1.40  #Partial instantiations: 377
% 2.76/1.40  #Strategies tried      : 1
% 2.76/1.40  
% 2.76/1.40  Timing (in seconds)
% 2.76/1.40  ----------------------
% 2.76/1.40  Preprocessing        : 0.32
% 2.76/1.40  Parsing              : 0.16
% 2.76/1.40  CNF conversion       : 0.03
% 2.76/1.40  Main loop            : 0.31
% 2.76/1.40  Inferencing          : 0.13
% 2.76/1.40  Reduction            : 0.10
% 2.76/1.40  Demodulation         : 0.08
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.05
% 2.76/1.40  Abstraction          : 0.01
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.66
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
