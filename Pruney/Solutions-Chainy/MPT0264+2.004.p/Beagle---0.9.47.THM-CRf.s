%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:21 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_63,plain,(
    ! [D_23,B_24] : r2_hidden(D_23,k2_tarski(D_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_63])).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_53,plain,(
    k3_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52])).

tff(c_141,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_141])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(k2_tarski(A_20,B_21),k1_tarski(B_21)) = k1_tarski(A_20)
      | B_21 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_416,plain,
    ( k4_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = k1_tarski('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_46])).

tff(c_432,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_416])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_459,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_7')
      | ~ r2_hidden(D_64,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_4])).

tff(c_463,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_459])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:08:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.34/1.32  
% 2.34/1.32  %Foreground sorts:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Background operators:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Foreground operators:
% 2.34/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.34/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.34/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.32  
% 2.34/1.33  tff(f_66, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.34/1.33  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.34/1.33  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.34/1.33  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.34/1.33  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.34/1.33  tff(f_57, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.34/1.33  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.34/1.33  tff(c_50, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.33  tff(c_44, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.34/1.33  tff(c_63, plain, (![D_23, B_24]: (r2_hidden(D_23, k2_tarski(D_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.33  tff(c_66, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_63])).
% 2.34/1.33  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.33  tff(c_24, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.33  tff(c_52, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.33  tff(c_53, plain, (k3_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52])).
% 2.34/1.33  tff(c_141, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.33  tff(c_153, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_53, c_141])).
% 2.34/1.33  tff(c_46, plain, (![A_20, B_21]: (k4_xboole_0(k2_tarski(A_20, B_21), k1_tarski(B_21))=k1_tarski(A_20) | B_21=A_20)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.34/1.33  tff(c_416, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')=k1_tarski('#skF_6') | '#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_153, c_46])).
% 2.34/1.33  tff(c_432, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_416])).
% 2.34/1.33  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.33  tff(c_459, plain, (![D_64]: (~r2_hidden(D_64, '#skF_7') | ~r2_hidden(D_64, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_432, c_4])).
% 2.34/1.33  tff(c_463, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_66, c_459])).
% 2.34/1.33  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_463])).
% 2.34/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.33  
% 2.34/1.33  Inference rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Ref     : 0
% 2.34/1.33  #Sup     : 107
% 2.34/1.33  #Fact    : 0
% 2.34/1.33  #Define  : 0
% 2.34/1.33  #Split   : 0
% 2.34/1.33  #Chain   : 0
% 2.34/1.33  #Close   : 0
% 2.34/1.33  
% 2.34/1.33  Ordering : KBO
% 2.34/1.33  
% 2.34/1.33  Simplification rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Subsume      : 13
% 2.34/1.33  #Demod        : 37
% 2.34/1.33  #Tautology    : 60
% 2.34/1.33  #SimpNegUnit  : 3
% 2.34/1.33  #BackRed      : 1
% 2.34/1.33  
% 2.34/1.33  #Partial instantiations: 0
% 2.34/1.33  #Strategies tried      : 1
% 2.34/1.33  
% 2.34/1.33  Timing (in seconds)
% 2.34/1.33  ----------------------
% 2.34/1.34  Preprocessing        : 0.31
% 2.34/1.34  Parsing              : 0.15
% 2.34/1.34  CNF conversion       : 0.02
% 2.34/1.34  Main loop            : 0.26
% 2.34/1.34  Inferencing          : 0.08
% 2.34/1.34  Reduction            : 0.10
% 2.34/1.34  Demodulation         : 0.08
% 2.34/1.34  BG Simplification    : 0.02
% 2.34/1.34  Subsumption          : 0.05
% 2.34/1.34  Abstraction          : 0.01
% 2.34/1.34  MUC search           : 0.00
% 2.34/1.34  Cooper               : 0.00
% 2.34/1.34  Total                : 0.60
% 2.34/1.34  Index Insertion      : 0.00
% 2.34/1.34  Index Deletion       : 0.00
% 2.34/1.34  Index Matching       : 0.00
% 2.34/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
