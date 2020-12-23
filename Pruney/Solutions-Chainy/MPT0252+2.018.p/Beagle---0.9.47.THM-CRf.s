%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:03 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_52,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    r1_tarski(k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_135,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,
    ( k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_56,c_135])).

tff(c_146,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_137])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_182,plain,(
    ! [D_46] :
      ( ~ r2_hidden(D_46,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_46,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_6])).

tff(c_190,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:45:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.27  
% 1.85/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.27  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.85/1.27  
% 1.85/1.27  %Foreground sorts:
% 1.85/1.27  
% 1.85/1.27  
% 1.85/1.27  %Background operators:
% 1.85/1.27  
% 1.85/1.27  
% 1.85/1.27  %Foreground operators:
% 1.85/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#skF_7', type, '#skF_7': $i).
% 1.85/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.27  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.27  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.85/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.27  
% 1.85/1.28  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.85/1.28  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.85/1.28  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.85/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.85/1.28  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.85/1.28  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.85/1.28  tff(c_52, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.85/1.28  tff(c_34, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.28  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.28  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.28  tff(c_54, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.85/1.28  tff(c_56, plain, (r1_tarski(k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_54])).
% 1.85/1.28  tff(c_135, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.85/1.28  tff(c_137, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_56, c_135])).
% 1.85/1.28  tff(c_146, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_137])).
% 1.85/1.28  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.85/1.28  tff(c_182, plain, (![D_46]: (~r2_hidden(D_46, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_46, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_6])).
% 1.85/1.28  tff(c_190, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_34, c_182])).
% 1.85/1.28  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_190])).
% 1.85/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.28  
% 1.85/1.28  Inference rules
% 1.85/1.28  ----------------------
% 1.85/1.28  #Ref     : 0
% 1.85/1.28  #Sup     : 33
% 1.85/1.28  #Fact    : 0
% 1.85/1.28  #Define  : 0
% 1.85/1.28  #Split   : 0
% 1.85/1.28  #Chain   : 0
% 1.85/1.28  #Close   : 0
% 1.85/1.28  
% 1.85/1.28  Ordering : KBO
% 1.85/1.28  
% 1.85/1.28  Simplification rules
% 1.85/1.28  ----------------------
% 1.85/1.28  #Subsume      : 4
% 1.85/1.28  #Demod        : 10
% 1.85/1.28  #Tautology    : 22
% 1.85/1.28  #SimpNegUnit  : 1
% 1.85/1.28  #BackRed      : 1
% 1.85/1.28  
% 2.13/1.28  #Partial instantiations: 0
% 2.13/1.28  #Strategies tried      : 1
% 2.13/1.28  
% 2.13/1.28  Timing (in seconds)
% 2.13/1.28  ----------------------
% 2.13/1.28  Preprocessing        : 0.33
% 2.13/1.28  Parsing              : 0.17
% 2.13/1.28  CNF conversion       : 0.03
% 2.13/1.28  Main loop            : 0.16
% 2.13/1.28  Inferencing          : 0.04
% 2.13/1.28  Reduction            : 0.06
% 2.13/1.28  Demodulation         : 0.05
% 2.13/1.28  BG Simplification    : 0.01
% 2.13/1.28  Subsumption          : 0.04
% 2.13/1.28  Abstraction          : 0.01
% 2.13/1.28  MUC search           : 0.00
% 2.13/1.28  Cooper               : 0.00
% 2.13/1.28  Total                : 0.52
% 2.13/1.28  Index Insertion      : 0.00
% 2.13/1.28  Index Deletion       : 0.00
% 2.13/1.28  Index Matching       : 0.00
% 2.13/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
