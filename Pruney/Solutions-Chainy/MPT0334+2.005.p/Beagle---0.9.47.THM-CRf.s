%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:51 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  29 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,k1_tarski(B_22)) = A_21
      | r2_hidden(B_22,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_168,plain,(
    ! [A_48,C_49,B_50] : k2_xboole_0(k4_xboole_0(A_48,C_49),k4_xboole_0(B_50,C_49)) = k4_xboole_0(k2_xboole_0(A_48,B_50),C_49) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1096,plain,(
    ! [A_78,A_79,B_80] :
      ( k4_xboole_0(k2_xboole_0(A_78,A_79),k1_tarski(B_80)) = k2_xboole_0(k4_xboole_0(A_78,k1_tarski(B_80)),A_79)
      | r2_hidden(B_80,A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_168])).

tff(c_32,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_35,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_1126,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_35])).

tff(c_1186,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1126])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1190,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1186,c_10])).

tff(c_1194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:02:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.59  
% 3.12/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.60  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.12/1.60  
% 3.12/1.60  %Foreground sorts:
% 3.12/1.60  
% 3.12/1.60  
% 3.12/1.60  %Background operators:
% 3.12/1.60  
% 3.12/1.60  
% 3.12/1.60  %Foreground operators:
% 3.12/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.12/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.12/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.12/1.60  
% 3.12/1.60  tff(f_57, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 3.12/1.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.12/1.60  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.12/1.60  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 3.12/1.60  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.12/1.60  tff(c_34, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.12/1.60  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.60  tff(c_30, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k1_tarski(B_22))=A_21 | r2_hidden(B_22, A_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.60  tff(c_168, plain, (![A_48, C_49, B_50]: (k2_xboole_0(k4_xboole_0(A_48, C_49), k4_xboole_0(B_50, C_49))=k4_xboole_0(k2_xboole_0(A_48, B_50), C_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.60  tff(c_1096, plain, (![A_78, A_79, B_80]: (k4_xboole_0(k2_xboole_0(A_78, A_79), k1_tarski(B_80))=k2_xboole_0(k4_xboole_0(A_78, k1_tarski(B_80)), A_79) | r2_hidden(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_30, c_168])).
% 3.12/1.60  tff(c_32, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.12/1.60  tff(c_35, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 3.12/1.60  tff(c_1126, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4'))) | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1096, c_35])).
% 3.12/1.60  tff(c_1186, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1126])).
% 3.12/1.60  tff(c_10, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.12/1.60  tff(c_1190, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1186, c_10])).
% 3.12/1.60  tff(c_1194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1190])).
% 3.12/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.60  
% 3.12/1.60  Inference rules
% 3.12/1.60  ----------------------
% 3.12/1.60  #Ref     : 0
% 3.12/1.60  #Sup     : 318
% 3.12/1.60  #Fact    : 0
% 3.12/1.60  #Define  : 0
% 3.12/1.60  #Split   : 1
% 3.12/1.60  #Chain   : 0
% 3.12/1.60  #Close   : 0
% 3.12/1.60  
% 3.12/1.60  Ordering : KBO
% 3.12/1.60  
% 3.12/1.60  Simplification rules
% 3.12/1.60  ----------------------
% 3.12/1.60  #Subsume      : 49
% 3.12/1.60  #Demod        : 43
% 3.12/1.60  #Tautology    : 98
% 3.12/1.60  #SimpNegUnit  : 1
% 3.12/1.60  #BackRed      : 0
% 3.12/1.60  
% 3.12/1.60  #Partial instantiations: 0
% 3.12/1.60  #Strategies tried      : 1
% 3.12/1.60  
% 3.12/1.60  Timing (in seconds)
% 3.12/1.60  ----------------------
% 3.12/1.61  Preprocessing        : 0.33
% 3.12/1.61  Parsing              : 0.17
% 3.12/1.61  CNF conversion       : 0.02
% 3.12/1.61  Main loop            : 0.46
% 3.49/1.61  Inferencing          : 0.15
% 3.49/1.61  Reduction            : 0.19
% 3.49/1.61  Demodulation         : 0.16
% 3.49/1.61  BG Simplification    : 0.03
% 3.49/1.61  Subsumption          : 0.07
% 3.49/1.61  Abstraction          : 0.03
% 3.49/1.61  MUC search           : 0.00
% 3.49/1.61  Cooper               : 0.00
% 3.49/1.61  Total                : 0.82
% 3.49/1.61  Index Insertion      : 0.00
% 3.49/1.61  Index Deletion       : 0.00
% 3.49/1.61  Index Matching       : 0.00
% 3.49/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
