%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:27 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_26,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_28,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_118,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_2')) = k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_118])).

tff(c_136,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_127])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_209,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(A_38,C_39)
      | ~ r1_tarski(k2_tarski(A_38,B_40),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1501,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden(A_79,B_80)
      | k4_xboole_0(k2_tarski(A_79,B_81),B_80) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_1523,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_1501])).

tff(c_1538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:04:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.47  
% 2.78/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.47  %$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.47  
% 2.78/1.47  %Foreground sorts:
% 2.78/1.47  
% 2.78/1.47  
% 2.78/1.47  %Background operators:
% 2.78/1.47  
% 2.78/1.47  
% 2.78/1.47  %Foreground operators:
% 2.78/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.47  
% 3.03/1.48  tff(f_54, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 3.03/1.48  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.03/1.48  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.03/1.48  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.03/1.48  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.03/1.48  tff(c_26, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.48  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.03/1.48  tff(c_64, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.03/1.48  tff(c_68, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_64])).
% 3.03/1.48  tff(c_28, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.48  tff(c_118, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.03/1.48  tff(c_127, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_2'))=k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_118])).
% 3.03/1.48  tff(c_136, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_127])).
% 3.03/1.48  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.03/1.48  tff(c_209, plain, (![A_38, C_39, B_40]: (r2_hidden(A_38, C_39) | ~r1_tarski(k2_tarski(A_38, B_40), C_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.03/1.48  tff(c_1501, plain, (![A_79, B_80, B_81]: (r2_hidden(A_79, B_80) | k4_xboole_0(k2_tarski(A_79, B_81), B_80)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_209])).
% 3.03/1.48  tff(c_1523, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_136, c_1501])).
% 3.03/1.48  tff(c_1538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1523])).
% 3.03/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.48  
% 3.03/1.48  Inference rules
% 3.03/1.48  ----------------------
% 3.03/1.48  #Ref     : 0
% 3.03/1.48  #Sup     : 366
% 3.03/1.48  #Fact    : 0
% 3.03/1.48  #Define  : 0
% 3.03/1.48  #Split   : 1
% 3.03/1.48  #Chain   : 0
% 3.03/1.48  #Close   : 0
% 3.03/1.48  
% 3.03/1.48  Ordering : KBO
% 3.03/1.48  
% 3.03/1.48  Simplification rules
% 3.03/1.48  ----------------------
% 3.03/1.48  #Subsume      : 15
% 3.03/1.48  #Demod        : 380
% 3.03/1.48  #Tautology    : 292
% 3.03/1.48  #SimpNegUnit  : 1
% 3.03/1.48  #BackRed      : 0
% 3.03/1.48  
% 3.03/1.48  #Partial instantiations: 0
% 3.03/1.48  #Strategies tried      : 1
% 3.03/1.48  
% 3.03/1.48  Timing (in seconds)
% 3.03/1.48  ----------------------
% 3.03/1.48  Preprocessing        : 0.29
% 3.03/1.48  Parsing              : 0.16
% 3.03/1.48  CNF conversion       : 0.02
% 3.03/1.48  Main loop            : 0.40
% 3.03/1.48  Inferencing          : 0.13
% 3.03/1.48  Reduction            : 0.17
% 3.03/1.49  Demodulation         : 0.15
% 3.03/1.49  BG Simplification    : 0.02
% 3.03/1.49  Subsumption          : 0.05
% 3.03/1.49  Abstraction          : 0.02
% 3.03/1.49  MUC search           : 0.00
% 3.03/1.49  Cooper               : 0.00
% 3.03/1.49  Total                : 0.71
% 3.03/1.49  Index Insertion      : 0.00
% 3.03/1.49  Index Deletion       : 0.00
% 3.03/1.49  Index Matching       : 0.00
% 3.03/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
