%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:02 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_22,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [B_23,A_24] : k3_tarski(k2_tarski(B_23,A_24)) = k2_xboole_0(A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_14,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_14])).

tff(c_24,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    r1_tarski(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_24])).

tff(c_220,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_224,plain,
    ( k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_108,c_220])).

tff(c_232,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_224])).

tff(c_109,plain,(
    ! [B_25,A_26] : k2_xboole_0(B_25,A_26) = k2_xboole_0(A_26,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_14])).

tff(c_124,plain,(
    ! [A_26,B_25] : r1_tarski(A_26,k2_xboole_0(B_25,A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_244,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_124])).

tff(c_20,plain,(
    ! [A_11,C_13,B_12] :
      ( r2_hidden(A_11,C_13)
      | ~ r1_tarski(k2_tarski(A_11,B_12),C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_259,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_244,c_20])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.19  
% 1.89/1.20  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.89/1.20  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.89/1.20  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.89/1.20  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.89/1.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.89/1.20  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.89/1.20  tff(c_22, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.89/1.20  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.20  tff(c_10, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.20  tff(c_70, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.20  tff(c_85, plain, (![B_23, A_24]: (k3_tarski(k2_tarski(B_23, A_24))=k2_xboole_0(A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 1.89/1.20  tff(c_14, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.20  tff(c_91, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_85, c_14])).
% 1.89/1.20  tff(c_24, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.89/1.20  tff(c_108, plain, (r1_tarski(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_24])).
% 1.89/1.20  tff(c_220, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.20  tff(c_224, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_108, c_220])).
% 1.89/1.20  tff(c_232, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_224])).
% 1.89/1.20  tff(c_109, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=k2_xboole_0(A_26, B_25))), inference(superposition, [status(thm), theory('equality')], [c_85, c_14])).
% 1.89/1.20  tff(c_124, plain, (![A_26, B_25]: (r1_tarski(A_26, k2_xboole_0(B_25, A_26)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_8])).
% 1.89/1.20  tff(c_244, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_232, c_124])).
% 1.89/1.20  tff(c_20, plain, (![A_11, C_13, B_12]: (r2_hidden(A_11, C_13) | ~r1_tarski(k2_tarski(A_11, B_12), C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.20  tff(c_259, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_244, c_20])).
% 1.89/1.20  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_259])).
% 1.89/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  Inference rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Ref     : 0
% 1.89/1.20  #Sup     : 57
% 1.89/1.20  #Fact    : 0
% 1.89/1.20  #Define  : 0
% 1.89/1.20  #Split   : 0
% 1.89/1.20  #Chain   : 0
% 1.89/1.20  #Close   : 0
% 1.89/1.20  
% 1.89/1.20  Ordering : KBO
% 1.89/1.20  
% 1.89/1.20  Simplification rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Subsume      : 3
% 1.89/1.20  #Demod        : 17
% 1.89/1.20  #Tautology    : 38
% 1.89/1.20  #SimpNegUnit  : 1
% 1.89/1.20  #BackRed      : 2
% 1.89/1.20  
% 1.89/1.20  #Partial instantiations: 0
% 1.89/1.20  #Strategies tried      : 1
% 1.89/1.20  
% 1.89/1.20  Timing (in seconds)
% 1.89/1.20  ----------------------
% 1.89/1.20  Preprocessing        : 0.28
% 1.89/1.20  Parsing              : 0.14
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.20  Main loop            : 0.17
% 1.89/1.20  Inferencing          : 0.06
% 1.89/1.20  Reduction            : 0.06
% 1.89/1.20  Demodulation         : 0.05
% 1.89/1.20  BG Simplification    : 0.01
% 1.89/1.20  Subsumption          : 0.03
% 1.89/1.20  Abstraction          : 0.01
% 1.89/1.20  MUC search           : 0.00
% 1.89/1.20  Cooper               : 0.00
% 1.89/1.20  Total                : 0.48
% 1.89/1.20  Index Insertion      : 0.00
% 1.89/1.20  Index Deletion       : 0.00
% 1.89/1.20  Index Matching       : 0.00
% 1.89/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
