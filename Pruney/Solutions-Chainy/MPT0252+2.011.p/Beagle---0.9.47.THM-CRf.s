%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:02 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.87s
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
%$ r2_hidden > r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_24,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [B_24,A_25] : k3_tarski(k2_tarski(B_24,A_25)) = k2_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_63])).

tff(c_16,plain,(
    ! [A_12,B_13] : k3_tarski(k2_tarski(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_16])).

tff(c_26,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    r1_tarski(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_26])).

tff(c_152,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,
    ( k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_101,c_152])).

tff(c_163,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_154])).

tff(c_102,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_16])).

tff(c_117,plain,(
    ! [A_27,B_26] : r1_tarski(A_27,k2_xboole_0(B_26,A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_10])).

tff(c_175,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_117])).

tff(c_199,plain,(
    ! [A_35,C_36,B_37] :
      ( r2_hidden(A_35,C_36)
      | ~ r1_tarski(k2_tarski(A_35,B_37),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_202,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_199])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.18  
% 1.60/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  %$ r2_hidden > r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.18  
% 1.87/1.19  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.87/1.19  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.87/1.19  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.87/1.19  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.87/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.87/1.19  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.87/1.19  tff(c_24, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.87/1.19  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.19  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.19  tff(c_63, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.19  tff(c_78, plain, (![B_24, A_25]: (k3_tarski(k2_tarski(B_24, A_25))=k2_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_12, c_63])).
% 1.87/1.19  tff(c_16, plain, (![A_12, B_13]: (k3_tarski(k2_tarski(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.19  tff(c_84, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_78, c_16])).
% 1.87/1.19  tff(c_26, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.87/1.19  tff(c_101, plain, (r1_tarski(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_26])).
% 1.87/1.19  tff(c_152, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_154, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_101, c_152])).
% 1.87/1.19  tff(c_163, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_154])).
% 1.87/1.19  tff(c_102, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_78, c_16])).
% 1.87/1.19  tff(c_117, plain, (![A_27, B_26]: (r1_tarski(A_27, k2_xboole_0(B_26, A_27)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_10])).
% 1.87/1.19  tff(c_175, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163, c_117])).
% 1.87/1.19  tff(c_199, plain, (![A_35, C_36, B_37]: (r2_hidden(A_35, C_36) | ~r1_tarski(k2_tarski(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.19  tff(c_202, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_175, c_199])).
% 1.87/1.19  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_202])).
% 1.87/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  Inference rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Ref     : 0
% 1.87/1.19  #Sup     : 50
% 1.87/1.19  #Fact    : 0
% 1.87/1.19  #Define  : 0
% 1.87/1.19  #Split   : 0
% 1.87/1.19  #Chain   : 0
% 1.87/1.19  #Close   : 0
% 1.87/1.19  
% 1.87/1.19  Ordering : KBO
% 1.87/1.19  
% 1.87/1.19  Simplification rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Subsume      : 1
% 1.87/1.19  #Demod        : 13
% 1.87/1.19  #Tautology    : 32
% 1.87/1.19  #SimpNegUnit  : 1
% 1.87/1.19  #BackRed      : 2
% 1.87/1.19  
% 1.87/1.19  #Partial instantiations: 0
% 1.87/1.19  #Strategies tried      : 1
% 1.87/1.19  
% 1.87/1.19  Timing (in seconds)
% 1.87/1.19  ----------------------
% 1.87/1.19  Preprocessing        : 0.28
% 1.87/1.19  Parsing              : 0.15
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.14
% 1.87/1.20  Inferencing          : 0.05
% 1.87/1.20  Reduction            : 0.05
% 1.87/1.20  Demodulation         : 0.04
% 1.87/1.20  BG Simplification    : 0.01
% 1.87/1.20  Subsumption          : 0.03
% 1.87/1.20  Abstraction          : 0.01
% 1.87/1.20  MUC search           : 0.00
% 1.87/1.20  Cooper               : 0.00
% 1.87/1.20  Total                : 0.45
% 1.87/1.20  Index Insertion      : 0.00
% 1.87/1.20  Index Deletion       : 0.00
% 1.87/1.20  Index Matching       : 0.00
% 1.87/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
