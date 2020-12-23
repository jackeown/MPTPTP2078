%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:37 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  37 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_26,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_149,plain,(
    ! [B_35,A_36] :
      ( B_35 = A_36
      | ~ r1_tarski(B_35,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_167,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_157])).

tff(c_42,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_57,plain,(
    ! [A_23,B_22] : r1_tarski(A_23,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_210,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_57])).

tff(c_14,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [B_37,C_38,A_39] :
      ( r2_hidden(B_37,C_38)
      | ~ r1_tarski(k2_tarski(A_39,B_37),C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_233,plain,(
    ! [A_44,C_45] :
      ( r2_hidden(A_44,C_45)
      | ~ r1_tarski(k1_tarski(A_44),C_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_173])).

tff(c_236,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_210,c_233])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.30  
% 1.89/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.30  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.89/1.30  
% 1.89/1.30  %Foreground sorts:
% 1.89/1.30  
% 1.89/1.30  
% 1.89/1.30  %Background operators:
% 1.89/1.30  
% 1.89/1.30  
% 1.89/1.30  %Foreground operators:
% 1.89/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.30  
% 1.89/1.31  tff(f_56, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.89/1.31  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.89/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.89/1.31  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.89/1.31  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/1.31  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.89/1.31  tff(c_26, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.31  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.31  tff(c_28, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.31  tff(c_30, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 1.89/1.31  tff(c_149, plain, (![B_35, A_36]: (B_35=A_36 | ~r1_tarski(B_35, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.31  tff(c_157, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_149])).
% 1.89/1.31  tff(c_167, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_157])).
% 1.89/1.31  tff(c_42, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.31  tff(c_57, plain, (![A_23, B_22]: (r1_tarski(A_23, k2_xboole_0(B_22, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_12])).
% 1.89/1.31  tff(c_210, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_167, c_57])).
% 1.89/1.31  tff(c_14, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.31  tff(c_173, plain, (![B_37, C_38, A_39]: (r2_hidden(B_37, C_38) | ~r1_tarski(k2_tarski(A_39, B_37), C_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.31  tff(c_233, plain, (![A_44, C_45]: (r2_hidden(A_44, C_45) | ~r1_tarski(k1_tarski(A_44), C_45))), inference(superposition, [status(thm), theory('equality')], [c_14, c_173])).
% 1.89/1.31  tff(c_236, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_210, c_233])).
% 1.89/1.31  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_236])).
% 1.89/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.31  
% 1.89/1.31  Inference rules
% 1.89/1.31  ----------------------
% 1.89/1.31  #Ref     : 0
% 1.89/1.31  #Sup     : 55
% 1.89/1.31  #Fact    : 0
% 1.89/1.31  #Define  : 0
% 1.89/1.31  #Split   : 0
% 1.89/1.31  #Chain   : 0
% 1.89/1.31  #Close   : 0
% 1.89/1.31  
% 1.89/1.31  Ordering : KBO
% 1.89/1.31  
% 1.89/1.31  Simplification rules
% 1.89/1.31  ----------------------
% 1.89/1.31  #Subsume      : 2
% 1.89/1.31  #Demod        : 13
% 1.89/1.31  #Tautology    : 28
% 1.89/1.31  #SimpNegUnit  : 1
% 1.89/1.31  #BackRed      : 1
% 1.89/1.31  
% 1.89/1.31  #Partial instantiations: 0
% 1.89/1.31  #Strategies tried      : 1
% 1.89/1.31  
% 1.89/1.31  Timing (in seconds)
% 1.89/1.31  ----------------------
% 1.89/1.31  Preprocessing        : 0.32
% 1.89/1.31  Parsing              : 0.16
% 1.89/1.31  CNF conversion       : 0.02
% 1.89/1.31  Main loop            : 0.17
% 1.89/1.31  Inferencing          : 0.06
% 1.89/1.31  Reduction            : 0.06
% 1.89/1.31  Demodulation         : 0.05
% 1.89/1.31  BG Simplification    : 0.01
% 1.89/1.31  Subsumption          : 0.03
% 1.89/1.31  Abstraction          : 0.01
% 1.89/1.31  MUC search           : 0.00
% 1.89/1.31  Cooper               : 0.00
% 1.89/1.31  Total                : 0.51
% 1.89/1.31  Index Insertion      : 0.00
% 1.89/1.31  Index Deletion       : 0.00
% 1.89/1.31  Index Matching       : 0.00
% 1.89/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
