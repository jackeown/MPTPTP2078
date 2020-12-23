%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:28 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [D_21,B_17] : r2_hidden(D_21,k2_tarski(D_21,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    k3_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_24,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_203,plain,(
    ! [A_67,B_68,C_69] : k3_xboole_0(k2_xboole_0(A_67,B_68),k2_xboole_0(A_67,C_69)) = k2_xboole_0(A_67,k3_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_232,plain,(
    ! [A_9,C_69] : k3_xboole_0(A_9,k2_xboole_0(A_9,C_69)) = k2_xboole_0(A_9,k3_xboole_0(A_9,C_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_203])).

tff(c_241,plain,(
    ! [A_70,C_71] : k2_xboole_0(A_70,k3_xboole_0(A_70,C_71)) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_232])).

tff(c_271,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_241])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_659,plain,(
    ! [D_89] :
      ( ~ r2_hidden(D_89,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_89,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_6])).

tff(c_667,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_659])).

tff(c_672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.33  
% 2.21/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.33  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.21/1.33  
% 2.21/1.33  %Foreground sorts:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Background operators:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Foreground operators:
% 2.21/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.21/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.21/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.33  
% 2.53/1.34  tff(f_64, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 2.53/1.34  tff(f_51, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.53/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.53/1.34  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.53/1.34  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.53/1.34  tff(f_42, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 2.53/1.34  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.53/1.34  tff(c_54, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.34  tff(c_32, plain, (![D_21, B_17]: (r2_hidden(D_21, k2_tarski(D_21, B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.34  tff(c_56, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.34  tff(c_134, plain, (k3_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 2.53/1.34  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.34  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.34  tff(c_203, plain, (![A_67, B_68, C_69]: (k3_xboole_0(k2_xboole_0(A_67, B_68), k2_xboole_0(A_67, C_69))=k2_xboole_0(A_67, k3_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.34  tff(c_232, plain, (![A_9, C_69]: (k3_xboole_0(A_9, k2_xboole_0(A_9, C_69))=k2_xboole_0(A_9, k3_xboole_0(A_9, C_69)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_203])).
% 2.53/1.34  tff(c_241, plain, (![A_70, C_71]: (k2_xboole_0(A_70, k3_xboole_0(A_70, C_71))=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_232])).
% 2.53/1.34  tff(c_271, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_134, c_241])).
% 2.53/1.34  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.53/1.34  tff(c_659, plain, (![D_89]: (~r2_hidden(D_89, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_89, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_271, c_6])).
% 2.53/1.34  tff(c_667, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_32, c_659])).
% 2.53/1.34  tff(c_672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_667])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 157
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 0
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 0
% 2.53/1.34  #Demod        : 54
% 2.53/1.34  #Tautology    : 109
% 2.53/1.34  #SimpNegUnit  : 1
% 2.53/1.34  #BackRed      : 0
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.34  Preprocessing        : 0.31
% 2.53/1.34  Parsing              : 0.16
% 2.53/1.34  CNF conversion       : 0.02
% 2.53/1.34  Main loop            : 0.25
% 2.53/1.34  Inferencing          : 0.08
% 2.53/1.34  Reduction            : 0.10
% 2.53/1.34  Demodulation         : 0.08
% 2.53/1.34  BG Simplification    : 0.02
% 2.53/1.34  Subsumption          : 0.04
% 2.53/1.34  Abstraction          : 0.02
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.58
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
