%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:21 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_18,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(k2_tarski(A_19,B_20),k1_tarski(B_20)) = k1_tarski(A_19)
      | B_20 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_141,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(k2_tarski(A_23,B_24),k1_tarski(A_23)) = k1_tarski(B_24)
      | B_24 = A_23 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_20,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_1')) = k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_147,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_tarski('#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_67])).

tff(c_180,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_147])).

tff(c_70,plain,(
    ! [A_14,C_15,B_16] :
      ( ~ r2_hidden(A_14,C_15)
      | k4_xboole_0(k2_tarski(A_14,B_16),C_15) != k1_tarski(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2418,plain,(
    ! [B_404,C_405,A_406] :
      ( ~ r2_hidden(B_404,C_405)
      | k4_xboole_0(k2_tarski(A_406,B_404),C_405) != k1_tarski(B_404) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_2437,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_2418])).

tff(c_2461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:09:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/2.00  
% 3.70/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/2.00  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.70/2.00  
% 3.70/2.00  %Foreground sorts:
% 3.70/2.00  
% 3.70/2.00  
% 3.70/2.00  %Background operators:
% 3.70/2.00  
% 3.70/2.00  
% 3.70/2.00  %Foreground operators:
% 3.70/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.70/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.70/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.70/2.00  tff('#skF_2', type, '#skF_2': $i).
% 3.70/2.00  tff('#skF_3', type, '#skF_3': $i).
% 3.70/2.00  tff('#skF_1', type, '#skF_1': $i).
% 3.70/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/2.00  
% 3.70/2.01  tff(f_52, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 3.70/2.01  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.70/2.01  tff(f_43, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 3.70/2.01  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.70/2.01  tff(f_38, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 3.70/2.01  tff(c_18, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.70/2.01  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.70/2.01  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.70/2.01  tff(c_103, plain, (![A_19, B_20]: (k4_xboole_0(k2_tarski(A_19, B_20), k1_tarski(B_20))=k1_tarski(A_19) | B_20=A_19)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.70/2.01  tff(c_141, plain, (![A_23, B_24]: (k4_xboole_0(k2_tarski(A_23, B_24), k1_tarski(A_23))=k1_tarski(B_24) | B_24=A_23)), inference(superposition, [status(thm), theory('equality')], [c_4, c_103])).
% 3.70/2.01  tff(c_20, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.70/2.01  tff(c_58, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/2.01  tff(c_67, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_1'))=k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_58])).
% 3.70/2.01  tff(c_147, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_tarski('#skF_2') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_141, c_67])).
% 3.70/2.01  tff(c_180, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_16, c_147])).
% 3.70/2.01  tff(c_70, plain, (![A_14, C_15, B_16]: (~r2_hidden(A_14, C_15) | k4_xboole_0(k2_tarski(A_14, B_16), C_15)!=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/2.01  tff(c_2418, plain, (![B_404, C_405, A_406]: (~r2_hidden(B_404, C_405) | k4_xboole_0(k2_tarski(A_406, B_404), C_405)!=k1_tarski(B_404))), inference(superposition, [status(thm), theory('equality')], [c_4, c_70])).
% 3.70/2.01  tff(c_2437, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_180, c_2418])).
% 3.70/2.01  tff(c_2461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2437])).
% 3.70/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/2.01  
% 3.70/2.01  Inference rules
% 3.70/2.01  ----------------------
% 3.70/2.01  #Ref     : 1
% 3.70/2.01  #Sup     : 334
% 3.70/2.01  #Fact    : 0
% 3.70/2.02  #Define  : 0
% 3.70/2.02  #Split   : 7
% 3.70/2.02  #Chain   : 0
% 3.70/2.02  #Close   : 0
% 3.70/2.02  
% 3.70/2.02  Ordering : KBO
% 3.70/2.02  
% 3.70/2.02  Simplification rules
% 3.70/2.02  ----------------------
% 3.70/2.02  #Subsume      : 79
% 3.70/2.02  #Demod        : 59
% 3.70/2.02  #Tautology    : 68
% 3.70/2.02  #SimpNegUnit  : 11
% 3.70/2.02  #BackRed      : 2
% 3.70/2.02  
% 3.70/2.02  #Partial instantiations: 364
% 3.70/2.02  #Strategies tried      : 1
% 3.70/2.02  
% 3.70/2.02  Timing (in seconds)
% 3.70/2.02  ----------------------
% 3.70/2.02  Preprocessing        : 0.44
% 3.70/2.02  Parsing              : 0.22
% 3.70/2.02  CNF conversion       : 0.03
% 3.70/2.02  Main loop            : 0.68
% 3.70/2.02  Inferencing          : 0.27
% 3.70/2.02  Reduction            : 0.20
% 3.70/2.02  Demodulation         : 0.15
% 3.70/2.02  BG Simplification    : 0.04
% 3.70/2.02  Subsumption          : 0.13
% 3.70/2.02  Abstraction          : 0.03
% 3.70/2.02  MUC search           : 0.00
% 3.70/2.02  Cooper               : 0.00
% 3.70/2.02  Total                : 1.16
% 3.70/2.02  Index Insertion      : 0.00
% 3.70/2.02  Index Deletion       : 0.00
% 3.70/2.02  Index Matching       : 0.00
% 3.70/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
