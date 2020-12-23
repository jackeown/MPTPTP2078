%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:53 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_12,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k1_tarski(A_6)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_13,C_14,B_15] : k2_xboole_0(k4_xboole_0(A_13,C_14),k4_xboole_0(B_15,C_14)) = k4_xboole_0(k2_xboole_0(A_13,B_15),C_14) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_325,plain,(
    ! [A_26,A_27,B_28] :
      ( k4_xboole_0(k2_xboole_0(A_26,k1_tarski(A_27)),k1_tarski(B_28)) = k2_xboole_0(k4_xboole_0(A_26,k1_tarski(B_28)),k1_tarski(A_27))
      | B_28 = A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_10,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_3',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_349,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) != k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_3',k1_tarski('#skF_2')))
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_13])).

tff(c_377,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_349])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.41  
% 2.31/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.41  %$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.31/1.41  
% 2.31/1.41  %Foreground sorts:
% 2.31/1.41  
% 2.31/1.41  
% 2.31/1.41  %Background operators:
% 2.31/1.41  
% 2.31/1.41  
% 2.31/1.41  %Foreground operators:
% 2.31/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.41  
% 2.31/1.42  tff(f_40, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 2.31/1.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.31/1.42  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.31/1.42  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.31/1.42  tff(c_12, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.42  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.42  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k1_tarski(A_6) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.31/1.42  tff(c_64, plain, (![A_13, C_14, B_15]: (k2_xboole_0(k4_xboole_0(A_13, C_14), k4_xboole_0(B_15, C_14))=k4_xboole_0(k2_xboole_0(A_13, B_15), C_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.42  tff(c_325, plain, (![A_26, A_27, B_28]: (k4_xboole_0(k2_xboole_0(A_26, k1_tarski(A_27)), k1_tarski(B_28))=k2_xboole_0(k4_xboole_0(A_26, k1_tarski(B_28)), k1_tarski(A_27)) | B_28=A_27)), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 2.31/1.42  tff(c_10, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.42  tff(c_13, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_3', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 2.31/1.42  tff(c_349, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))!=k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_3', k1_tarski('#skF_2'))) | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_325, c_13])).
% 2.31/1.42  tff(c_377, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_349])).
% 2.31/1.42  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_377])).
% 2.31/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.42  
% 2.31/1.42  Inference rules
% 2.31/1.42  ----------------------
% 2.31/1.42  #Ref     : 0
% 2.31/1.42  #Sup     : 96
% 2.31/1.42  #Fact    : 0
% 2.31/1.42  #Define  : 0
% 2.31/1.42  #Split   : 0
% 2.31/1.42  #Chain   : 0
% 2.31/1.42  #Close   : 0
% 2.31/1.42  
% 2.31/1.42  Ordering : KBO
% 2.31/1.42  
% 2.31/1.42  Simplification rules
% 2.31/1.42  ----------------------
% 2.31/1.42  #Subsume      : 2
% 2.31/1.42  #Demod        : 17
% 2.31/1.42  #Tautology    : 55
% 2.31/1.42  #SimpNegUnit  : 1
% 2.31/1.42  #BackRed      : 0
% 2.31/1.42  
% 2.31/1.42  #Partial instantiations: 0
% 2.31/1.42  #Strategies tried      : 1
% 2.31/1.42  
% 2.31/1.42  Timing (in seconds)
% 2.31/1.42  ----------------------
% 2.31/1.42  Preprocessing        : 0.34
% 2.31/1.42  Parsing              : 0.19
% 2.31/1.42  CNF conversion       : 0.02
% 2.31/1.42  Main loop            : 0.28
% 2.31/1.42  Inferencing          : 0.10
% 2.31/1.42  Reduction            : 0.11
% 2.31/1.42  Demodulation         : 0.10
% 2.31/1.42  BG Simplification    : 0.02
% 2.31/1.42  Subsumption          : 0.03
% 2.31/1.42  Abstraction          : 0.02
% 2.31/1.42  MUC search           : 0.00
% 2.31/1.42  Cooper               : 0.00
% 2.31/1.42  Total                : 0.64
% 2.31/1.42  Index Insertion      : 0.00
% 2.31/1.42  Index Deletion       : 0.00
% 2.31/1.42  Index Matching       : 0.00
% 2.31/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
