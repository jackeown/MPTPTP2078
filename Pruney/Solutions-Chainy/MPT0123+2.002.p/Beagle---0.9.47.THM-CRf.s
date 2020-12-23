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
% DateTime   : Thu Dec  3 09:45:35 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  25 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [A_27,B_28] : k3_xboole_0(k3_xboole_0(A_27,B_28),A_27) = k3_xboole_0(A_27,B_28) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_208,plain,(
    ! [A_27,B_28] : k3_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_2])).

tff(c_72,plain,(
    ! [A_18,B_19,C_20] : k3_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k3_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [B_2,A_18,B_19] : k3_xboole_0(B_2,k3_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,k3_xboole_0(B_19,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k3_xboole_0(k3_xboole_0(A_3,B_4),C_5) = k3_xboole_0(A_3,k3_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_12,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11])).

tff(c_1605,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_12])).

tff(c_1608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_1605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.55  
% 3.22/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.55  %$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.22/1.55  
% 3.22/1.55  %Foreground sorts:
% 3.22/1.55  
% 3.22/1.55  
% 3.22/1.55  %Background operators:
% 3.22/1.55  
% 3.22/1.55  
% 3.22/1.55  %Foreground operators:
% 3.22/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.55  
% 3.22/1.56  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.22/1.56  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.22/1.56  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.22/1.56  tff(f_38, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_xboole_1)).
% 3.22/1.56  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.56  tff(c_63, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.56  tff(c_176, plain, (![A_27, B_28]: (k3_xboole_0(k3_xboole_0(A_27, B_28), A_27)=k3_xboole_0(A_27, B_28))), inference(resolution, [status(thm)], [c_6, c_63])).
% 3.22/1.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.56  tff(c_208, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(superposition, [status(thm), theory('equality')], [c_176, c_2])).
% 3.22/1.56  tff(c_72, plain, (![A_18, B_19, C_20]: (k3_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k3_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.56  tff(c_103, plain, (![B_2, A_18, B_19]: (k3_xboole_0(B_2, k3_xboole_0(A_18, B_19))=k3_xboole_0(A_18, k3_xboole_0(B_19, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 3.22/1.56  tff(c_4, plain, (![A_3, B_4, C_5]: (k3_xboole_0(k3_xboole_0(A_3, B_4), C_5)=k3_xboole_0(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.56  tff(c_10, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.56  tff(c_11, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3')))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 3.35/1.56  tff(c_12, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3')))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11])).
% 3.35/1.56  tff(c_1605, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_12])).
% 3.35/1.56  tff(c_1608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_1605])).
% 3.35/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.56  
% 3.35/1.56  Inference rules
% 3.35/1.56  ----------------------
% 3.35/1.56  #Ref     : 0
% 3.35/1.56  #Sup     : 390
% 3.35/1.56  #Fact    : 0
% 3.35/1.56  #Define  : 0
% 3.35/1.56  #Split   : 0
% 3.35/1.56  #Chain   : 0
% 3.35/1.56  #Close   : 0
% 3.35/1.56  
% 3.35/1.56  Ordering : KBO
% 3.35/1.56  
% 3.35/1.56  Simplification rules
% 3.35/1.56  ----------------------
% 3.35/1.56  #Subsume      : 22
% 3.35/1.56  #Demod        : 443
% 3.35/1.56  #Tautology    : 206
% 3.35/1.56  #SimpNegUnit  : 0
% 3.35/1.56  #BackRed      : 1
% 3.35/1.56  
% 3.35/1.56  #Partial instantiations: 0
% 3.35/1.56  #Strategies tried      : 1
% 3.35/1.56  
% 3.35/1.56  Timing (in seconds)
% 3.35/1.56  ----------------------
% 3.35/1.57  Preprocessing        : 0.27
% 3.35/1.57  Parsing              : 0.15
% 3.35/1.57  CNF conversion       : 0.02
% 3.35/1.57  Main loop            : 0.47
% 3.35/1.57  Inferencing          : 0.12
% 3.35/1.57  Reduction            : 0.25
% 3.35/1.57  Demodulation         : 0.22
% 3.35/1.57  BG Simplification    : 0.02
% 3.35/1.57  Subsumption          : 0.06
% 3.35/1.57  Abstraction          : 0.02
% 3.35/1.57  MUC search           : 0.00
% 3.35/1.57  Cooper               : 0.00
% 3.35/1.57  Total                : 0.77
% 3.35/1.57  Index Insertion      : 0.00
% 3.35/1.57  Index Deletion       : 0.00
% 3.35/1.57  Index Matching       : 0.00
% 3.35/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
