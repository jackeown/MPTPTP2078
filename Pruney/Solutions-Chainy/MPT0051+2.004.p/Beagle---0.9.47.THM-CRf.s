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
% DateTime   : Thu Dec  3 09:42:49 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   31 (  44 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  39 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k4_xboole_0(A,B),C)
       => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_149,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_xboole_0(A_22,B_23),C_24) = k2_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [C_24,A_22,B_23] : k2_xboole_0(C_24,k2_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_65])).

tff(c_937,plain,(
    ! [C_49,A_50,B_51] : k2_xboole_0(C_49,k2_xboole_0(A_50,B_51)) = k2_xboole_0(A_50,k2_xboole_0(B_51,C_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2])).

tff(c_4119,plain,(
    ! [A_76] : k2_xboole_0('#skF_3',k2_xboole_0(A_76,k4_xboole_0('#skF_1','#skF_2'))) = k2_xboole_0(A_76,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_937])).

tff(c_4278,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_1')) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4119])).

tff(c_4332,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_168,c_2,c_2,c_4278])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4412,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4332,c_10])).

tff(c_4434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_4412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.20  
% 5.32/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.20  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 5.32/2.20  
% 5.32/2.20  %Foreground sorts:
% 5.32/2.20  
% 5.32/2.20  
% 5.32/2.20  %Background operators:
% 5.32/2.20  
% 5.32/2.20  
% 5.32/2.20  %Foreground operators:
% 5.32/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.32/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.32/2.20  tff('#skF_3', type, '#skF_3': $i).
% 5.32/2.20  tff('#skF_1', type, '#skF_1': $i).
% 5.32/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.32/2.20  
% 5.32/2.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.32/2.21  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.32/2.21  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 5.32/2.21  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.32/2.21  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.32/2.21  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.32/2.21  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.32/2.21  tff(c_12, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.32/2.21  tff(c_15, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 5.32/2.21  tff(c_149, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k2_xboole_0(A_22, B_23), C_24)=k2_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.32/2.21  tff(c_168, plain, (![C_24, A_22, B_23]: (k2_xboole_0(C_24, k2_xboole_0(A_22, B_23))=k2_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_2])).
% 5.32/2.21  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.32/2.21  tff(c_14, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.32/2.21  tff(c_65, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.21  tff(c_77, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_14, c_65])).
% 5.32/2.21  tff(c_937, plain, (![C_49, A_50, B_51]: (k2_xboole_0(C_49, k2_xboole_0(A_50, B_51))=k2_xboole_0(A_50, k2_xboole_0(B_51, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_2])).
% 5.32/2.21  tff(c_4119, plain, (![A_76]: (k2_xboole_0('#skF_3', k2_xboole_0(A_76, k4_xboole_0('#skF_1', '#skF_2')))=k2_xboole_0(A_76, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_937])).
% 5.32/2.21  tff(c_4278, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_1'))=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_4119])).
% 5.32/2.21  tff(c_4332, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_168, c_2, c_2, c_4278])).
% 5.32/2.21  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.32/2.21  tff(c_4412, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4332, c_10])).
% 5.32/2.21  tff(c_4434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15, c_4412])).
% 5.32/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.21  
% 5.32/2.21  Inference rules
% 5.32/2.21  ----------------------
% 5.32/2.21  #Ref     : 0
% 5.32/2.21  #Sup     : 1102
% 5.32/2.21  #Fact    : 0
% 5.32/2.21  #Define  : 0
% 5.32/2.21  #Split   : 0
% 5.32/2.21  #Chain   : 0
% 5.32/2.21  #Close   : 0
% 5.32/2.21  
% 5.32/2.21  Ordering : KBO
% 5.32/2.21  
% 5.32/2.21  Simplification rules
% 5.32/2.21  ----------------------
% 5.32/2.21  #Subsume      : 80
% 5.32/2.21  #Demod        : 1255
% 5.32/2.21  #Tautology    : 564
% 5.32/2.21  #SimpNegUnit  : 1
% 5.32/2.21  #BackRed      : 0
% 5.32/2.21  
% 5.32/2.21  #Partial instantiations: 0
% 5.32/2.21  #Strategies tried      : 1
% 5.32/2.21  
% 5.32/2.21  Timing (in seconds)
% 5.32/2.21  ----------------------
% 5.32/2.21  Preprocessing        : 0.31
% 5.32/2.21  Parsing              : 0.17
% 5.32/2.21  CNF conversion       : 0.02
% 5.32/2.21  Main loop            : 1.06
% 5.32/2.21  Inferencing          : 0.24
% 5.32/2.21  Reduction            : 0.60
% 5.32/2.21  Demodulation         : 0.53
% 5.32/2.21  BG Simplification    : 0.03
% 5.32/2.21  Subsumption          : 0.14
% 5.32/2.21  Abstraction          : 0.05
% 5.32/2.21  MUC search           : 0.00
% 5.32/2.21  Cooper               : 0.00
% 5.32/2.21  Total                : 1.39
% 5.32/2.21  Index Insertion      : 0.00
% 5.32/2.21  Index Deletion       : 0.00
% 5.32/2.21  Index Matching       : 0.00
% 5.32/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
