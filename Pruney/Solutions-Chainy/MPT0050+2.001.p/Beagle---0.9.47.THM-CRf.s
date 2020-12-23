%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:48 EST 2020

% Result     : Theorem 11.97s
% Output     : CNFRefutation 11.97s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  35 expanded)
%              Number of equality atoms :   13 (  15 expanded)
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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k2_xboole_0(B,C))
       => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_16,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_72,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_19,c_61])).

tff(c_657,plain,(
    ! [A_59,C_60,B_61] : k2_xboole_0(k4_xboole_0(A_59,C_60),k4_xboole_0(B_61,C_60)) = k4_xboole_0(k2_xboole_0(A_59,B_61),C_60) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_xboole_0(A_12,B_13),C_14) = k2_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10254,plain,(
    ! [A_205,C_206,B_207,C_208] : k2_xboole_0(k4_xboole_0(A_205,C_206),k2_xboole_0(k4_xboole_0(B_207,C_206),C_208)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(A_205,B_207),C_206),C_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_12])).

tff(c_14,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25220,plain,(
    ! [A_320,C_321,B_322,C_323] : r1_tarski(k4_xboole_0(A_320,C_321),k2_xboole_0(k4_xboole_0(k2_xboole_0(A_320,B_322),C_321),C_323)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10254,c_14])).

tff(c_25921,plain,(
    ! [C_325,C_326] : r1_tarski(k4_xboole_0('#skF_1',C_325),k2_xboole_0(k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_325),C_326)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_25220])).

tff(c_26783,plain,(
    ! [C_330] : r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k2_xboole_0(k4_xboole_0('#skF_3','#skF_2'),C_330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_25921])).

tff(c_26874,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_26783])).

tff(c_26894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_26874])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.97/5.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/5.35  
% 11.97/5.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/5.35  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 11.97/5.35  
% 11.97/5.35  %Foreground sorts:
% 11.97/5.35  
% 11.97/5.35  
% 11.97/5.35  %Background operators:
% 11.97/5.35  
% 11.97/5.35  
% 11.97/5.35  %Foreground operators:
% 11.97/5.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.97/5.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.97/5.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.97/5.35  tff('#skF_2', type, '#skF_2': $i).
% 11.97/5.35  tff('#skF_3', type, '#skF_3': $i).
% 11.97/5.35  tff('#skF_1', type, '#skF_1': $i).
% 11.97/5.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.97/5.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.97/5.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.97/5.35  
% 11.97/5.36  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.97/5.36  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.97/5.36  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.97/5.36  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 11.97/5.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.97/5.36  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 11.97/5.36  tff(f_39, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 11.97/5.36  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.97/5.36  tff(c_16, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.97/5.36  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.97/5.36  tff(c_61, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.97/5.36  tff(c_71, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_61])).
% 11.97/5.36  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.97/5.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.97/5.36  tff(c_18, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.97/5.36  tff(c_19, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 11.97/5.36  tff(c_72, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_19, c_61])).
% 11.97/5.36  tff(c_657, plain, (![A_59, C_60, B_61]: (k2_xboole_0(k4_xboole_0(A_59, C_60), k4_xboole_0(B_61, C_60))=k4_xboole_0(k2_xboole_0(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.97/5.36  tff(c_12, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k2_xboole_0(A_12, B_13), C_14)=k2_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.97/5.36  tff(c_10254, plain, (![A_205, C_206, B_207, C_208]: (k2_xboole_0(k4_xboole_0(A_205, C_206), k2_xboole_0(k4_xboole_0(B_207, C_206), C_208))=k2_xboole_0(k4_xboole_0(k2_xboole_0(A_205, B_207), C_206), C_208))), inference(superposition, [status(thm), theory('equality')], [c_657, c_12])).
% 11.97/5.36  tff(c_14, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.97/5.36  tff(c_25220, plain, (![A_320, C_321, B_322, C_323]: (r1_tarski(k4_xboole_0(A_320, C_321), k2_xboole_0(k4_xboole_0(k2_xboole_0(A_320, B_322), C_321), C_323)))), inference(superposition, [status(thm), theory('equality')], [c_10254, c_14])).
% 11.97/5.36  tff(c_25921, plain, (![C_325, C_326]: (r1_tarski(k4_xboole_0('#skF_1', C_325), k2_xboole_0(k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_325), C_326)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_25220])).
% 11.97/5.36  tff(c_26783, plain, (![C_330]: (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k2_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), C_330)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_25921])).
% 11.97/5.36  tff(c_26874, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_71, c_26783])).
% 11.97/5.36  tff(c_26894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_26874])).
% 11.97/5.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/5.36  
% 11.97/5.36  Inference rules
% 11.97/5.36  ----------------------
% 11.97/5.36  #Ref     : 0
% 11.97/5.36  #Sup     : 6597
% 11.97/5.36  #Fact    : 0
% 11.97/5.36  #Define  : 0
% 11.97/5.36  #Split   : 0
% 11.97/5.36  #Chain   : 0
% 11.97/5.36  #Close   : 0
% 11.97/5.36  
% 11.97/5.36  Ordering : KBO
% 11.97/5.36  
% 11.97/5.36  Simplification rules
% 11.97/5.36  ----------------------
% 11.97/5.36  #Subsume      : 146
% 11.97/5.36  #Demod        : 6774
% 11.97/5.36  #Tautology    : 3147
% 11.97/5.36  #SimpNegUnit  : 1
% 11.97/5.36  #BackRed      : 0
% 11.97/5.36  
% 11.97/5.36  #Partial instantiations: 0
% 11.97/5.36  #Strategies tried      : 1
% 11.97/5.36  
% 11.97/5.36  Timing (in seconds)
% 11.97/5.36  ----------------------
% 11.97/5.37  Preprocessing        : 0.25
% 11.97/5.37  Parsing              : 0.14
% 11.97/5.37  CNF conversion       : 0.02
% 11.97/5.37  Main loop            : 4.36
% 11.97/5.37  Inferencing          : 0.61
% 11.97/5.37  Reduction            : 2.79
% 11.97/5.37  Demodulation         : 2.60
% 11.97/5.37  BG Simplification    : 0.09
% 11.97/5.37  Subsumption          : 0.67
% 11.97/5.37  Abstraction          : 0.13
% 11.97/5.37  MUC search           : 0.00
% 11.97/5.37  Cooper               : 0.00
% 11.97/5.37  Total                : 4.63
% 11.97/5.37  Index Insertion      : 0.00
% 11.97/5.37  Index Deletion       : 0.00
% 11.97/5.37  Index Matching       : 0.00
% 11.97/5.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
