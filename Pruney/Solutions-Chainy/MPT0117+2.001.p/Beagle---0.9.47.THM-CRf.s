%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:29 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   43 (  72 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  82 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

tff(c_116,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_120,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_116,c_26])).

tff(c_20,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_220,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_234,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_220])).

tff(c_442,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k4_xboole_0(B_46,A_45)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_466,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_442])).

tff(c_473,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_466])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_236,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_220])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_235,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_220])).

tff(c_460,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_442])).

tff(c_471,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20,c_460])).

tff(c_463,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_442])).

tff(c_472,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20,c_463])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k4_xboole_0(A_19,k2_xboole_0(B_20,C_21)),k4_xboole_0(B_20,k2_xboole_0(A_19,C_21))) = k4_xboole_0(k5_xboole_0(A_19,B_20),C_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1421,plain,(
    ! [A_68] : k2_xboole_0(k4_xboole_0(A_68,'#skF_2'),k4_xboole_0('#skF_3',k2_xboole_0(A_68,'#skF_2'))) = k4_xboole_0(k5_xboole_0(A_68,'#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_24])).

tff(c_1472,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_1421])).

tff(c_1504,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_236,c_2,c_235,c_1472])).

tff(c_1506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.77  
% 2.95/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.77  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.95/1.77  
% 2.95/1.77  %Foreground sorts:
% 2.95/1.77  
% 2.95/1.77  
% 2.95/1.77  %Background operators:
% 2.95/1.77  
% 2.95/1.77  
% 2.95/1.77  %Foreground operators:
% 2.95/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.95/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.77  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.77  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.77  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.95/1.77  
% 2.95/1.78  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.95/1.78  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.95/1.78  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.95/1.78  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.95/1.78  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.95/1.78  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.95/1.78  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_xboole_1)).
% 2.95/1.78  tff(c_116, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | k4_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.78  tff(c_26, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.95/1.78  tff(c_120, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_116, c_26])).
% 2.95/1.78  tff(c_20, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.95/1.78  tff(c_16, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.78  tff(c_220, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.78  tff(c_234, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_220])).
% 2.95/1.78  tff(c_442, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k4_xboole_0(B_46, A_45))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.95/1.78  tff(c_466, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_442])).
% 2.95/1.78  tff(c_473, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_466])).
% 2.95/1.78  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.95/1.78  tff(c_236, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_220])).
% 2.95/1.78  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.95/1.78  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.95/1.78  tff(c_235, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_220])).
% 2.95/1.78  tff(c_460, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_236, c_442])).
% 2.95/1.78  tff(c_471, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20, c_460])).
% 2.95/1.78  tff(c_463, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_235, c_442])).
% 2.95/1.78  tff(c_472, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20, c_463])).
% 2.95/1.78  tff(c_24, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k4_xboole_0(A_19, k2_xboole_0(B_20, C_21)), k4_xboole_0(B_20, k2_xboole_0(A_19, C_21)))=k4_xboole_0(k5_xboole_0(A_19, B_20), C_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.95/1.78  tff(c_1421, plain, (![A_68]: (k2_xboole_0(k4_xboole_0(A_68, '#skF_2'), k4_xboole_0('#skF_3', k2_xboole_0(A_68, '#skF_2')))=k4_xboole_0(k5_xboole_0(A_68, '#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_472, c_24])).
% 2.95/1.78  tff(c_1472, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_471, c_1421])).
% 2.95/1.78  tff(c_1504, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_473, c_236, c_2, c_235, c_1472])).
% 2.95/1.78  tff(c_1506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_1504])).
% 2.95/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.78  
% 2.95/1.78  Inference rules
% 2.95/1.78  ----------------------
% 2.95/1.78  #Ref     : 0
% 2.95/1.78  #Sup     : 382
% 2.95/1.78  #Fact    : 0
% 2.95/1.78  #Define  : 0
% 2.95/1.78  #Split   : 0
% 2.95/1.78  #Chain   : 0
% 2.95/1.78  #Close   : 0
% 2.95/1.78  
% 2.95/1.78  Ordering : KBO
% 2.95/1.78  
% 2.95/1.78  Simplification rules
% 2.95/1.78  ----------------------
% 2.95/1.78  #Subsume      : 0
% 2.95/1.78  #Demod        : 305
% 2.95/1.78  #Tautology    : 248
% 2.95/1.78  #SimpNegUnit  : 1
% 2.95/1.78  #BackRed      : 1
% 2.95/1.78  
% 2.95/1.78  #Partial instantiations: 0
% 2.95/1.78  #Strategies tried      : 1
% 2.95/1.78  
% 2.95/1.78  Timing (in seconds)
% 2.95/1.78  ----------------------
% 2.95/1.78  Preprocessing        : 0.37
% 2.95/1.78  Parsing              : 0.21
% 2.95/1.78  CNF conversion       : 0.02
% 2.95/1.78  Main loop            : 0.48
% 2.95/1.78  Inferencing          : 0.16
% 2.95/1.78  Reduction            : 0.20
% 2.95/1.78  Demodulation         : 0.16
% 2.95/1.78  BG Simplification    : 0.02
% 2.95/1.78  Subsumption          : 0.07
% 2.95/1.78  Abstraction          : 0.02
% 2.95/1.78  MUC search           : 0.00
% 2.95/1.78  Cooper               : 0.00
% 2.95/1.78  Total                : 0.87
% 2.95/1.78  Index Insertion      : 0.00
% 2.95/1.78  Index Deletion       : 0.00
% 2.95/1.78  Index Matching       : 0.00
% 2.95/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
