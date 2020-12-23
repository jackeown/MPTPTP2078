%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:18 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  68 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_23,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_763,plain,(
    ! [A_75,B_76] : k3_xboole_0(k4_xboole_0(A_75,B_76),A_75) = k4_xboole_0(A_75,B_76) ),
    inference(resolution,[status(thm)],[c_10,c_57])).

tff(c_246,plain,(
    ! [A_45,B_46,C_47] : k3_xboole_0(k3_xboole_0(A_45,B_46),C_47) = k3_xboole_0(A_45,k3_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_285,plain,(
    ! [C_47] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_47)) = k3_xboole_0('#skF_1',C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_246])).

tff(c_789,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_285])).

tff(c_858,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_789])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [A_31,B_32] : r1_tarski(k3_xboole_0(A_31,B_32),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_10])).

tff(c_118,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_894,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_118])).

tff(c_908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23,c_894])).

tff(c_909,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_16,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1107,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_xboole_0(A_89,C_90)
      | ~ r1_xboole_0(B_91,C_90)
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1850,plain,(
    ! [A_125,B_126,A_127] :
      ( r1_xboole_0(A_125,B_126)
      | ~ r1_tarski(A_125,k4_xboole_0(A_127,B_126)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1107])).

tff(c_1888,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1850])).

tff(c_1901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_909,c_1888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.80  
% 3.77/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.80  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.77/1.80  
% 3.77/1.80  %Foreground sorts:
% 3.77/1.80  
% 3.77/1.80  
% 3.77/1.80  %Background operators:
% 3.77/1.80  
% 3.77/1.80  
% 3.77/1.80  %Foreground operators:
% 3.77/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.77/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.77/1.80  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.80  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.80  tff('#skF_1', type, '#skF_1': $i).
% 3.77/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.77/1.80  
% 3.92/1.82  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.92/1.82  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.92/1.82  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.92/1.82  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.92/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.92/1.82  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.92/1.82  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.92/1.82  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.92/1.82  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.92/1.82  tff(c_23, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 3.92/1.82  tff(c_20, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.92/1.82  tff(c_57, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.92/1.82  tff(c_65, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_20, c_57])).
% 3.92/1.82  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.92/1.82  tff(c_763, plain, (![A_75, B_76]: (k3_xboole_0(k4_xboole_0(A_75, B_76), A_75)=k4_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_10, c_57])).
% 3.92/1.82  tff(c_246, plain, (![A_45, B_46, C_47]: (k3_xboole_0(k3_xboole_0(A_45, B_46), C_47)=k3_xboole_0(A_45, k3_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.92/1.82  tff(c_285, plain, (![C_47]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_47))=k3_xboole_0('#skF_1', C_47))), inference(superposition, [status(thm), theory('equality')], [c_65, c_246])).
% 3.92/1.82  tff(c_789, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_763, c_285])).
% 3.92/1.82  tff(c_858, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_789])).
% 3.92/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.92/1.82  tff(c_70, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.92/1.82  tff(c_109, plain, (![A_31, B_32]: (r1_tarski(k3_xboole_0(A_31, B_32), A_31))), inference(superposition, [status(thm), theory('equality')], [c_70, c_10])).
% 3.92/1.82  tff(c_118, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_109])).
% 3.92/1.82  tff(c_894, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_858, c_118])).
% 3.92/1.82  tff(c_908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23, c_894])).
% 3.92/1.82  tff(c_909, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 3.92/1.82  tff(c_16, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.92/1.82  tff(c_1107, plain, (![A_89, C_90, B_91]: (r1_xboole_0(A_89, C_90) | ~r1_xboole_0(B_91, C_90) | ~r1_tarski(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.92/1.82  tff(c_1850, plain, (![A_125, B_126, A_127]: (r1_xboole_0(A_125, B_126) | ~r1_tarski(A_125, k4_xboole_0(A_127, B_126)))), inference(resolution, [status(thm)], [c_16, c_1107])).
% 3.92/1.82  tff(c_1888, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_1850])).
% 3.92/1.82  tff(c_1901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_909, c_1888])).
% 3.92/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.82  
% 3.92/1.82  Inference rules
% 3.92/1.82  ----------------------
% 3.92/1.82  #Ref     : 0
% 3.92/1.82  #Sup     : 495
% 3.92/1.82  #Fact    : 0
% 3.92/1.82  #Define  : 0
% 3.92/1.82  #Split   : 1
% 3.92/1.82  #Chain   : 0
% 3.92/1.82  #Close   : 0
% 3.92/1.82  
% 3.92/1.82  Ordering : KBO
% 3.92/1.82  
% 3.92/1.82  Simplification rules
% 3.92/1.82  ----------------------
% 3.92/1.82  #Subsume      : 0
% 3.92/1.82  #Demod        : 255
% 3.92/1.82  #Tautology    : 244
% 3.92/1.82  #SimpNegUnit  : 2
% 3.92/1.82  #BackRed      : 3
% 3.92/1.82  
% 3.92/1.82  #Partial instantiations: 0
% 3.92/1.82  #Strategies tried      : 1
% 3.92/1.82  
% 3.92/1.82  Timing (in seconds)
% 3.92/1.82  ----------------------
% 3.92/1.82  Preprocessing        : 0.33
% 3.92/1.82  Parsing              : 0.19
% 3.92/1.82  CNF conversion       : 0.02
% 3.92/1.82  Main loop            : 0.66
% 3.92/1.82  Inferencing          : 0.22
% 3.92/1.82  Reduction            : 0.26
% 3.92/1.82  Demodulation         : 0.22
% 3.92/1.82  BG Simplification    : 0.03
% 3.92/1.82  Subsumption          : 0.10
% 3.92/1.82  Abstraction          : 0.03
% 3.92/1.82  MUC search           : 0.00
% 3.92/1.82  Cooper               : 0.00
% 3.92/1.82  Total                : 1.02
% 3.92/1.82  Index Insertion      : 0.00
% 3.92/1.82  Index Deletion       : 0.00
% 3.92/1.82  Index Matching       : 0.00
% 3.92/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
