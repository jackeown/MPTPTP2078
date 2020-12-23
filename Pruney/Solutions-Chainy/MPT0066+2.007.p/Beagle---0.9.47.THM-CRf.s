%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:13 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   52 (  88 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 123 expanded)
%              Number of equality atoms :   24 (  46 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_220,plain,(
    ! [A_33,B_34] :
      ( r2_xboole_0(A_33,B_34)
      | B_34 = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_232,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_220,c_22])).

tff(c_235,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_24,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_37,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_236,plain,(
    ! [A_35,B_36] : k2_xboole_0(A_35,k4_xboole_0(B_36,A_35)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_261,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_236])).

tff(c_272,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_261])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_352,plain,(
    ! [C_41] :
      ( r1_tarski('#skF_1',C_41)
      | ~ r1_tarski('#skF_2',C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_16])).

tff(c_359,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_41,c_352])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_359])).

tff(c_365,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_133,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_126])).

tff(c_369,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_133])).

tff(c_20,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_467,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_20])).

tff(c_472,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_467])).

tff(c_407,plain,(
    ! [A_42,B_43] : k2_xboole_0(A_42,k4_xboole_0(B_43,A_42)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_426,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_407])).

tff(c_435,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_426])).

tff(c_492,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_435])).

tff(c_372,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_24])).

tff(c_503,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_372])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:59:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.35  
% 2.27/1.35  %Foreground sorts:
% 2.27/1.35  
% 2.27/1.35  
% 2.27/1.35  %Background operators:
% 2.27/1.35  
% 2.27/1.35  
% 2.27/1.35  %Foreground operators:
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.35  
% 2.27/1.36  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.27/1.36  tff(f_47, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.27/1.36  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.27/1.36  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 2.27/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.27/1.36  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.27/1.36  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.27/1.36  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.27/1.36  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.36  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.27/1.36  tff(c_220, plain, (![A_33, B_34]: (r2_xboole_0(A_33, B_34) | B_34=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.36  tff(c_22, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.36  tff(c_232, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_220, c_22])).
% 2.27/1.36  tff(c_235, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_232])).
% 2.27/1.36  tff(c_24, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.36  tff(c_37, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.36  tff(c_41, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_37])).
% 2.27/1.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.36  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.36  tff(c_126, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.36  tff(c_134, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_126])).
% 2.27/1.36  tff(c_236, plain, (![A_35, B_36]: (k2_xboole_0(A_35, k4_xboole_0(B_36, A_35))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.36  tff(c_261, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_134, c_236])).
% 2.27/1.36  tff(c_272, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_261])).
% 2.27/1.36  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.36  tff(c_352, plain, (![C_41]: (r1_tarski('#skF_1', C_41) | ~r1_tarski('#skF_2', C_41))), inference(superposition, [status(thm), theory('equality')], [c_272, c_16])).
% 2.27/1.36  tff(c_359, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_41, c_352])).
% 2.27/1.36  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_359])).
% 2.27/1.36  tff(c_365, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_232])).
% 2.27/1.36  tff(c_133, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_126])).
% 2.27/1.36  tff(c_369, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_365, c_133])).
% 2.27/1.36  tff(c_20, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.36  tff(c_467, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_369, c_20])).
% 2.27/1.36  tff(c_472, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_467])).
% 2.27/1.36  tff(c_407, plain, (![A_42, B_43]: (k2_xboole_0(A_42, k4_xboole_0(B_43, A_42))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.36  tff(c_426, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_134, c_407])).
% 2.27/1.36  tff(c_435, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_426])).
% 2.27/1.36  tff(c_492, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_472, c_435])).
% 2.27/1.36  tff(c_372, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_24])).
% 2.27/1.36  tff(c_503, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_372])).
% 2.27/1.36  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_503])).
% 2.27/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.36  
% 2.27/1.36  Inference rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Ref     : 0
% 2.27/1.36  #Sup     : 122
% 2.27/1.36  #Fact    : 0
% 2.27/1.36  #Define  : 0
% 2.27/1.36  #Split   : 2
% 2.27/1.36  #Chain   : 0
% 2.27/1.36  #Close   : 0
% 2.27/1.36  
% 2.27/1.36  Ordering : KBO
% 2.27/1.36  
% 2.27/1.36  Simplification rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Subsume      : 10
% 2.27/1.36  #Demod        : 64
% 2.27/1.36  #Tautology    : 87
% 2.27/1.36  #SimpNegUnit  : 7
% 2.27/1.36  #BackRed      : 20
% 2.27/1.36  
% 2.27/1.36  #Partial instantiations: 0
% 2.27/1.36  #Strategies tried      : 1
% 2.27/1.36  
% 2.27/1.36  Timing (in seconds)
% 2.27/1.36  ----------------------
% 2.27/1.37  Preprocessing        : 0.29
% 2.27/1.37  Parsing              : 0.17
% 2.27/1.37  CNF conversion       : 0.02
% 2.27/1.37  Main loop            : 0.26
% 2.27/1.37  Inferencing          : 0.10
% 2.27/1.37  Reduction            : 0.09
% 2.27/1.37  Demodulation         : 0.07
% 2.27/1.37  BG Simplification    : 0.01
% 2.27/1.37  Subsumption          : 0.04
% 2.27/1.37  Abstraction          : 0.01
% 2.27/1.37  MUC search           : 0.00
% 2.27/1.37  Cooper               : 0.00
% 2.27/1.37  Total                : 0.58
% 2.27/1.37  Index Insertion      : 0.00
% 2.27/1.37  Index Deletion       : 0.00
% 2.27/1.37  Index Matching       : 0.00
% 2.27/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
