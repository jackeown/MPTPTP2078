%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:11 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  81 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 ( 109 expanded)
%              Number of equality atoms :   23 (  42 expanded)
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
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

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
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_37,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_126,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_126])).

tff(c_236,plain,(
    ! [A_35,B_36] : k2_xboole_0(A_35,k4_xboole_0(B_36,A_35)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_258,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_236])).

tff(c_271,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_258])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_360,plain,(
    ! [C_42] :
      ( r1_tarski('#skF_1',C_42)
      | ~ r1_tarski('#skF_2',C_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_16])).

tff(c_370,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_360])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_370])).

tff(c_377,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_134,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_126])).

tff(c_381,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_134])).

tff(c_421,plain,(
    ! [A_43,B_44] : k2_xboole_0(A_43,k4_xboole_0(B_44,A_43)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_437,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_421])).

tff(c_451,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_437])).

tff(c_443,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_421])).

tff(c_453,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_443])).

tff(c_498,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_453])).

tff(c_506,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_26])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:50:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.23  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.23  
% 2.08/1.23  %Foreground sorts:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Background operators:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Foreground operators:
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.23  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.23  
% 2.21/1.24  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.21/1.24  tff(f_47, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.21/1.24  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.21/1.24  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 2.21/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.21/1.24  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.21/1.24  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.21/1.24  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.21/1.24  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.24  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.24  tff(c_220, plain, (![A_33, B_34]: (r2_xboole_0(A_33, B_34) | B_34=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.21/1.24  tff(c_22, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.24  tff(c_232, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_220, c_22])).
% 2.21/1.24  tff(c_235, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_232])).
% 2.21/1.24  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.24  tff(c_26, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.24  tff(c_37, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.21/1.24  tff(c_41, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_37])).
% 2.21/1.24  tff(c_126, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.24  tff(c_133, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_126])).
% 2.21/1.24  tff(c_236, plain, (![A_35, B_36]: (k2_xboole_0(A_35, k4_xboole_0(B_36, A_35))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.24  tff(c_258, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_133, c_236])).
% 2.21/1.24  tff(c_271, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_258])).
% 2.21/1.24  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.24  tff(c_360, plain, (![C_42]: (r1_tarski('#skF_1', C_42) | ~r1_tarski('#skF_2', C_42))), inference(superposition, [status(thm), theory('equality')], [c_271, c_16])).
% 2.21/1.24  tff(c_370, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_360])).
% 2.21/1.24  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_370])).
% 2.21/1.24  tff(c_377, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_232])).
% 2.21/1.24  tff(c_134, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_126])).
% 2.21/1.24  tff(c_381, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_377, c_134])).
% 2.21/1.24  tff(c_421, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k4_xboole_0(B_44, A_43))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.24  tff(c_437, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_381, c_421])).
% 2.21/1.24  tff(c_451, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_437])).
% 2.21/1.24  tff(c_443, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_133, c_421])).
% 2.21/1.24  tff(c_453, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_443])).
% 2.21/1.24  tff(c_498, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_451, c_453])).
% 2.21/1.24  tff(c_506, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_26])).
% 2.21/1.24  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_506])).
% 2.21/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  Inference rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Ref     : 0
% 2.21/1.24  #Sup     : 121
% 2.21/1.24  #Fact    : 0
% 2.21/1.24  #Define  : 0
% 2.21/1.24  #Split   : 2
% 2.21/1.24  #Chain   : 0
% 2.21/1.24  #Close   : 0
% 2.21/1.24  
% 2.21/1.24  Ordering : KBO
% 2.21/1.24  
% 2.21/1.24  Simplification rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Subsume      : 11
% 2.21/1.24  #Demod        : 65
% 2.21/1.24  #Tautology    : 87
% 2.21/1.24  #SimpNegUnit  : 7
% 2.21/1.24  #BackRed      : 18
% 2.21/1.24  
% 2.21/1.24  #Partial instantiations: 0
% 2.21/1.24  #Strategies tried      : 1
% 2.21/1.24  
% 2.21/1.24  Timing (in seconds)
% 2.21/1.24  ----------------------
% 2.21/1.24  Preprocessing        : 0.26
% 2.21/1.24  Parsing              : 0.14
% 2.21/1.24  CNF conversion       : 0.02
% 2.21/1.24  Main loop            : 0.24
% 2.21/1.24  Inferencing          : 0.09
% 2.21/1.24  Reduction            : 0.08
% 2.21/1.24  Demodulation         : 0.06
% 2.21/1.24  BG Simplification    : 0.01
% 2.21/1.24  Subsumption          : 0.04
% 2.21/1.24  Abstraction          : 0.01
% 2.21/1.24  MUC search           : 0.00
% 2.21/1.24  Cooper               : 0.00
% 2.21/1.24  Total                : 0.53
% 2.21/1.24  Index Insertion      : 0.00
% 2.21/1.24  Index Deletion       : 0.00
% 2.21/1.24  Index Matching       : 0.00
% 2.21/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
