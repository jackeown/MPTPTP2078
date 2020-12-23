%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:13 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   49 (  77 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 112 expanded)
%              Number of equality atoms :   20 (  34 expanded)
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

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_26,B_27] :
      ( r2_xboole_0(A_26,B_27)
      | B_27 = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_159,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_22])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ r2_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_127,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_123])).

tff(c_220,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(A_31,C_32)
      | ~ r1_tarski(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_238,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_3')
      | ~ r1_tarski(A_35,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_127,c_220])).

tff(c_248,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_238])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_248])).

tff(c_255,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_258,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_127])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_277,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_258,c_14])).

tff(c_284,plain,(
    ! [A_36,B_37] : k2_xboole_0(A_36,k4_xboole_0(B_37,A_36)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_297,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_284])).

tff(c_308,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_297])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_300,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_284])).

tff(c_309,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_300])).

tff(c_336,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_309])).

tff(c_260,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_24])).

tff(c_344,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_260])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:20:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.91/1.19  
% 1.91/1.19  %Foreground sorts:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Background operators:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Foreground operators:
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.19  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.19  
% 2.04/1.20  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.04/1.20  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.04/1.20  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.04/1.20  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 2.04/1.20  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.04/1.20  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.04/1.20  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.04/1.20  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.04/1.20  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.20  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.20  tff(c_147, plain, (![A_26, B_27]: (r2_xboole_0(A_26, B_27) | B_27=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.20  tff(c_22, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.20  tff(c_159, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_147, c_22])).
% 2.04/1.20  tff(c_166, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_159])).
% 2.04/1.20  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.20  tff(c_24, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.20  tff(c_123, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~r2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.20  tff(c_127, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_123])).
% 2.04/1.20  tff(c_220, plain, (![A_31, C_32, B_33]: (r1_tarski(A_31, C_32) | ~r1_tarski(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.20  tff(c_238, plain, (![A_35]: (r1_tarski(A_35, '#skF_3') | ~r1_tarski(A_35, '#skF_2'))), inference(resolution, [status(thm)], [c_127, c_220])).
% 2.04/1.20  tff(c_248, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_238])).
% 2.04/1.20  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_248])).
% 2.04/1.20  tff(c_255, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_159])).
% 2.04/1.20  tff(c_258, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_127])).
% 2.04/1.20  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.20  tff(c_277, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_258, c_14])).
% 2.04/1.20  tff(c_284, plain, (![A_36, B_37]: (k2_xboole_0(A_36, k4_xboole_0(B_37, A_36))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.20  tff(c_297, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_277, c_284])).
% 2.04/1.20  tff(c_308, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_297])).
% 2.04/1.20  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.20  tff(c_130, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.20  tff(c_142, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_130])).
% 2.04/1.20  tff(c_300, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_142, c_284])).
% 2.04/1.20  tff(c_309, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_300])).
% 2.04/1.20  tff(c_336, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_308, c_309])).
% 2.04/1.20  tff(c_260, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_24])).
% 2.04/1.20  tff(c_344, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_260])).
% 2.04/1.20  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_344])).
% 2.04/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.20  
% 2.04/1.20  Inference rules
% 2.04/1.20  ----------------------
% 2.04/1.20  #Ref     : 0
% 2.04/1.20  #Sup     : 78
% 2.04/1.20  #Fact    : 0
% 2.04/1.20  #Define  : 0
% 2.04/1.20  #Split   : 1
% 2.04/1.20  #Chain   : 0
% 2.04/1.20  #Close   : 0
% 2.04/1.20  
% 2.04/1.20  Ordering : KBO
% 2.04/1.20  
% 2.04/1.20  Simplification rules
% 2.04/1.20  ----------------------
% 2.04/1.20  #Subsume      : 2
% 2.04/1.20  #Demod        : 39
% 2.04/1.20  #Tautology    : 57
% 2.04/1.20  #SimpNegUnit  : 2
% 2.04/1.20  #BackRed      : 11
% 2.04/1.20  
% 2.04/1.20  #Partial instantiations: 0
% 2.04/1.20  #Strategies tried      : 1
% 2.04/1.20  
% 2.04/1.20  Timing (in seconds)
% 2.04/1.20  ----------------------
% 2.04/1.21  Preprocessing        : 0.26
% 2.04/1.21  Parsing              : 0.15
% 2.04/1.21  CNF conversion       : 0.02
% 2.04/1.21  Main loop            : 0.20
% 2.04/1.21  Inferencing          : 0.08
% 2.04/1.21  Reduction            : 0.06
% 2.04/1.21  Demodulation         : 0.05
% 2.04/1.21  BG Simplification    : 0.01
% 2.04/1.21  Subsumption          : 0.03
% 2.04/1.21  Abstraction          : 0.01
% 2.04/1.21  MUC search           : 0.00
% 2.04/1.21  Cooper               : 0.00
% 2.04/1.21  Total                : 0.49
% 2.04/1.21  Index Insertion      : 0.00
% 2.04/1.21  Index Deletion       : 0.00
% 2.04/1.21  Index Matching       : 0.00
% 2.04/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
