%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:13 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   37 (  80 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   41 ( 122 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_12,plain,(
    ! [A_7] : ~ r2_xboole_0(A_7,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_20,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ r2_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_73,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_65,c_66])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_4])).

tff(c_101,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,B_24)
      | ~ r1_tarski(A_23,k3_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,'#skF_3')
      | ~ r1_tarski(A_26,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_101])).

tff(c_122,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_118])).

tff(c_134,plain,(
    ! [A_27,B_28] :
      ( r2_xboole_0(A_27,B_28)
      | B_28 = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_18])).

tff(c_157,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_149])).

tff(c_161,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_82])).

tff(c_167,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_161])).

tff(c_166,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_20])).

tff(c_190,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_166])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  %$ r2_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.19  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.19  
% 1.88/1.20  tff(f_42, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.88/1.20  tff(f_57, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.88/1.20  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.88/1.20  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.88/1.20  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.88/1.20  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.88/1.20  tff(c_12, plain, (![A_7]: (~r2_xboole_0(A_7, A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.20  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.20  tff(c_66, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.20  tff(c_74, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_66])).
% 1.88/1.20  tff(c_20, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.20  tff(c_61, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~r2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.20  tff(c_65, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_61])).
% 1.88/1.20  tff(c_73, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_65, c_66])).
% 1.88/1.20  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.20  tff(c_82, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_73, c_4])).
% 1.88/1.20  tff(c_101, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, B_24) | ~r1_tarski(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.20  tff(c_118, plain, (![A_26]: (r1_tarski(A_26, '#skF_3') | ~r1_tarski(A_26, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_101])).
% 1.88/1.20  tff(c_122, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_118])).
% 1.88/1.20  tff(c_134, plain, (![A_27, B_28]: (r2_xboole_0(A_27, B_28) | B_28=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.20  tff(c_18, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.20  tff(c_149, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_134, c_18])).
% 1.88/1.20  tff(c_157, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_149])).
% 1.88/1.20  tff(c_161, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_82])).
% 1.88/1.20  tff(c_167, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_161])).
% 1.88/1.20  tff(c_166, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_20])).
% 1.88/1.20  tff(c_190, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_166])).
% 1.88/1.20  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_190])).
% 1.88/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  Inference rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Ref     : 0
% 1.88/1.20  #Sup     : 43
% 1.88/1.20  #Fact    : 0
% 1.88/1.20  #Define  : 0
% 1.88/1.20  #Split   : 0
% 1.88/1.20  #Chain   : 0
% 1.88/1.20  #Close   : 0
% 1.88/1.20  
% 1.88/1.20  Ordering : KBO
% 1.88/1.20  
% 1.88/1.20  Simplification rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Subsume      : 3
% 1.88/1.20  #Demod        : 21
% 1.88/1.20  #Tautology    : 30
% 1.88/1.20  #SimpNegUnit  : 1
% 1.88/1.20  #BackRed      : 11
% 1.88/1.20  
% 1.88/1.21  #Partial instantiations: 0
% 1.88/1.21  #Strategies tried      : 1
% 1.88/1.21  
% 1.88/1.21  Timing (in seconds)
% 1.88/1.21  ----------------------
% 1.88/1.21  Preprocessing        : 0.26
% 1.88/1.21  Parsing              : 0.14
% 1.88/1.21  CNF conversion       : 0.02
% 1.88/1.21  Main loop            : 0.16
% 1.88/1.21  Inferencing          : 0.06
% 1.88/1.21  Reduction            : 0.05
% 1.88/1.21  Demodulation         : 0.04
% 1.88/1.21  BG Simplification    : 0.01
% 1.88/1.21  Subsumption          : 0.03
% 1.88/1.21  Abstraction          : 0.01
% 1.88/1.21  MUC search           : 0.00
% 1.88/1.21  Cooper               : 0.00
% 1.88/1.21  Total                : 0.45
% 1.88/1.21  Index Insertion      : 0.00
% 1.88/1.21  Index Deletion       : 0.00
% 1.88/1.21  Index Matching       : 0.00
% 1.88/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
