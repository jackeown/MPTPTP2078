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
% DateTime   : Thu Dec  3 09:43:10 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   36 (  56 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   40 (  79 expanded)
%              Number of equality atoms :   13 (  23 expanded)
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
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ r2_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_66,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_65,c_66])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_88,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_74])).

tff(c_101,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,B_24)
      | ~ r1_tarski(A_23,k3_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,'#skF_3')
      | ~ r1_tarski(A_26,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_101])).

tff(c_122,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_118])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_88])).

tff(c_165,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_161])).

tff(c_173,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_22])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:03:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.14  
% 1.71/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.14  %$ r2_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.71/1.14  
% 1.71/1.14  %Foreground sorts:
% 1.71/1.14  
% 1.71/1.14  
% 1.71/1.14  %Background operators:
% 1.71/1.14  
% 1.71/1.14  
% 1.71/1.14  %Foreground operators:
% 1.71/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.14  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.71/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.14  
% 1.71/1.15  tff(f_42, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.71/1.15  tff(f_57, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.71/1.15  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.71/1.15  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.71/1.15  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.71/1.15  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.71/1.15  tff(c_12, plain, (![A_7]: (~r2_xboole_0(A_7, A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.15  tff(c_22, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.71/1.15  tff(c_61, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~r2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.15  tff(c_65, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_61])).
% 1.71/1.15  tff(c_66, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.71/1.15  tff(c_73, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_65, c_66])).
% 1.71/1.15  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.15  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.71/1.15  tff(c_74, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_66])).
% 1.71/1.15  tff(c_88, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4, c_74])).
% 1.71/1.15  tff(c_101, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, B_24) | ~r1_tarski(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.15  tff(c_118, plain, (![A_26]: (r1_tarski(A_26, '#skF_3') | ~r1_tarski(A_26, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_101])).
% 1.71/1.15  tff(c_122, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_65, c_118])).
% 1.71/1.15  tff(c_134, plain, (![A_27, B_28]: (r2_xboole_0(A_27, B_28) | B_28=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.15  tff(c_18, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.71/1.15  tff(c_149, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_134, c_18])).
% 1.71/1.15  tff(c_157, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_149])).
% 1.71/1.15  tff(c_161, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_88])).
% 1.71/1.15  tff(c_165, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_161])).
% 1.71/1.15  tff(c_173, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_22])).
% 1.71/1.15  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_173])).
% 1.71/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  Inference rules
% 1.71/1.15  ----------------------
% 1.71/1.15  #Ref     : 0
% 1.71/1.15  #Sup     : 39
% 1.71/1.15  #Fact    : 0
% 1.71/1.15  #Define  : 0
% 1.71/1.15  #Split   : 0
% 1.71/1.15  #Chain   : 0
% 1.71/1.15  #Close   : 0
% 1.71/1.15  
% 1.71/1.15  Ordering : KBO
% 1.71/1.15  
% 1.71/1.15  Simplification rules
% 1.71/1.15  ----------------------
% 1.71/1.15  #Subsume      : 3
% 1.71/1.15  #Demod        : 16
% 1.71/1.15  #Tautology    : 26
% 1.71/1.15  #SimpNegUnit  : 1
% 1.71/1.15  #BackRed      : 11
% 1.71/1.15  
% 1.71/1.15  #Partial instantiations: 0
% 1.71/1.15  #Strategies tried      : 1
% 1.71/1.15  
% 1.71/1.15  Timing (in seconds)
% 1.71/1.15  ----------------------
% 1.71/1.15  Preprocessing        : 0.25
% 1.71/1.15  Parsing              : 0.13
% 1.71/1.15  CNF conversion       : 0.02
% 1.71/1.15  Main loop            : 0.15
% 1.71/1.15  Inferencing          : 0.06
% 1.71/1.15  Reduction            : 0.05
% 1.71/1.15  Demodulation         : 0.04
% 1.71/1.15  BG Simplification    : 0.01
% 1.71/1.15  Subsumption          : 0.03
% 1.71/1.15  Abstraction          : 0.01
% 1.71/1.15  MUC search           : 0.00
% 1.71/1.15  Cooper               : 0.00
% 1.71/1.15  Total                : 0.42
% 1.71/1.15  Index Insertion      : 0.00
% 1.71/1.15  Index Deletion       : 0.00
% 1.71/1.15  Index Matching       : 0.00
% 1.71/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
