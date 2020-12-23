%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:14 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   39 (  70 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 ( 114 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_19,B_20] :
      ( r2_xboole_0(A_19,B_20)
      | B_20 = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_16])).

tff(c_118,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_55,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r2_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_111,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,'#skF_3')
      | ~ r1_tarski(A_25,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_59,c_111])).

tff(c_133,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_127])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_133])).

tff(c_139,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_60,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_59,c_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2])).

tff(c_141,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_76])).

tff(c_68,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_210,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_68])).

tff(c_145,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_18])).

tff(c_220,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_145])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.26  
% 1.90/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.26  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.90/1.26  
% 1.90/1.26  %Foreground sorts:
% 1.90/1.26  
% 1.90/1.26  
% 1.90/1.26  %Background operators:
% 1.90/1.26  
% 1.90/1.26  
% 1.90/1.26  %Foreground operators:
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.26  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.26  
% 1.90/1.27  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.90/1.27  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.90/1.27  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.90/1.27  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.90/1.27  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.90/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.90/1.27  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.90/1.27  tff(c_96, plain, (![A_19, B_20]: (r2_xboole_0(A_19, B_20) | B_20=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.27  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.27  tff(c_110, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_16])).
% 1.90/1.27  tff(c_118, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_110])).
% 1.90/1.27  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.27  tff(c_18, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.27  tff(c_55, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.27  tff(c_59, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_55])).
% 1.90/1.27  tff(c_111, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.27  tff(c_127, plain, (![A_25]: (r1_tarski(A_25, '#skF_3') | ~r1_tarski(A_25, '#skF_2'))), inference(resolution, [status(thm)], [c_59, c_111])).
% 1.90/1.27  tff(c_133, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_127])).
% 1.90/1.27  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_133])).
% 1.90/1.27  tff(c_139, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_110])).
% 1.90/1.27  tff(c_60, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.27  tff(c_67, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_59, c_60])).
% 1.90/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.90/1.27  tff(c_76, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_67, c_2])).
% 1.90/1.27  tff(c_141, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_76])).
% 1.90/1.27  tff(c_68, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_60])).
% 1.90/1.27  tff(c_210, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_68])).
% 1.90/1.27  tff(c_145, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_18])).
% 1.90/1.27  tff(c_220, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_145])).
% 1.90/1.27  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_220])).
% 1.90/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.27  
% 1.90/1.27  Inference rules
% 1.90/1.27  ----------------------
% 1.90/1.27  #Ref     : 0
% 1.90/1.27  #Sup     : 51
% 1.90/1.27  #Fact    : 0
% 1.90/1.27  #Define  : 0
% 1.90/1.27  #Split   : 1
% 1.90/1.27  #Chain   : 0
% 1.90/1.27  #Close   : 0
% 1.90/1.27  
% 1.90/1.27  Ordering : KBO
% 1.90/1.27  
% 1.90/1.27  Simplification rules
% 1.90/1.27  ----------------------
% 1.90/1.27  #Subsume      : 2
% 1.90/1.27  #Demod        : 26
% 1.90/1.27  #Tautology    : 37
% 1.90/1.27  #SimpNegUnit  : 2
% 1.90/1.27  #BackRed      : 11
% 1.90/1.27  
% 1.90/1.27  #Partial instantiations: 0
% 1.90/1.27  #Strategies tried      : 1
% 1.90/1.27  
% 1.90/1.27  Timing (in seconds)
% 1.90/1.27  ----------------------
% 1.90/1.27  Preprocessing        : 0.28
% 1.90/1.27  Parsing              : 0.16
% 1.90/1.27  CNF conversion       : 0.02
% 1.90/1.27  Main loop            : 0.19
% 1.90/1.28  Inferencing          : 0.07
% 1.90/1.28  Reduction            : 0.06
% 1.90/1.28  Demodulation         : 0.04
% 1.90/1.28  BG Simplification    : 0.01
% 1.90/1.28  Subsumption          : 0.03
% 1.90/1.28  Abstraction          : 0.01
% 1.90/1.28  MUC search           : 0.00
% 1.90/1.28  Cooper               : 0.00
% 1.90/1.28  Total                : 0.50
% 1.90/1.28  Index Insertion      : 0.00
% 1.90/1.28  Index Deletion       : 0.00
% 1.90/1.28  Index Matching       : 0.00
% 1.90/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
