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
% DateTime   : Thu Dec  3 09:43:11 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   38 (  66 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 ( 103 expanded)
%              Number of equality atoms :   13 (  27 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [A_22,B_23] :
      ( r2_xboole_0(A_22,B_23)
      | B_23 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_16])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_55,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r2_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_55])).

tff(c_60,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_59,c_60])).

tff(c_96,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(A_19,C_20)
      | ~ r1_tarski(k2_xboole_0(A_19,B_21),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [C_25] :
      ( r1_tarski('#skF_1',C_25)
      | ~ r1_tarski('#skF_2',C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_96])).

tff(c_139,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_133])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_139])).

tff(c_145,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_68,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_148,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_145,c_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_173,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2])).

tff(c_207,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_67])).

tff(c_222,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_20])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:20 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.25  
% 1.84/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.25  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.84/1.25  
% 1.84/1.25  %Foreground sorts:
% 1.84/1.25  
% 1.84/1.25  
% 1.84/1.25  %Background operators:
% 1.84/1.25  
% 1.84/1.25  
% 1.84/1.25  %Foreground operators:
% 1.84/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.25  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.84/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.25  
% 1.84/1.26  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.84/1.26  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.84/1.26  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.84/1.26  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.84/1.26  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.84/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.84/1.26  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.26  tff(c_112, plain, (![A_22, B_23]: (r2_xboole_0(A_22, B_23) | B_23=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.26  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.26  tff(c_126, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_112, c_16])).
% 1.84/1.26  tff(c_127, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_126])).
% 1.84/1.26  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.26  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.26  tff(c_55, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.26  tff(c_59, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_55])).
% 1.84/1.26  tff(c_60, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.26  tff(c_67, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_59, c_60])).
% 1.84/1.26  tff(c_96, plain, (![A_19, C_20, B_21]: (r1_tarski(A_19, C_20) | ~r1_tarski(k2_xboole_0(A_19, B_21), C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.26  tff(c_133, plain, (![C_25]: (r1_tarski('#skF_1', C_25) | ~r1_tarski('#skF_2', C_25))), inference(superposition, [status(thm), theory('equality')], [c_67, c_96])).
% 1.84/1.26  tff(c_139, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_133])).
% 1.84/1.26  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_139])).
% 1.84/1.26  tff(c_145, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_126])).
% 1.84/1.26  tff(c_68, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_60])).
% 1.84/1.26  tff(c_148, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_145, c_68])).
% 1.84/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.26  tff(c_173, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_148, c_2])).
% 1.84/1.26  tff(c_207, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_67])).
% 1.84/1.26  tff(c_222, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_20])).
% 1.84/1.26  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_222])).
% 1.84/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.26  
% 1.84/1.26  Inference rules
% 1.84/1.26  ----------------------
% 1.84/1.26  #Ref     : 0
% 1.84/1.26  #Sup     : 55
% 1.84/1.26  #Fact    : 0
% 1.84/1.26  #Define  : 0
% 1.84/1.26  #Split   : 1
% 1.84/1.26  #Chain   : 0
% 1.84/1.26  #Close   : 0
% 1.84/1.26  
% 1.84/1.26  Ordering : KBO
% 1.84/1.26  
% 1.84/1.26  Simplification rules
% 1.84/1.26  ----------------------
% 1.84/1.26  #Subsume      : 4
% 1.84/1.26  #Demod        : 21
% 1.84/1.26  #Tautology    : 38
% 1.84/1.26  #SimpNegUnit  : 2
% 1.84/1.26  #BackRed      : 10
% 1.84/1.26  
% 1.84/1.26  #Partial instantiations: 0
% 1.84/1.26  #Strategies tried      : 1
% 1.84/1.26  
% 1.84/1.26  Timing (in seconds)
% 1.84/1.26  ----------------------
% 1.84/1.27  Preprocessing        : 0.26
% 1.84/1.27  Parsing              : 0.14
% 1.84/1.27  CNF conversion       : 0.02
% 1.84/1.27  Main loop            : 0.23
% 1.84/1.27  Inferencing          : 0.08
% 1.84/1.27  Reduction            : 0.08
% 1.84/1.27  Demodulation         : 0.06
% 1.84/1.27  BG Simplification    : 0.01
% 1.84/1.27  Subsumption          : 0.04
% 1.84/1.27  Abstraction          : 0.01
% 1.84/1.27  MUC search           : 0.00
% 1.84/1.27  Cooper               : 0.00
% 1.84/1.27  Total                : 0.52
% 1.84/1.27  Index Insertion      : 0.00
% 1.84/1.27  Index Deletion       : 0.00
% 1.84/1.27  Index Matching       : 0.00
% 1.84/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
