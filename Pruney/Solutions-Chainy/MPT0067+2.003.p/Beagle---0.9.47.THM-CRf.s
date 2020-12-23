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
% DateTime   : Thu Dec  3 09:43:15 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  33 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_tarski(A,B)
          & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ r2_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_18])).

tff(c_56,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_2])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_85,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64])).

tff(c_93,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_14])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.21  
% 1.78/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.21  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.78/1.21  
% 1.78/1.21  %Foreground sorts:
% 1.78/1.21  
% 1.78/1.21  
% 1.78/1.21  %Background operators:
% 1.78/1.21  
% 1.78/1.21  
% 1.78/1.21  %Foreground operators:
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.21  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.21  
% 1.78/1.22  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.78/1.22  tff(f_47, negated_conjecture, ~(![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.78/1.22  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.78/1.22  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.78/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.78/1.22  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.78/1.22  tff(c_14, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.78/1.22  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~r2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.78/1.22  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_18])).
% 1.78/1.22  tff(c_56, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.78/1.22  tff(c_63, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_56])).
% 1.78/1.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.22  tff(c_72, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_63, c_2])).
% 1.78/1.22  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.78/1.22  tff(c_64, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_56])).
% 1.78/1.22  tff(c_85, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64])).
% 1.78/1.22  tff(c_93, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_14])).
% 1.78/1.22  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_93])).
% 1.78/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.22  
% 1.78/1.22  Inference rules
% 1.78/1.22  ----------------------
% 1.78/1.22  #Ref     : 0
% 1.78/1.22  #Sup     : 21
% 1.78/1.22  #Fact    : 0
% 1.78/1.22  #Define  : 0
% 1.78/1.22  #Split   : 0
% 1.78/1.22  #Chain   : 0
% 1.78/1.22  #Close   : 0
% 1.78/1.22  
% 1.78/1.22  Ordering : KBO
% 1.78/1.22  
% 1.78/1.22  Simplification rules
% 1.78/1.22  ----------------------
% 1.78/1.22  #Subsume      : 1
% 1.78/1.22  #Demod        : 6
% 1.78/1.22  #Tautology    : 14
% 1.78/1.22  #SimpNegUnit  : 1
% 1.78/1.22  #BackRed      : 6
% 1.78/1.22  
% 1.78/1.22  #Partial instantiations: 0
% 1.78/1.22  #Strategies tried      : 1
% 1.78/1.22  
% 1.78/1.22  Timing (in seconds)
% 1.78/1.22  ----------------------
% 1.78/1.22  Preprocessing        : 0.27
% 1.78/1.22  Parsing              : 0.15
% 1.78/1.22  CNF conversion       : 0.02
% 1.78/1.22  Main loop            : 0.11
% 1.78/1.22  Inferencing          : 0.04
% 1.78/1.22  Reduction            : 0.03
% 1.78/1.22  Demodulation         : 0.03
% 1.78/1.22  BG Simplification    : 0.01
% 1.78/1.22  Subsumption          : 0.02
% 1.78/1.22  Abstraction          : 0.00
% 1.78/1.22  MUC search           : 0.00
% 1.78/1.22  Cooper               : 0.00
% 1.78/1.22  Total                : 0.40
% 1.78/1.22  Index Insertion      : 0.00
% 1.78/1.22  Index Deletion       : 0.00
% 1.78/1.22  Index Matching       : 0.00
% 1.78/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
