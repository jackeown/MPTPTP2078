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
% DateTime   : Thu Dec  3 09:52:40 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  79 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_20,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,k4_xboole_0(B_27,k1_tarski(C_28)))
      | r2_hidden(C_28,A_26)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [B_16,A_17] :
      ( B_16 = A_17
      | ~ r1_tarski(B_16,A_17)
      | ~ r1_tarski(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k4_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_58,plain,(
    ! [B_27,C_28] :
      ( k4_xboole_0(B_27,k1_tarski(C_28)) = B_27
      | r2_hidden(C_28,B_27)
      | ~ r1_tarski(B_27,B_27) ) ),
    inference(resolution,[status(thm)],[c_54,c_36])).

tff(c_65,plain,(
    ! [B_29,C_30] :
      ( k4_xboole_0(B_29,k1_tarski(C_30)) = B_29
      | r2_hidden(C_30,B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_83,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_30])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_83])).

tff(c_100,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_101,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_22,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_22])).

tff(c_14,plain,(
    ! [C_10,B_9] : ~ r2_hidden(C_10,k4_xboole_0(B_9,k1_tarski(C_10))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_128,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_14])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_128])).

tff(c_137,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_138,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_24,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_152,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_24])).

tff(c_156,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_14])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:12:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.65/1.14  
% 1.65/1.14  %Foreground sorts:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Background operators:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Foreground operators:
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.14  
% 1.65/1.15  tff(f_52, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.65/1.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.65/1.15  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_zfmisc_1)).
% 1.65/1.15  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.65/1.15  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.65/1.15  tff(c_20, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_28, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 1.65/1.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.15  tff(c_54, plain, (![A_26, B_27, C_28]: (r1_tarski(A_26, k4_xboole_0(B_27, k1_tarski(C_28))) | r2_hidden(C_28, A_26) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.15  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.15  tff(c_31, plain, (![B_16, A_17]: (B_16=A_17 | ~r1_tarski(B_16, A_17) | ~r1_tarski(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.15  tff(c_36, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k4_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.65/1.15  tff(c_58, plain, (![B_27, C_28]: (k4_xboole_0(B_27, k1_tarski(C_28))=B_27 | r2_hidden(C_28, B_27) | ~r1_tarski(B_27, B_27))), inference(resolution, [status(thm)], [c_54, c_36])).
% 1.65/1.15  tff(c_65, plain, (![B_29, C_30]: (k4_xboole_0(B_29, k1_tarski(C_30))=B_29 | r2_hidden(C_30, B_29))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_58])).
% 1.65/1.15  tff(c_18, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_30, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_18])).
% 1.65/1.15  tff(c_83, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_30])).
% 1.65/1.15  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_83])).
% 1.65/1.15  tff(c_100, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 1.65/1.15  tff(c_101, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 1.65/1.15  tff(c_22, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_124, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_22])).
% 1.65/1.15  tff(c_14, plain, (![C_10, B_9]: (~r2_hidden(C_10, k4_xboole_0(B_9, k1_tarski(C_10))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.65/1.15  tff(c_128, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_14])).
% 1.65/1.15  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_128])).
% 1.65/1.15  tff(c_137, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 1.65/1.15  tff(c_138, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 1.65/1.15  tff(c_24, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.15  tff(c_152, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_24])).
% 1.65/1.15  tff(c_156, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_14])).
% 1.65/1.15  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_156])).
% 1.65/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  Inference rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Ref     : 0
% 1.65/1.15  #Sup     : 31
% 1.65/1.15  #Fact    : 0
% 1.65/1.15  #Define  : 0
% 1.65/1.15  #Split   : 2
% 1.65/1.15  #Chain   : 0
% 1.65/1.15  #Close   : 0
% 1.65/1.15  
% 1.65/1.15  Ordering : KBO
% 1.65/1.15  
% 1.65/1.15  Simplification rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Subsume      : 5
% 1.65/1.15  #Demod        : 12
% 1.65/1.15  #Tautology    : 16
% 1.65/1.15  #SimpNegUnit  : 1
% 1.65/1.15  #BackRed      : 0
% 1.65/1.15  
% 1.65/1.15  #Partial instantiations: 0
% 1.65/1.15  #Strategies tried      : 1
% 1.65/1.15  
% 1.65/1.15  Timing (in seconds)
% 1.65/1.15  ----------------------
% 1.65/1.15  Preprocessing        : 0.26
% 1.65/1.15  Parsing              : 0.14
% 1.65/1.15  CNF conversion       : 0.02
% 1.65/1.15  Main loop            : 0.13
% 1.65/1.15  Inferencing          : 0.05
% 1.65/1.15  Reduction            : 0.03
% 1.65/1.15  Demodulation         : 0.02
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.03
% 1.65/1.15  Abstraction          : 0.01
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.42
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
