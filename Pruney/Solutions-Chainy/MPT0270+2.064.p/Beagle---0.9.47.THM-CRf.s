%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:01 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  70 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_24,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_39,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_45,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(k1_tarski(A_45),B_46) = k1_tarski(A_45)
      | r2_hidden(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_45,c_6])).

tff(c_22,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_113,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_129,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_113])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_129])).

tff(c_144,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_145,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_26])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_xboole_0(k4_xboole_0(A_3,B_4),B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_165,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden(A_17,B_18)
      | ~ r1_xboole_0(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_181,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_165,c_18])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_181])).

tff(c_189,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_190,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_226,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_28])).

tff(c_230,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_4])).

tff(c_236,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_230,c_18])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:42:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.87/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.18  
% 1.87/1.19  tff(f_57, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 1.87/1.19  tff(f_51, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.87/1.19  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.87/1.19  tff(f_29, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.87/1.19  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.87/1.19  tff(c_24, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.19  tff(c_39, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 1.87/1.19  tff(c_45, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.87/1.19  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.19  tff(c_123, plain, (![A_45, B_46]: (k4_xboole_0(k1_tarski(A_45), B_46)=k1_tarski(A_45) | r2_hidden(A_45, B_46))), inference(resolution, [status(thm)], [c_45, c_6])).
% 1.87/1.19  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.19  tff(c_113, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 1.87/1.19  tff(c_129, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_123, c_113])).
% 1.87/1.19  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_129])).
% 1.87/1.19  tff(c_144, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 1.87/1.19  tff(c_145, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 1.87/1.19  tff(c_26, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.19  tff(c_158, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_26])).
% 1.87/1.19  tff(c_4, plain, (![A_3, B_4]: (r1_xboole_0(k4_xboole_0(A_3, B_4), B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.19  tff(c_165, plain, (r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_158, c_4])).
% 1.87/1.19  tff(c_18, plain, (![A_17, B_18]: (~r2_hidden(A_17, B_18) | ~r1_xboole_0(k1_tarski(A_17), B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.19  tff(c_181, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_165, c_18])).
% 1.87/1.19  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_181])).
% 1.87/1.19  tff(c_189, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 1.87/1.19  tff(c_190, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 1.87/1.19  tff(c_28, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.19  tff(c_226, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_28])).
% 1.87/1.19  tff(c_230, plain, (r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_226, c_4])).
% 1.87/1.19  tff(c_236, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_230, c_18])).
% 1.87/1.19  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_236])).
% 1.87/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  Inference rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Ref     : 0
% 1.87/1.19  #Sup     : 49
% 1.87/1.19  #Fact    : 0
% 1.87/1.19  #Define  : 0
% 1.87/1.19  #Split   : 2
% 1.87/1.19  #Chain   : 0
% 1.87/1.19  #Close   : 0
% 1.87/1.19  
% 1.87/1.19  Ordering : KBO
% 1.87/1.19  
% 1.87/1.19  Simplification rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Subsume      : 2
% 1.87/1.19  #Demod        : 14
% 1.87/1.19  #Tautology    : 31
% 1.87/1.19  #SimpNegUnit  : 1
% 1.87/1.19  #BackRed      : 0
% 1.87/1.19  
% 1.87/1.19  #Partial instantiations: 0
% 1.87/1.19  #Strategies tried      : 1
% 1.87/1.19  
% 1.87/1.19  Timing (in seconds)
% 1.87/1.19  ----------------------
% 1.97/1.19  Preprocessing        : 0.29
% 1.97/1.19  Parsing              : 0.15
% 1.97/1.19  CNF conversion       : 0.02
% 1.97/1.19  Main loop            : 0.15
% 1.97/1.19  Inferencing          : 0.06
% 1.97/1.19  Reduction            : 0.04
% 1.97/1.19  Demodulation         : 0.03
% 1.97/1.19  BG Simplification    : 0.01
% 1.97/1.19  Subsumption          : 0.02
% 1.97/1.19  Abstraction          : 0.01
% 1.97/1.19  MUC search           : 0.00
% 1.97/1.19  Cooper               : 0.00
% 1.97/1.19  Total                : 0.46
% 1.97/1.19  Index Insertion      : 0.00
% 1.97/1.19  Index Deletion       : 0.00
% 1.97/1.19  Index Matching       : 0.00
% 1.97/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
