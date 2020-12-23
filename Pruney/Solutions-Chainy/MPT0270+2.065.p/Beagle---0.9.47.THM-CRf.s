%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:01 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  58 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_8,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_13,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(k1_tarski(A_1),B_2) = k1_tarski(A_1)
      | r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_23,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6])).

tff(c_26,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_23])).

tff(c_30,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13,c_26])).

tff(c_31,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6])).

tff(c_32,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_6])).

tff(c_10,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden(A_1,B_2)
      | k4_xboole_0(k1_tarski(A_1),B_2) != k1_tarski(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_61,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_61])).

tff(c_74,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_75,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_12,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_102,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden(A_9,B_10)
      | k4_xboole_0(k1_tarski(A_9),B_10) != k1_tarski(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_108,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_102])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.09  
% 1.60/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  %$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.60/1.10  
% 1.60/1.10  %Foreground sorts:
% 1.60/1.10  
% 1.60/1.10  
% 1.60/1.10  %Background operators:
% 1.60/1.10  
% 1.60/1.10  
% 1.60/1.10  %Foreground operators:
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.10  
% 1.60/1.11  tff(f_36, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 1.60/1.11  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.60/1.11  tff(c_8, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.60/1.11  tff(c_13, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_8])).
% 1.60/1.11  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(k1_tarski(A_1), B_2)=k1_tarski(A_1) | r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.60/1.11  tff(c_6, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.60/1.11  tff(c_23, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_6])).
% 1.60/1.11  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_23])).
% 1.60/1.11  tff(c_30, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13, c_26])).
% 1.60/1.11  tff(c_31, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_6])).
% 1.60/1.11  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_6])).
% 1.60/1.11  tff(c_10, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.60/1.11  tff(c_57, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10])).
% 1.60/1.11  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden(A_1, B_2) | k4_xboole_0(k1_tarski(A_1), B_2)!=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.60/1.11  tff(c_61, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 1.60/1.11  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_61])).
% 1.60/1.11  tff(c_74, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_8])).
% 1.60/1.11  tff(c_75, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_8])).
% 1.60/1.11  tff(c_12, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.60/1.11  tff(c_77, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_12])).
% 1.60/1.11  tff(c_102, plain, (![A_9, B_10]: (~r2_hidden(A_9, B_10) | k4_xboole_0(k1_tarski(A_9), B_10)!=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.60/1.11  tff(c_108, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77, c_102])).
% 1.60/1.11  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_108])).
% 1.60/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.11  
% 1.60/1.11  Inference rules
% 1.60/1.11  ----------------------
% 1.60/1.11  #Ref     : 0
% 1.60/1.11  #Sup     : 22
% 1.60/1.11  #Fact    : 0
% 1.60/1.11  #Define  : 0
% 1.60/1.11  #Split   : 2
% 1.60/1.11  #Chain   : 0
% 1.60/1.11  #Close   : 0
% 1.60/1.11  
% 1.60/1.11  Ordering : KBO
% 1.60/1.11  
% 1.60/1.11  Simplification rules
% 1.60/1.11  ----------------------
% 1.60/1.11  #Subsume      : 2
% 1.60/1.11  #Demod        : 7
% 1.60/1.11  #Tautology    : 16
% 1.60/1.11  #SimpNegUnit  : 3
% 1.60/1.11  #BackRed      : 0
% 1.60/1.11  
% 1.60/1.11  #Partial instantiations: 0
% 1.60/1.11  #Strategies tried      : 1
% 1.60/1.11  
% 1.60/1.11  Timing (in seconds)
% 1.60/1.11  ----------------------
% 1.60/1.11  Preprocessing        : 0.23
% 1.60/1.11  Parsing              : 0.12
% 1.60/1.11  CNF conversion       : 0.02
% 1.60/1.11  Main loop            : 0.09
% 1.60/1.11  Inferencing          : 0.04
% 1.60/1.11  Reduction            : 0.02
% 1.60/1.11  Demodulation         : 0.01
% 1.60/1.11  BG Simplification    : 0.01
% 1.60/1.11  Subsumption          : 0.01
% 1.60/1.11  Abstraction          : 0.01
% 1.60/1.11  MUC search           : 0.00
% 1.60/1.11  Cooper               : 0.00
% 1.60/1.11  Total                : 0.36
% 1.60/1.11  Index Insertion      : 0.00
% 1.60/1.11  Index Deletion       : 0.00
% 1.60/1.11  Index Matching       : 0.00
% 1.60/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
