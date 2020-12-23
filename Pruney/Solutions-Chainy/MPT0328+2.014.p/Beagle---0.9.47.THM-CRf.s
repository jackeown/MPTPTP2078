%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:39 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_10,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,k1_tarski(B_10)) = A_9
      | r2_hidden(B_10,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_39,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_11])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:21:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.15  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.73/1.15  
% 1.73/1.15  %Foreground sorts:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Background operators:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Foreground operators:
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.15  
% 1.73/1.16  tff(f_38, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.73/1.16  tff(f_32, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.73/1.16  tff(f_27, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.73/1.16  tff(c_10, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.16  tff(c_26, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k1_tarski(B_10))=A_9 | r2_hidden(B_10, A_9))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.73/1.16  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), B_2)=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.73/1.16  tff(c_8, plain, (k4_xboole_0(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.16  tff(c_11, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 1.73/1.16  tff(c_39, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_11])).
% 1.73/1.16  tff(c_52, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_39])).
% 1.73/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  Inference rules
% 1.73/1.16  ----------------------
% 1.73/1.16  #Ref     : 0
% 1.73/1.16  #Sup     : 9
% 1.73/1.16  #Fact    : 0
% 1.73/1.16  #Define  : 0
% 1.73/1.16  #Split   : 0
% 1.73/1.16  #Chain   : 0
% 1.73/1.16  #Close   : 0
% 1.73/1.16  
% 1.73/1.16  Ordering : KBO
% 1.73/1.16  
% 1.73/1.16  Simplification rules
% 1.73/1.16  ----------------------
% 1.73/1.16  #Subsume      : 0
% 1.73/1.16  #Demod        : 1
% 1.73/1.16  #Tautology    : 4
% 1.73/1.16  #SimpNegUnit  : 1
% 1.73/1.16  #BackRed      : 0
% 1.73/1.16  
% 1.73/1.16  #Partial instantiations: 0
% 1.73/1.16  #Strategies tried      : 1
% 1.73/1.16  
% 1.73/1.16  Timing (in seconds)
% 1.73/1.16  ----------------------
% 1.73/1.16  Preprocessing        : 0.26
% 1.73/1.16  Parsing              : 0.15
% 1.73/1.16  CNF conversion       : 0.02
% 1.73/1.16  Main loop            : 0.09
% 1.73/1.16  Inferencing          : 0.05
% 1.73/1.17  Reduction            : 0.02
% 1.73/1.17  Demodulation         : 0.02
% 1.73/1.17  BG Simplification    : 0.01
% 1.73/1.17  Subsumption          : 0.01
% 1.73/1.17  Abstraction          : 0.00
% 1.73/1.17  MUC search           : 0.00
% 1.73/1.17  Cooper               : 0.00
% 1.73/1.17  Total                : 0.37
% 1.73/1.17  Index Insertion      : 0.00
% 1.73/1.17  Index Deletion       : 0.00
% 1.73/1.17  Index Matching       : 0.00
% 1.73/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
