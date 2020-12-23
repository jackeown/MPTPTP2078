%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:28 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_14,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [B_12,A_13] : k3_xboole_0(B_12,A_13) = k3_xboole_0(A_13,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [B_12,A_13] : r1_tarski(k3_xboole_0(B_12,A_13),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4])).

tff(c_87,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_33])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r2_hidden(A_7,C_9)
      | ~ r1_tarski(k2_tarski(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_12])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.68/1.12  
% 1.68/1.12  %Foreground sorts:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Background operators:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Foreground operators:
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.12  
% 1.68/1.12  tff(f_42, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 1.68/1.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.68/1.12  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.68/1.12  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.68/1.12  tff(c_14, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.12  tff(c_16, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.12  tff(c_18, plain, (![B_12, A_13]: (k3_xboole_0(B_12, A_13)=k3_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.12  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.12  tff(c_33, plain, (![B_12, A_13]: (r1_tarski(k3_xboole_0(B_12, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4])).
% 1.68/1.12  tff(c_87, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_33])).
% 1.68/1.12  tff(c_12, plain, (![A_7, C_9, B_8]: (r2_hidden(A_7, C_9) | ~r1_tarski(k2_tarski(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.68/1.12  tff(c_108, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_87, c_12])).
% 1.68/1.12  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_108])).
% 1.68/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  
% 1.68/1.12  Inference rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Ref     : 0
% 1.68/1.12  #Sup     : 26
% 1.68/1.12  #Fact    : 0
% 1.68/1.12  #Define  : 0
% 1.68/1.12  #Split   : 0
% 1.68/1.12  #Chain   : 0
% 1.68/1.12  #Close   : 0
% 1.68/1.12  
% 1.68/1.12  Ordering : KBO
% 1.68/1.12  
% 1.68/1.12  Simplification rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Subsume      : 0
% 1.68/1.12  #Demod        : 3
% 1.68/1.12  #Tautology    : 15
% 1.68/1.12  #SimpNegUnit  : 1
% 1.68/1.12  #BackRed      : 0
% 1.68/1.12  
% 1.68/1.12  #Partial instantiations: 0
% 1.68/1.12  #Strategies tried      : 1
% 1.68/1.12  
% 1.68/1.12  Timing (in seconds)
% 1.68/1.12  ----------------------
% 1.68/1.13  Preprocessing        : 0.26
% 1.68/1.13  Parsing              : 0.14
% 1.68/1.13  CNF conversion       : 0.02
% 1.68/1.13  Main loop            : 0.12
% 1.68/1.13  Inferencing          : 0.05
% 1.68/1.13  Reduction            : 0.04
% 1.68/1.13  Demodulation         : 0.03
% 1.68/1.13  BG Simplification    : 0.01
% 1.68/1.13  Subsumption          : 0.02
% 1.68/1.13  Abstraction          : 0.01
% 1.68/1.13  MUC search           : 0.00
% 1.68/1.13  Cooper               : 0.00
% 1.68/1.13  Total                : 0.40
% 1.68/1.13  Index Insertion      : 0.00
% 1.68/1.13  Index Deletion       : 0.00
% 1.68/1.13  Index Matching       : 0.00
% 1.68/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
