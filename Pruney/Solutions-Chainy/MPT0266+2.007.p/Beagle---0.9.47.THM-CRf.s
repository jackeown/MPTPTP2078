%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:27 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_38,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_46,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [D_16,A_11] : r2_hidden(D_16,k2_tarski(A_11,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_49,plain,(
    k3_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_48])).

tff(c_186,plain,(
    ! [D_35,B_36,A_37] :
      ( r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k3_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_194,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_7')
      | ~ r2_hidden(D_41,k2_tarski('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_186])).

tff(c_198,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.21  
% 1.84/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.21  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.84/1.21  
% 1.84/1.21  %Foreground sorts:
% 1.84/1.21  
% 1.84/1.21  
% 1.84/1.21  %Background operators:
% 1.84/1.21  
% 1.84/1.21  
% 1.84/1.21  %Foreground operators:
% 1.84/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.84/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.84/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.84/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.84/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.84/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.21  
% 1.84/1.22  tff(f_56, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 1.84/1.22  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.84/1.22  tff(f_38, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.84/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.84/1.22  tff(c_46, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.22  tff(c_26, plain, (![D_16, A_11]: (r2_hidden(D_16, k2_tarski(A_11, D_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.84/1.22  tff(c_22, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.84/1.22  tff(c_48, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.22  tff(c_49, plain, (k3_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_48])).
% 1.84/1.22  tff(c_186, plain, (![D_35, B_36, A_37]: (r2_hidden(D_35, B_36) | ~r2_hidden(D_35, k3_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.22  tff(c_194, plain, (![D_41]: (r2_hidden(D_41, '#skF_7') | ~r2_hidden(D_41, k2_tarski('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_49, c_186])).
% 1.84/1.22  tff(c_198, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_26, c_194])).
% 1.84/1.22  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_198])).
% 1.84/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.22  
% 1.84/1.22  Inference rules
% 1.84/1.22  ----------------------
% 1.84/1.22  #Ref     : 0
% 1.84/1.22  #Sup     : 38
% 1.84/1.22  #Fact    : 0
% 1.84/1.22  #Define  : 0
% 1.84/1.22  #Split   : 0
% 1.84/1.22  #Chain   : 0
% 1.84/1.22  #Close   : 0
% 1.84/1.22  
% 1.84/1.22  Ordering : KBO
% 1.84/1.22  
% 1.84/1.22  Simplification rules
% 1.84/1.22  ----------------------
% 1.84/1.22  #Subsume      : 1
% 1.84/1.22  #Demod        : 9
% 1.84/1.22  #Tautology    : 32
% 1.84/1.22  #SimpNegUnit  : 1
% 1.84/1.22  #BackRed      : 0
% 1.84/1.22  
% 1.84/1.22  #Partial instantiations: 0
% 1.84/1.22  #Strategies tried      : 1
% 1.84/1.22  
% 1.84/1.22  Timing (in seconds)
% 1.84/1.22  ----------------------
% 1.84/1.22  Preprocessing        : 0.31
% 1.84/1.22  Parsing              : 0.15
% 1.84/1.22  CNF conversion       : 0.02
% 1.84/1.22  Main loop            : 0.15
% 1.84/1.22  Inferencing          : 0.04
% 1.84/1.22  Reduction            : 0.06
% 1.84/1.22  Demodulation         : 0.05
% 1.84/1.22  BG Simplification    : 0.01
% 1.84/1.22  Subsumption          : 0.03
% 1.84/1.22  Abstraction          : 0.01
% 1.84/1.22  MUC search           : 0.00
% 1.84/1.22  Cooper               : 0.00
% 1.84/1.22  Total                : 0.48
% 1.84/1.22  Index Insertion      : 0.00
% 1.84/1.22  Index Deletion       : 0.00
% 1.84/1.22  Index Matching       : 0.00
% 1.84/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
