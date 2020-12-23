%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:31 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [D_14,B_10] : r2_hidden(D_14,k2_tarski(D_14,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,'#skF_7')
      | ~ r2_hidden(D_31,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_91,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.59  
% 2.08/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.60  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.08/1.60  
% 2.08/1.60  %Foreground sorts:
% 2.08/1.60  
% 2.08/1.60  
% 2.08/1.60  %Background operators:
% 2.08/1.60  
% 2.08/1.60  
% 2.08/1.60  %Foreground operators:
% 2.08/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.08/1.60  tff('#skF_7', type, '#skF_7': $i).
% 2.08/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.60  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.60  tff('#skF_6', type, '#skF_6': $i).
% 2.08/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.08/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.60  
% 2.08/1.61  tff(f_52, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 2.08/1.61  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.08/1.61  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.08/1.61  tff(c_42, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.61  tff(c_26, plain, (![D_14, B_10]: (r2_hidden(D_14, k2_tarski(D_14, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.61  tff(c_44, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.61  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.61  tff(c_83, plain, (![D_31]: (r2_hidden(D_31, '#skF_7') | ~r2_hidden(D_31, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_4])).
% 2.08/1.61  tff(c_91, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_26, c_83])).
% 2.08/1.61  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_91])).
% 2.08/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.61  
% 2.08/1.61  Inference rules
% 2.08/1.61  ----------------------
% 2.08/1.61  #Ref     : 0
% 2.08/1.61  #Sup     : 12
% 2.08/1.61  #Fact    : 0
% 2.08/1.61  #Define  : 0
% 2.08/1.61  #Split   : 0
% 2.08/1.61  #Chain   : 0
% 2.08/1.61  #Close   : 0
% 2.08/1.61  
% 2.08/1.61  Ordering : KBO
% 2.08/1.61  
% 2.08/1.61  Simplification rules
% 2.08/1.61  ----------------------
% 2.08/1.61  #Subsume      : 0
% 2.08/1.61  #Demod        : 0
% 2.08/1.61  #Tautology    : 7
% 2.08/1.61  #SimpNegUnit  : 1
% 2.08/1.61  #BackRed      : 0
% 2.08/1.61  
% 2.08/1.61  #Partial instantiations: 0
% 2.08/1.61  #Strategies tried      : 1
% 2.08/1.61  
% 2.08/1.61  Timing (in seconds)
% 2.08/1.61  ----------------------
% 2.08/1.62  Preprocessing        : 0.52
% 2.08/1.62  Parsing              : 0.29
% 2.08/1.62  CNF conversion       : 0.04
% 2.08/1.62  Main loop            : 0.19
% 2.08/1.62  Inferencing          : 0.06
% 2.08/1.62  Reduction            : 0.06
% 2.08/1.62  Demodulation         : 0.04
% 2.19/1.62  BG Simplification    : 0.02
% 2.19/1.62  Subsumption          : 0.04
% 2.19/1.62  Abstraction          : 0.01
% 2.19/1.62  MUC search           : 0.00
% 2.19/1.62  Cooper               : 0.00
% 2.19/1.62  Total                : 0.76
% 2.19/1.62  Index Insertion      : 0.00
% 2.19/1.62  Index Deletion       : 0.00
% 2.19/1.62  Index Matching       : 0.00
% 2.19/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
