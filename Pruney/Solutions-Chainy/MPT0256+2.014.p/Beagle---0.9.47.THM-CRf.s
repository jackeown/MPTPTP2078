%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:03 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    ! [D_25,A_26,B_27] :
      ( r2_hidden(D_25,A_26)
      | ~ r2_hidden(D_25,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    ! [D_28] :
      ( r2_hidden(D_28,'#skF_5')
      | ~ r2_hidden(D_28,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_85])).

tff(c_93,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_89])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.29  
% 1.95/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.29  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.95/1.29  
% 1.95/1.29  %Foreground sorts:
% 1.95/1.29  
% 1.95/1.29  
% 1.95/1.29  %Background operators:
% 1.95/1.29  
% 1.95/1.29  
% 1.95/1.29  %Foreground operators:
% 1.95/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.95/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.29  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.95/1.29  
% 1.95/1.30  tff(f_52, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.95/1.30  tff(f_43, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.95/1.30  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.95/1.30  tff(c_38, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.30  tff(c_24, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.30  tff(c_40, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.30  tff(c_85, plain, (![D_25, A_26, B_27]: (r2_hidden(D_25, A_26) | ~r2_hidden(D_25, k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.95/1.30  tff(c_89, plain, (![D_28]: (r2_hidden(D_28, '#skF_5') | ~r2_hidden(D_28, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_85])).
% 1.95/1.30  tff(c_93, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_89])).
% 1.95/1.30  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_93])).
% 1.95/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.30  
% 1.95/1.30  Inference rules
% 1.95/1.30  ----------------------
% 1.95/1.30  #Ref     : 0
% 1.95/1.30  #Sup     : 13
% 1.95/1.30  #Fact    : 0
% 1.95/1.30  #Define  : 0
% 1.95/1.30  #Split   : 0
% 1.95/1.30  #Chain   : 0
% 1.95/1.30  #Close   : 0
% 1.95/1.30  
% 1.95/1.30  Ordering : KBO
% 1.95/1.30  
% 1.95/1.30  Simplification rules
% 1.95/1.30  ----------------------
% 1.95/1.30  #Subsume      : 0
% 1.95/1.30  #Demod        : 0
% 1.95/1.30  #Tautology    : 9
% 1.95/1.30  #SimpNegUnit  : 1
% 1.95/1.30  #BackRed      : 0
% 1.95/1.30  
% 1.95/1.30  #Partial instantiations: 0
% 1.95/1.30  #Strategies tried      : 1
% 1.95/1.30  
% 1.95/1.30  Timing (in seconds)
% 1.95/1.30  ----------------------
% 1.95/1.30  Preprocessing        : 0.38
% 1.95/1.30  Parsing              : 0.18
% 1.95/1.30  CNF conversion       : 0.03
% 1.95/1.30  Main loop            : 0.13
% 1.95/1.30  Inferencing          : 0.04
% 1.95/1.30  Reduction            : 0.04
% 1.95/1.30  Demodulation         : 0.02
% 1.95/1.30  BG Simplification    : 0.02
% 1.95/1.30  Subsumption          : 0.03
% 1.95/1.30  Abstraction          : 0.01
% 1.95/1.30  MUC search           : 0.00
% 1.95/1.30  Cooper               : 0.00
% 1.95/1.30  Total                : 0.53
% 1.95/1.30  Index Insertion      : 0.00
% 1.95/1.30  Index Deletion       : 0.00
% 1.95/1.30  Index Matching       : 0.00
% 1.95/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
