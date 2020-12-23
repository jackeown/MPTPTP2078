%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:27 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_50,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    ! [A_32,B_33] : r2_hidden(A_32,k2_tarski(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_26])).

tff(c_52,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | ~ r2_hidden(D_38,k3_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_168,plain,(
    ! [D_47] :
      ( r2_hidden(D_47,'#skF_7')
      | ~ r2_hidden(D_47,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_126])).

tff(c_172,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_98,c_168])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:47:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.95/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.95/1.22  
% 1.95/1.23  tff(f_60, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 1.95/1.23  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.95/1.23  tff(f_51, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.95/1.23  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.95/1.23  tff(c_50, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.95/1.23  tff(c_89, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.23  tff(c_26, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.23  tff(c_98, plain, (![A_32, B_33]: (r2_hidden(A_32, k2_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_26])).
% 1.95/1.23  tff(c_52, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.95/1.23  tff(c_126, plain, (![D_38, B_39, A_40]: (r2_hidden(D_38, B_39) | ~r2_hidden(D_38, k3_xboole_0(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.95/1.23  tff(c_168, plain, (![D_47]: (r2_hidden(D_47, '#skF_7') | ~r2_hidden(D_47, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_126])).
% 1.95/1.23  tff(c_172, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_98, c_168])).
% 1.95/1.23  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_172])).
% 1.95/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  Inference rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Ref     : 0
% 1.95/1.23  #Sup     : 33
% 1.95/1.23  #Fact    : 0
% 1.95/1.23  #Define  : 0
% 1.95/1.23  #Split   : 0
% 1.95/1.23  #Chain   : 0
% 1.95/1.23  #Close   : 0
% 1.95/1.23  
% 1.95/1.23  Ordering : KBO
% 1.95/1.23  
% 1.95/1.23  Simplification rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Subsume      : 4
% 1.95/1.23  #Demod        : 4
% 1.95/1.23  #Tautology    : 22
% 1.95/1.23  #SimpNegUnit  : 1
% 1.95/1.23  #BackRed      : 0
% 1.95/1.23  
% 1.95/1.23  #Partial instantiations: 0
% 1.95/1.23  #Strategies tried      : 1
% 1.95/1.23  
% 1.95/1.23  Timing (in seconds)
% 1.95/1.23  ----------------------
% 1.95/1.23  Preprocessing        : 0.31
% 1.95/1.24  Parsing              : 0.16
% 1.95/1.24  CNF conversion       : 0.02
% 1.95/1.24  Main loop            : 0.15
% 1.95/1.24  Inferencing          : 0.04
% 1.95/1.24  Reduction            : 0.06
% 1.95/1.24  Demodulation         : 0.04
% 1.95/1.24  BG Simplification    : 0.01
% 1.95/1.24  Subsumption          : 0.03
% 1.95/1.24  Abstraction          : 0.01
% 1.95/1.24  MUC search           : 0.00
% 1.95/1.24  Cooper               : 0.00
% 1.95/1.24  Total                : 0.48
% 1.95/1.24  Index Insertion      : 0.00
% 1.95/1.24  Index Deletion       : 0.00
% 1.95/1.24  Index Matching       : 0.00
% 2.04/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
