%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:05 EST 2020

% Result     : Theorem 13.98s
% Output     : CNFRefutation 14.06s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   28 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_70,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_72,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [D_27,B_23] : r2_hidden(D_27,k2_tarski(D_27,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_248,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_291,plain,(
    ! [D_120,B_121,B_122] :
      ( r2_hidden(D_120,B_121)
      | ~ r1_tarski(k2_tarski(D_120,B_122),B_121) ) ),
    inference(resolution,[status(thm)],[c_32,c_248])).

tff(c_306,plain,(
    ! [D_123,B_124,B_125] : r2_hidden(D_123,k2_xboole_0(k2_tarski(D_123,B_124),B_125)) ),
    inference(resolution,[status(thm)],[c_20,c_291])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26186,plain,(
    ! [D_20020,B_20021,B_20022,B_20023] :
      ( r2_hidden(D_20020,B_20021)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(D_20020,B_20022),B_20023),B_20021) ) ),
    inference(resolution,[status(thm)],[c_306,c_4])).

tff(c_26205,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_26186])).

tff(c_26220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_26205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.98/6.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.98/6.40  
% 13.98/6.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.06/6.40  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 14.06/6.40  
% 14.06/6.40  %Foreground sorts:
% 14.06/6.40  
% 14.06/6.40  
% 14.06/6.40  %Background operators:
% 14.06/6.40  
% 14.06/6.40  
% 14.06/6.40  %Foreground operators:
% 14.06/6.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.06/6.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.06/6.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.06/6.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.06/6.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.06/6.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.06/6.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.06/6.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.06/6.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.06/6.40  tff('#skF_5', type, '#skF_5': $i).
% 14.06/6.40  tff('#skF_6', type, '#skF_6': $i).
% 14.06/6.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.06/6.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.06/6.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.06/6.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.06/6.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.06/6.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.06/6.40  tff('#skF_4', type, '#skF_4': $i).
% 14.06/6.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.06/6.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.06/6.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.06/6.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.06/6.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.06/6.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.06/6.40  
% 14.06/6.41  tff(f_90, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 14.06/6.41  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.06/6.41  tff(f_61, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 14.06/6.41  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.06/6.41  tff(c_70, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.06/6.41  tff(c_72, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.06/6.41  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.06/6.41  tff(c_32, plain, (![D_27, B_23]: (r2_hidden(D_27, k2_tarski(D_27, B_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.06/6.41  tff(c_248, plain, (![C_110, B_111, A_112]: (r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.06/6.41  tff(c_291, plain, (![D_120, B_121, B_122]: (r2_hidden(D_120, B_121) | ~r1_tarski(k2_tarski(D_120, B_122), B_121))), inference(resolution, [status(thm)], [c_32, c_248])).
% 14.06/6.41  tff(c_306, plain, (![D_123, B_124, B_125]: (r2_hidden(D_123, k2_xboole_0(k2_tarski(D_123, B_124), B_125)))), inference(resolution, [status(thm)], [c_20, c_291])).
% 14.06/6.41  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.06/6.41  tff(c_26186, plain, (![D_20020, B_20021, B_20022, B_20023]: (r2_hidden(D_20020, B_20021) | ~r1_tarski(k2_xboole_0(k2_tarski(D_20020, B_20022), B_20023), B_20021))), inference(resolution, [status(thm)], [c_306, c_4])).
% 14.06/6.41  tff(c_26205, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_72, c_26186])).
% 14.06/6.41  tff(c_26220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_26205])).
% 14.06/6.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.06/6.41  
% 14.06/6.41  Inference rules
% 14.06/6.41  ----------------------
% 14.06/6.41  #Ref     : 0
% 14.06/6.41  #Sup     : 6282
% 14.06/6.41  #Fact    : 4
% 14.06/6.41  #Define  : 0
% 14.06/6.41  #Split   : 9
% 14.06/6.41  #Chain   : 0
% 14.06/6.41  #Close   : 0
% 14.06/6.41  
% 14.06/6.41  Ordering : KBO
% 14.06/6.41  
% 14.06/6.41  Simplification rules
% 14.06/6.41  ----------------------
% 14.06/6.41  #Subsume      : 417
% 14.06/6.41  #Demod        : 7896
% 14.06/6.41  #Tautology    : 2079
% 14.06/6.41  #SimpNegUnit  : 1
% 14.06/6.41  #BackRed      : 5
% 14.06/6.41  
% 14.06/6.41  #Partial instantiations: 7353
% 14.06/6.41  #Strategies tried      : 1
% 14.06/6.41  
% 14.06/6.41  Timing (in seconds)
% 14.06/6.41  ----------------------
% 14.06/6.41  Preprocessing        : 0.33
% 14.06/6.41  Parsing              : 0.17
% 14.06/6.41  CNF conversion       : 0.02
% 14.06/6.41  Main loop            : 5.33
% 14.06/6.41  Inferencing          : 0.97
% 14.06/6.41  Reduction            : 3.52
% 14.06/6.41  Demodulation         : 3.31
% 14.06/6.41  BG Simplification    : 0.14
% 14.06/6.41  Subsumption          : 0.56
% 14.06/6.41  Abstraction          : 0.19
% 14.06/6.41  MUC search           : 0.00
% 14.06/6.41  Cooper               : 0.00
% 14.06/6.41  Total                : 5.68
% 14.06/6.41  Index Insertion      : 0.00
% 14.06/6.41  Index Deletion       : 0.00
% 14.06/6.41  Index Matching       : 0.00
% 14.06/6.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
