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
% DateTime   : Thu Dec  3 09:50:43 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  31 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_26,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [C_28,B_29,A_30] :
      ( r2_hidden(C_28,B_29)
      | ~ r2_hidden(C_28,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [C_32,B_33] :
      ( r2_hidden(C_32,B_33)
      | ~ r1_tarski(k1_tarski(C_32),B_33) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_87,plain,(
    ! [C_34,B_35] : r2_hidden(C_34,k2_xboole_0(k1_tarski(C_34),B_35)) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [C_42,B_43,B_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(C_42),B_44),B_43) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_120,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:40:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.08  
% 1.71/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.08  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 1.71/1.08  
% 1.71/1.08  %Foreground sorts:
% 1.71/1.08  
% 1.71/1.08  
% 1.71/1.08  %Background operators:
% 1.71/1.08  
% 1.71/1.08  
% 1.71/1.08  %Foreground operators:
% 1.71/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.71/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.08  tff('#skF_5', type, '#skF_5': $i).
% 1.71/1.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.71/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.71/1.08  
% 1.71/1.09  tff(f_50, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.71/1.09  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.71/1.09  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.71/1.09  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.71/1.09  tff(c_26, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.71/1.09  tff(c_28, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.71/1.09  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.71/1.09  tff(c_12, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.71/1.09  tff(c_67, plain, (![C_28, B_29, A_30]: (r2_hidden(C_28, B_29) | ~r2_hidden(C_28, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.09  tff(c_75, plain, (![C_32, B_33]: (r2_hidden(C_32, B_33) | ~r1_tarski(k1_tarski(C_32), B_33))), inference(resolution, [status(thm)], [c_12, c_67])).
% 1.71/1.09  tff(c_87, plain, (![C_34, B_35]: (r2_hidden(C_34, k2_xboole_0(k1_tarski(C_34), B_35)))), inference(resolution, [status(thm)], [c_8, c_75])).
% 1.71/1.09  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.09  tff(c_113, plain, (![C_42, B_43, B_44]: (r2_hidden(C_42, B_43) | ~r1_tarski(k2_xboole_0(k1_tarski(C_42), B_44), B_43))), inference(resolution, [status(thm)], [c_87, c_2])).
% 1.71/1.09  tff(c_120, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_113])).
% 1.71/1.09  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_120])).
% 1.71/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.09  
% 1.71/1.09  Inference rules
% 1.71/1.09  ----------------------
% 1.71/1.09  #Ref     : 0
% 1.71/1.09  #Sup     : 20
% 1.71/1.09  #Fact    : 0
% 1.71/1.09  #Define  : 0
% 1.71/1.09  #Split   : 0
% 1.71/1.09  #Chain   : 0
% 1.71/1.09  #Close   : 0
% 1.71/1.09  
% 1.71/1.09  Ordering : KBO
% 1.71/1.09  
% 1.71/1.09  Simplification rules
% 1.71/1.09  ----------------------
% 1.71/1.09  #Subsume      : 0
% 1.71/1.09  #Demod        : 3
% 1.71/1.09  #Tautology    : 11
% 1.71/1.09  #SimpNegUnit  : 1
% 1.71/1.09  #BackRed      : 0
% 1.71/1.09  
% 1.71/1.09  #Partial instantiations: 0
% 1.71/1.09  #Strategies tried      : 1
% 1.71/1.09  
% 1.71/1.09  Timing (in seconds)
% 1.71/1.09  ----------------------
% 1.71/1.09  Preprocessing        : 0.26
% 1.71/1.09  Parsing              : 0.13
% 1.71/1.09  CNF conversion       : 0.02
% 1.71/1.09  Main loop            : 0.12
% 1.71/1.09  Inferencing          : 0.05
% 1.71/1.09  Reduction            : 0.04
% 1.71/1.09  Demodulation         : 0.03
% 1.71/1.09  BG Simplification    : 0.01
% 1.71/1.09  Subsumption          : 0.02
% 1.71/1.09  Abstraction          : 0.01
% 1.71/1.09  MUC search           : 0.00
% 1.71/1.09  Cooper               : 0.00
% 1.71/1.09  Total                : 0.41
% 1.71/1.09  Index Insertion      : 0.00
% 1.71/1.09  Index Deletion       : 0.00
% 1.71/1.09  Index Matching       : 0.00
% 1.71/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
