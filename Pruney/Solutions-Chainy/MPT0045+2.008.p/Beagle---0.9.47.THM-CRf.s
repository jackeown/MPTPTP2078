%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:45 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  43 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [C_25,B_26,A_27] :
      ( r2_hidden(C_25,B_26)
      | ~ r2_hidden(C_25,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_31,B_32,B_33] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_33)
      | ~ r1_tarski(A_31,B_33)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_801,plain,(
    ! [A_115,B_116,B_117,A_118] :
      ( ~ r2_hidden('#skF_1'(A_115,B_116),B_117)
      | ~ r1_tarski(A_115,k4_xboole_0(A_118,B_117))
      | r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_79,c_10])).

tff(c_821,plain,(
    ! [A_119,A_120,B_121] :
      ( ~ r1_tarski(A_119,k4_xboole_0(A_120,A_119))
      | r1_tarski(A_119,B_121) ) ),
    inference(resolution,[status(thm)],[c_6,c_801])).

tff(c_839,plain,(
    ! [B_122] : r1_tarski('#skF_4',B_122) ),
    inference(resolution,[status(thm)],[c_30,c_821])).

tff(c_26,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_855,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_839,c_26])).

tff(c_866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.38  
% 2.64/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.38  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.64/1.38  
% 2.64/1.38  %Foreground sorts:
% 2.64/1.38  
% 2.64/1.38  
% 2.64/1.38  %Background operators:
% 2.64/1.38  
% 2.64/1.38  
% 2.64/1.38  %Foreground operators:
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.64/1.38  
% 2.64/1.39  tff(f_51, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.64/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.64/1.39  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.64/1.39  tff(f_46, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.64/1.39  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.39  tff(c_30, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.39  tff(c_58, plain, (![C_25, B_26, A_27]: (r2_hidden(C_25, B_26) | ~r2_hidden(C_25, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.39  tff(c_79, plain, (![A_31, B_32, B_33]: (r2_hidden('#skF_1'(A_31, B_32), B_33) | ~r1_tarski(A_31, B_33) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_6, c_58])).
% 2.64/1.39  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.64/1.39  tff(c_801, plain, (![A_115, B_116, B_117, A_118]: (~r2_hidden('#skF_1'(A_115, B_116), B_117) | ~r1_tarski(A_115, k4_xboole_0(A_118, B_117)) | r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_79, c_10])).
% 2.64/1.39  tff(c_821, plain, (![A_119, A_120, B_121]: (~r1_tarski(A_119, k4_xboole_0(A_120, A_119)) | r1_tarski(A_119, B_121))), inference(resolution, [status(thm)], [c_6, c_801])).
% 2.64/1.39  tff(c_839, plain, (![B_122]: (r1_tarski('#skF_4', B_122))), inference(resolution, [status(thm)], [c_30, c_821])).
% 2.64/1.39  tff(c_26, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.64/1.39  tff(c_855, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_839, c_26])).
% 2.64/1.39  tff(c_866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_855])).
% 2.64/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.39  
% 2.64/1.39  Inference rules
% 2.64/1.39  ----------------------
% 2.64/1.39  #Ref     : 0
% 2.64/1.39  #Sup     : 178
% 2.64/1.39  #Fact    : 0
% 2.64/1.39  #Define  : 0
% 2.64/1.39  #Split   : 1
% 2.64/1.39  #Chain   : 0
% 2.64/1.39  #Close   : 0
% 2.64/1.39  
% 2.64/1.39  Ordering : KBO
% 2.64/1.39  
% 2.64/1.39  Simplification rules
% 2.64/1.39  ----------------------
% 2.64/1.39  #Subsume      : 29
% 2.64/1.39  #Demod        : 86
% 2.64/1.39  #Tautology    : 68
% 2.64/1.39  #SimpNegUnit  : 1
% 2.64/1.39  #BackRed      : 1
% 2.64/1.39  
% 2.64/1.39  #Partial instantiations: 0
% 2.64/1.39  #Strategies tried      : 1
% 2.64/1.39  
% 2.64/1.39  Timing (in seconds)
% 2.64/1.39  ----------------------
% 2.64/1.39  Preprocessing        : 0.27
% 2.64/1.39  Parsing              : 0.14
% 2.64/1.39  CNF conversion       : 0.02
% 2.64/1.39  Main loop            : 0.36
% 2.64/1.39  Inferencing          : 0.14
% 2.64/1.39  Reduction            : 0.09
% 2.64/1.40  Demodulation         : 0.07
% 2.64/1.40  BG Simplification    : 0.02
% 2.64/1.40  Subsumption          : 0.08
% 2.64/1.40  Abstraction          : 0.02
% 2.64/1.40  MUC search           : 0.00
% 2.64/1.40  Cooper               : 0.00
% 2.64/1.40  Total                : 0.66
% 2.64/1.40  Index Insertion      : 0.00
% 2.64/1.40  Index Deletion       : 0.00
% 2.64/1.40  Index Matching       : 0.00
% 2.64/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
