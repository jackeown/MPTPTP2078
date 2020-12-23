%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:03 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  43 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_58,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_112,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [E_20,A_14,C_16] : r2_hidden(E_20,k1_enumset1(A_14,E_20,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_118,plain,(
    ! [A_41,B_42] : r2_hidden(A_41,k2_tarski(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_32])).

tff(c_56,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_97,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,(
    ! [B_49,A_50] : k3_tarski(k2_tarski(B_49,A_50)) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_97])).

tff(c_162,plain,(
    ! [B_27,A_26] : k2_xboole_0(B_27,A_26) = k2_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_150])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_180,plain,(
    r1_tarski(k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_7')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_60])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_239,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_373,plain,(
    ! [D_93,B_94,A_95,B_96] :
      ( r2_hidden(D_93,B_94)
      | ~ r1_tarski(k2_xboole_0(A_95,B_96),B_94)
      | ~ r2_hidden(D_93,B_96) ) ),
    inference(resolution,[status(thm)],[c_10,c_239])).

tff(c_385,plain,(
    ! [D_97] :
      ( r2_hidden(D_97,'#skF_8')
      | ~ r2_hidden(D_97,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_180,c_373])).

tff(c_397,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_118,c_385])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.28  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 2.11/1.28  
% 2.11/1.28  %Foreground sorts:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Background operators:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Foreground operators:
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.11/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.11/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.11/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.11/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.28  
% 2.11/1.29  tff(f_69, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.11/1.29  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.11/1.29  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.11/1.29  tff(f_64, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.11/1.29  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.11/1.29  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.11/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.11/1.29  tff(c_58, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.11/1.29  tff(c_112, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.29  tff(c_32, plain, (![E_20, A_14, C_16]: (r2_hidden(E_20, k1_enumset1(A_14, E_20, C_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.11/1.29  tff(c_118, plain, (![A_41, B_42]: (r2_hidden(A_41, k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_32])).
% 2.11/1.29  tff(c_56, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.29  tff(c_26, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.29  tff(c_97, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.29  tff(c_150, plain, (![B_49, A_50]: (k3_tarski(k2_tarski(B_49, A_50))=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_26, c_97])).
% 2.11/1.29  tff(c_162, plain, (![B_27, A_26]: (k2_xboole_0(B_27, A_26)=k2_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_56, c_150])).
% 2.11/1.29  tff(c_60, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.11/1.29  tff(c_180, plain, (r1_tarski(k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_7')), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_60])).
% 2.11/1.29  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.29  tff(c_239, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.11/1.29  tff(c_373, plain, (![D_93, B_94, A_95, B_96]: (r2_hidden(D_93, B_94) | ~r1_tarski(k2_xboole_0(A_95, B_96), B_94) | ~r2_hidden(D_93, B_96))), inference(resolution, [status(thm)], [c_10, c_239])).
% 2.11/1.29  tff(c_385, plain, (![D_97]: (r2_hidden(D_97, '#skF_8') | ~r2_hidden(D_97, k2_tarski('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_180, c_373])).
% 2.11/1.29  tff(c_397, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_118, c_385])).
% 2.11/1.29  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_397])).
% 2.11/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  Inference rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Ref     : 0
% 2.11/1.29  #Sup     : 81
% 2.11/1.29  #Fact    : 0
% 2.11/1.29  #Define  : 0
% 2.11/1.29  #Split   : 0
% 2.11/1.29  #Chain   : 0
% 2.11/1.29  #Close   : 0
% 2.11/1.29  
% 2.11/1.29  Ordering : KBO
% 2.11/1.29  
% 2.11/1.29  Simplification rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Subsume      : 13
% 2.11/1.29  #Demod        : 14
% 2.11/1.29  #Tautology    : 42
% 2.11/1.29  #SimpNegUnit  : 1
% 2.11/1.29  #BackRed      : 1
% 2.11/1.29  
% 2.11/1.29  #Partial instantiations: 0
% 2.11/1.29  #Strategies tried      : 1
% 2.11/1.29  
% 2.11/1.29  Timing (in seconds)
% 2.11/1.29  ----------------------
% 2.11/1.29  Preprocessing        : 0.30
% 2.11/1.29  Parsing              : 0.15
% 2.11/1.29  CNF conversion       : 0.02
% 2.11/1.29  Main loop            : 0.22
% 2.11/1.29  Inferencing          : 0.07
% 2.11/1.29  Reduction            : 0.08
% 2.11/1.29  Demodulation         : 0.06
% 2.11/1.29  BG Simplification    : 0.02
% 2.11/1.29  Subsumption          : 0.04
% 2.11/1.29  Abstraction          : 0.01
% 2.11/1.29  MUC search           : 0.00
% 2.11/1.29  Cooper               : 0.00
% 2.11/1.29  Total                : 0.55
% 2.11/1.29  Index Insertion      : 0.00
% 2.11/1.29  Index Deletion       : 0.00
% 2.11/1.29  Index Matching       : 0.00
% 2.11/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
