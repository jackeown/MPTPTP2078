%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:42 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   48 (  53 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  53 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_70,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_114,plain,(
    ! [A_81,B_82] : k1_enumset1(A_81,A_81,B_82) = k2_tarski(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_203,plain,(
    ! [A_86,B_87] : r2_hidden(A_86,k2_tarski(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_12])).

tff(c_206,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_203])).

tff(c_72,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_8'),'#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_68,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_120,plain,(
    ! [A_81,B_82] : r2_hidden(A_81,k2_tarski(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_12])).

tff(c_624,plain,(
    ! [C_114,A_115,D_116] :
      ( r2_hidden(C_114,k3_tarski(A_115))
      | ~ r2_hidden(D_116,A_115)
      | ~ r2_hidden(C_114,D_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_632,plain,(
    ! [C_114,A_81,B_82] :
      ( r2_hidden(C_114,k3_tarski(k2_tarski(A_81,B_82)))
      | ~ r2_hidden(C_114,A_81) ) ),
    inference(resolution,[status(thm)],[c_120,c_624])).

tff(c_836,plain,(
    ! [C_126,A_127,B_128] :
      ( r2_hidden(C_126,k2_xboole_0(A_127,B_128))
      | ~ r2_hidden(C_126,A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_632])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1608,plain,(
    ! [C_224,B_225,A_226,B_227] :
      ( r2_hidden(C_224,B_225)
      | ~ r1_tarski(k2_xboole_0(A_226,B_227),B_225)
      | ~ r2_hidden(C_224,A_226) ) ),
    inference(resolution,[status(thm)],[c_836,c_2])).

tff(c_1618,plain,(
    ! [C_228] :
      ( r2_hidden(C_228,'#skF_9')
      | ~ r2_hidden(C_228,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_72,c_1608])).

tff(c_1650,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_206,c_1618])).

tff(c_1664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:04:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.59  
% 3.39/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.60  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.39/1.60  
% 3.39/1.60  %Foreground sorts:
% 3.39/1.60  
% 3.39/1.60  
% 3.39/1.60  %Background operators:
% 3.39/1.60  
% 3.39/1.60  
% 3.39/1.60  %Foreground operators:
% 3.39/1.60  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.39/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.39/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.39/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.60  tff('#skF_9', type, '#skF_9': $i).
% 3.39/1.60  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.39/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.39/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.39/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.39/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.39/1.60  
% 3.39/1.61  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.39/1.61  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.39/1.61  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.39/1.61  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.39/1.61  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.39/1.61  tff(f_75, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 3.39/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.39/1.61  tff(c_70, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.39/1.61  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.39/1.61  tff(c_114, plain, (![A_81, B_82]: (k1_enumset1(A_81, A_81, B_82)=k2_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.61  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.61  tff(c_203, plain, (![A_86, B_87]: (r2_hidden(A_86, k2_tarski(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_12])).
% 3.39/1.61  tff(c_206, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_203])).
% 3.39/1.61  tff(c_72, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_8'), '#skF_9'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.39/1.61  tff(c_68, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.39/1.61  tff(c_120, plain, (![A_81, B_82]: (r2_hidden(A_81, k2_tarski(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_12])).
% 3.39/1.61  tff(c_624, plain, (![C_114, A_115, D_116]: (r2_hidden(C_114, k3_tarski(A_115)) | ~r2_hidden(D_116, A_115) | ~r2_hidden(C_114, D_116))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.39/1.61  tff(c_632, plain, (![C_114, A_81, B_82]: (r2_hidden(C_114, k3_tarski(k2_tarski(A_81, B_82))) | ~r2_hidden(C_114, A_81))), inference(resolution, [status(thm)], [c_120, c_624])).
% 3.39/1.61  tff(c_836, plain, (![C_126, A_127, B_128]: (r2_hidden(C_126, k2_xboole_0(A_127, B_128)) | ~r2_hidden(C_126, A_127))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_632])).
% 3.39/1.61  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.61  tff(c_1608, plain, (![C_224, B_225, A_226, B_227]: (r2_hidden(C_224, B_225) | ~r1_tarski(k2_xboole_0(A_226, B_227), B_225) | ~r2_hidden(C_224, A_226))), inference(resolution, [status(thm)], [c_836, c_2])).
% 3.39/1.61  tff(c_1618, plain, (![C_228]: (r2_hidden(C_228, '#skF_9') | ~r2_hidden(C_228, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_72, c_1608])).
% 3.39/1.61  tff(c_1650, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_206, c_1618])).
% 3.39/1.61  tff(c_1664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1650])).
% 3.39/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.61  
% 3.39/1.61  Inference rules
% 3.39/1.61  ----------------------
% 3.39/1.61  #Ref     : 0
% 3.39/1.61  #Sup     : 405
% 3.39/1.61  #Fact    : 0
% 3.39/1.61  #Define  : 0
% 3.39/1.61  #Split   : 0
% 3.39/1.61  #Chain   : 0
% 3.39/1.61  #Close   : 0
% 3.39/1.61  
% 3.39/1.61  Ordering : KBO
% 3.39/1.61  
% 3.39/1.61  Simplification rules
% 3.39/1.61  ----------------------
% 3.39/1.61  #Subsume      : 126
% 3.39/1.61  #Demod        : 112
% 3.39/1.61  #Tautology    : 144
% 3.39/1.61  #SimpNegUnit  : 1
% 3.39/1.61  #BackRed      : 0
% 3.39/1.61  
% 3.39/1.61  #Partial instantiations: 0
% 3.39/1.61  #Strategies tried      : 1
% 3.39/1.61  
% 3.39/1.61  Timing (in seconds)
% 3.39/1.61  ----------------------
% 3.39/1.61  Preprocessing        : 0.35
% 3.39/1.61  Parsing              : 0.17
% 3.39/1.61  CNF conversion       : 0.03
% 3.39/1.61  Main loop            : 0.52
% 3.39/1.61  Inferencing          : 0.17
% 3.39/1.61  Reduction            : 0.20
% 3.39/1.61  Demodulation         : 0.16
% 3.39/1.61  BG Simplification    : 0.03
% 3.39/1.61  Subsumption          : 0.09
% 3.39/1.61  Abstraction          : 0.03
% 3.73/1.61  MUC search           : 0.00
% 3.73/1.61  Cooper               : 0.00
% 3.73/1.61  Total                : 0.89
% 3.73/1.61  Index Insertion      : 0.00
% 3.73/1.61  Index Deletion       : 0.00
% 3.73/1.61  Index Matching       : 0.00
% 3.73/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
