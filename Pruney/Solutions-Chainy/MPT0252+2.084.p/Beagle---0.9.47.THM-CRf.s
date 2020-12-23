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
% DateTime   : Thu Dec  3 09:51:11 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  50 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

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

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_67,axiom,(
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

tff(c_62,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_68,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_12])).

tff(c_64,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_328,plain,(
    ! [C_102,A_103,D_104] :
      ( r2_hidden(C_102,k3_tarski(A_103))
      | ~ r2_hidden(D_104,A_103)
      | ~ r2_hidden(C_102,D_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_332,plain,(
    ! [C_102,A_60,B_61] :
      ( r2_hidden(C_102,k3_tarski(k2_tarski(A_60,B_61)))
      | ~ r2_hidden(C_102,A_60) ) ),
    inference(resolution,[status(thm)],[c_77,c_328])).

tff(c_349,plain,(
    ! [C_105,A_106,B_107] :
      ( r2_hidden(C_105,k2_xboole_0(A_106,B_107))
      | ~ r2_hidden(C_105,A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_332])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_599,plain,(
    ! [C_148,B_149,A_150,B_151] :
      ( r2_hidden(C_148,B_149)
      | ~ r1_tarski(k2_xboole_0(A_150,B_151),B_149)
      | ~ r2_hidden(C_148,A_150) ) ),
    inference(resolution,[status(thm)],[c_349,c_2])).

tff(c_607,plain,(
    ! [C_152] :
      ( r2_hidden(C_152,'#skF_10')
      | ~ r2_hidden(C_152,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_64,c_599])).

tff(c_623,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_77,c_607])).

tff(c_635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.39  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.61/1.39  
% 2.61/1.39  %Foreground sorts:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Background operators:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Foreground operators:
% 2.61/1.39  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.39  tff('#skF_10', type, '#skF_10': $i).
% 2.61/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.61/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.61/1.39  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.61/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.61/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.39  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.61/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.61/1.39  
% 2.61/1.40  tff(f_74, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.61/1.40  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.61/1.40  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.61/1.40  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.61/1.40  tff(f_67, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.61/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.61/1.40  tff(c_62, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.40  tff(c_68, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.61/1.40  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.40  tff(c_77, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_12])).
% 2.61/1.40  tff(c_64, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.40  tff(c_60, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.40  tff(c_328, plain, (![C_102, A_103, D_104]: (r2_hidden(C_102, k3_tarski(A_103)) | ~r2_hidden(D_104, A_103) | ~r2_hidden(C_102, D_104))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.61/1.40  tff(c_332, plain, (![C_102, A_60, B_61]: (r2_hidden(C_102, k3_tarski(k2_tarski(A_60, B_61))) | ~r2_hidden(C_102, A_60))), inference(resolution, [status(thm)], [c_77, c_328])).
% 2.61/1.40  tff(c_349, plain, (![C_105, A_106, B_107]: (r2_hidden(C_105, k2_xboole_0(A_106, B_107)) | ~r2_hidden(C_105, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_332])).
% 2.61/1.40  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.40  tff(c_599, plain, (![C_148, B_149, A_150, B_151]: (r2_hidden(C_148, B_149) | ~r1_tarski(k2_xboole_0(A_150, B_151), B_149) | ~r2_hidden(C_148, A_150))), inference(resolution, [status(thm)], [c_349, c_2])).
% 2.61/1.40  tff(c_607, plain, (![C_152]: (r2_hidden(C_152, '#skF_10') | ~r2_hidden(C_152, k2_tarski('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_64, c_599])).
% 2.61/1.40  tff(c_623, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_77, c_607])).
% 2.61/1.40  tff(c_635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_623])).
% 2.61/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.40  
% 2.61/1.40  Inference rules
% 2.61/1.40  ----------------------
% 2.61/1.40  #Ref     : 0
% 2.61/1.40  #Sup     : 135
% 2.61/1.40  #Fact    : 0
% 2.61/1.40  #Define  : 0
% 2.61/1.40  #Split   : 0
% 2.61/1.40  #Chain   : 0
% 2.61/1.40  #Close   : 0
% 2.61/1.40  
% 2.61/1.40  Ordering : KBO
% 2.61/1.40  
% 2.61/1.40  Simplification rules
% 2.61/1.40  ----------------------
% 2.61/1.40  #Subsume      : 26
% 2.61/1.40  #Demod        : 40
% 2.61/1.40  #Tautology    : 51
% 2.61/1.40  #SimpNegUnit  : 1
% 2.61/1.40  #BackRed      : 0
% 2.61/1.40  
% 2.61/1.40  #Partial instantiations: 0
% 2.61/1.40  #Strategies tried      : 1
% 2.61/1.40  
% 2.61/1.40  Timing (in seconds)
% 2.61/1.40  ----------------------
% 2.61/1.41  Preprocessing        : 0.31
% 2.61/1.41  Parsing              : 0.15
% 2.61/1.41  CNF conversion       : 0.03
% 2.61/1.41  Main loop            : 0.28
% 2.61/1.41  Inferencing          : 0.10
% 2.61/1.41  Reduction            : 0.10
% 2.61/1.41  Demodulation         : 0.07
% 2.61/1.41  BG Simplification    : 0.02
% 2.61/1.41  Subsumption          : 0.05
% 2.61/1.41  Abstraction          : 0.02
% 2.61/1.41  MUC search           : 0.00
% 2.61/1.41  Cooper               : 0.00
% 2.61/1.41  Total                : 0.62
% 2.61/1.41  Index Insertion      : 0.00
% 2.61/1.41  Index Deletion       : 0.00
% 2.61/1.41  Index Matching       : 0.00
% 2.61/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
