%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:50 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   29 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_94,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_96,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_152,plain,(
    ! [B_64,A_65] : k2_xboole_0(B_64,A_65) = k2_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_268,plain,(
    ! [B_71,A_72] : r1_tarski(B_71,k2_xboole_0(A_72,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_44])).

tff(c_274,plain,(
    r1_tarski(k1_tarski('#skF_9'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_268])).

tff(c_74,plain,(
    ! [C_40] : r2_hidden(C_40,k1_tarski(C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_884,plain,(
    ! [C_121,B_122,A_123] :
      ( r2_hidden(C_121,B_122)
      | ~ r2_hidden(C_121,A_123)
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_913,plain,(
    ! [C_124,B_125] :
      ( r2_hidden(C_124,B_125)
      | ~ r1_tarski(k1_tarski(C_124),B_125) ) ),
    inference(resolution,[status(thm)],[c_74,c_884])).

tff(c_929,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_274,c_913])).

tff(c_72,plain,(
    ! [C_40,A_36] :
      ( C_40 = A_36
      | ~ r2_hidden(C_40,k1_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_938,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_929,c_72])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:56:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.38  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_1
% 2.81/1.38  
% 2.81/1.38  %Foreground sorts:
% 2.81/1.38  
% 2.81/1.38  
% 2.81/1.38  %Background operators:
% 2.81/1.38  
% 2.81/1.38  
% 2.81/1.38  %Foreground operators:
% 2.81/1.38  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.81/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.81/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.81/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.81/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.81/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.38  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.81/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.38  
% 2.81/1.39  tff(f_103, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.81/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.81/1.39  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.81/1.39  tff(f_88, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.81/1.39  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.81/1.39  tff(c_94, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.81/1.39  tff(c_96, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.81/1.39  tff(c_152, plain, (![B_64, A_65]: (k2_xboole_0(B_64, A_65)=k2_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.39  tff(c_44, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.39  tff(c_268, plain, (![B_71, A_72]: (r1_tarski(B_71, k2_xboole_0(A_72, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_44])).
% 2.81/1.39  tff(c_274, plain, (r1_tarski(k1_tarski('#skF_9'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_268])).
% 2.81/1.39  tff(c_74, plain, (![C_40]: (r2_hidden(C_40, k1_tarski(C_40)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.81/1.39  tff(c_884, plain, (![C_121, B_122, A_123]: (r2_hidden(C_121, B_122) | ~r2_hidden(C_121, A_123) | ~r1_tarski(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.81/1.39  tff(c_913, plain, (![C_124, B_125]: (r2_hidden(C_124, B_125) | ~r1_tarski(k1_tarski(C_124), B_125))), inference(resolution, [status(thm)], [c_74, c_884])).
% 2.81/1.39  tff(c_929, plain, (r2_hidden('#skF_9', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_274, c_913])).
% 2.81/1.39  tff(c_72, plain, (![C_40, A_36]: (C_40=A_36 | ~r2_hidden(C_40, k1_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.81/1.39  tff(c_938, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_929, c_72])).
% 2.81/1.39  tff(c_943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_938])).
% 2.81/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.39  
% 2.81/1.39  Inference rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Ref     : 0
% 2.81/1.39  #Sup     : 215
% 2.81/1.39  #Fact    : 0
% 2.81/1.39  #Define  : 0
% 2.81/1.39  #Split   : 1
% 2.81/1.39  #Chain   : 0
% 2.81/1.39  #Close   : 0
% 2.81/1.39  
% 2.81/1.39  Ordering : KBO
% 2.81/1.39  
% 2.81/1.39  Simplification rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Subsume      : 21
% 2.81/1.39  #Demod        : 68
% 2.81/1.39  #Tautology    : 141
% 2.81/1.39  #SimpNegUnit  : 1
% 2.81/1.39  #BackRed      : 0
% 2.81/1.39  
% 2.81/1.39  #Partial instantiations: 0
% 2.81/1.39  #Strategies tried      : 1
% 2.81/1.39  
% 2.81/1.39  Timing (in seconds)
% 2.81/1.39  ----------------------
% 2.81/1.40  Preprocessing        : 0.33
% 2.81/1.40  Parsing              : 0.16
% 2.81/1.40  CNF conversion       : 0.03
% 2.81/1.40  Main loop            : 0.31
% 2.81/1.40  Inferencing          : 0.10
% 2.81/1.40  Reduction            : 0.11
% 2.81/1.40  Demodulation         : 0.09
% 2.81/1.40  BG Simplification    : 0.02
% 2.81/1.40  Subsumption          : 0.06
% 2.81/1.40  Abstraction          : 0.01
% 2.81/1.40  MUC search           : 0.00
% 2.81/1.40  Cooper               : 0.00
% 2.81/1.40  Total                : 0.66
% 2.81/1.40  Index Insertion      : 0.00
% 2.81/1.40  Index Deletion       : 0.00
% 2.81/1.40  Index Matching       : 0.00
% 2.81/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
