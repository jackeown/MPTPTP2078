%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:50 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
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

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_95,axiom,(
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

tff(c_104,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_162,plain,(
    ! [B_63,A_64] : k2_xboole_0(B_63,A_64) = k2_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_310,plain,(
    ! [A_69,B_70] : r1_tarski(A_69,k2_xboole_0(B_70,A_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_56])).

tff(c_316,plain,(
    r1_tarski(k1_tarski('#skF_9'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_310])).

tff(c_86,plain,(
    ! [C_43] : r2_hidden(C_43,k1_tarski(C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1047,plain,(
    ! [C_125,B_126,A_127] :
      ( r2_hidden(C_125,B_126)
      | ~ r2_hidden(C_125,A_127)
      | ~ r1_tarski(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1069,plain,(
    ! [C_128,B_129] :
      ( r2_hidden(C_128,B_129)
      | ~ r1_tarski(k1_tarski(C_128),B_129) ) ),
    inference(resolution,[status(thm)],[c_86,c_1047])).

tff(c_1085,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_316,c_1069])).

tff(c_84,plain,(
    ! [C_43,A_39] :
      ( C_43 = A_39
      | ~ r2_hidden(C_43,k1_tarski(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1094,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1085,c_84])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.50  
% 3.23/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.50  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_1
% 3.23/1.50  
% 3.23/1.50  %Foreground sorts:
% 3.23/1.50  
% 3.23/1.50  
% 3.23/1.50  %Background operators:
% 3.23/1.50  
% 3.23/1.50  
% 3.23/1.50  %Foreground operators:
% 3.23/1.50  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.23/1.50  tff('#skF_9', type, '#skF_9': $i).
% 3.23/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.23/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.23/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.50  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.23/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.50  
% 3.23/1.51  tff(f_108, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.23/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.23/1.51  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.23/1.51  tff(f_95, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.23/1.51  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.51  tff(c_104, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.23/1.51  tff(c_106, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.23/1.51  tff(c_162, plain, (![B_63, A_64]: (k2_xboole_0(B_63, A_64)=k2_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.51  tff(c_56, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.51  tff(c_310, plain, (![A_69, B_70]: (r1_tarski(A_69, k2_xboole_0(B_70, A_69)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_56])).
% 3.23/1.51  tff(c_316, plain, (r1_tarski(k1_tarski('#skF_9'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_310])).
% 3.23/1.51  tff(c_86, plain, (![C_43]: (r2_hidden(C_43, k1_tarski(C_43)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.23/1.51  tff(c_1047, plain, (![C_125, B_126, A_127]: (r2_hidden(C_125, B_126) | ~r2_hidden(C_125, A_127) | ~r1_tarski(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.51  tff(c_1069, plain, (![C_128, B_129]: (r2_hidden(C_128, B_129) | ~r1_tarski(k1_tarski(C_128), B_129))), inference(resolution, [status(thm)], [c_86, c_1047])).
% 3.23/1.51  tff(c_1085, plain, (r2_hidden('#skF_9', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_316, c_1069])).
% 3.23/1.51  tff(c_84, plain, (![C_43, A_39]: (C_43=A_39 | ~r2_hidden(C_43, k1_tarski(A_39)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.23/1.51  tff(c_1094, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_1085, c_84])).
% 3.23/1.51  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_1094])).
% 3.23/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  Inference rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Ref     : 0
% 3.23/1.51  #Sup     : 253
% 3.23/1.51  #Fact    : 0
% 3.23/1.51  #Define  : 0
% 3.23/1.51  #Split   : 1
% 3.23/1.51  #Chain   : 0
% 3.23/1.51  #Close   : 0
% 3.23/1.51  
% 3.23/1.51  Ordering : KBO
% 3.23/1.51  
% 3.23/1.51  Simplification rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Subsume      : 33
% 3.23/1.51  #Demod        : 85
% 3.23/1.51  #Tautology    : 164
% 3.23/1.51  #SimpNegUnit  : 1
% 3.23/1.51  #BackRed      : 0
% 3.23/1.51  
% 3.23/1.51  #Partial instantiations: 0
% 3.23/1.51  #Strategies tried      : 1
% 3.23/1.51  
% 3.23/1.51  Timing (in seconds)
% 3.23/1.51  ----------------------
% 3.23/1.52  Preprocessing        : 0.35
% 3.23/1.52  Parsing              : 0.17
% 3.23/1.52  CNF conversion       : 0.03
% 3.23/1.52  Main loop            : 0.39
% 3.23/1.52  Inferencing          : 0.13
% 3.23/1.52  Reduction            : 0.14
% 3.23/1.52  Demodulation         : 0.11
% 3.23/1.52  BG Simplification    : 0.03
% 3.23/1.52  Subsumption          : 0.07
% 3.23/1.52  Abstraction          : 0.02
% 3.23/1.52  MUC search           : 0.00
% 3.23/1.52  Cooper               : 0.00
% 3.23/1.52  Total                : 0.76
% 3.23/1.52  Index Insertion      : 0.00
% 3.23/1.52  Index Deletion       : 0.00
% 3.23/1.52  Index Matching       : 0.00
% 3.23/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
