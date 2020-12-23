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
% DateTime   : Thu Dec  3 09:48:01 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,(
    ! [A_48,B_49,C_50] : k2_xboole_0(k1_tarski(A_48),k2_tarski(B_49,C_50)) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_375,plain,(
    ! [A_540,A_541] : k2_xboole_0(k1_tarski(A_540),k1_tarski(A_541)) = k1_enumset1(A_540,A_541,A_541) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_121])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_388,plain,(
    k1_enumset1('#skF_5','#skF_6','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_50])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_488,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_6])).

tff(c_28,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_515,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_488,c_28])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.36  
% 2.25/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.36  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.25/1.36  
% 2.25/1.36  %Foreground sorts:
% 2.25/1.36  
% 2.25/1.36  
% 2.25/1.36  %Background operators:
% 2.25/1.36  
% 2.25/1.36  
% 2.25/1.36  %Foreground operators:
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.25/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.25/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.25/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.25/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.25/1.36  
% 2.25/1.37  tff(f_62, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.25/1.37  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.25/1.37  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.25/1.37  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.25/1.37  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.25/1.37  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.25/1.37  tff(c_42, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.25/1.37  tff(c_121, plain, (![A_48, B_49, C_50]: (k2_xboole_0(k1_tarski(A_48), k2_tarski(B_49, C_50))=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.25/1.37  tff(c_375, plain, (![A_540, A_541]: (k2_xboole_0(k1_tarski(A_540), k1_tarski(A_541))=k1_enumset1(A_540, A_541, A_541))), inference(superposition, [status(thm), theory('equality')], [c_42, c_121])).
% 2.25/1.37  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.25/1.37  tff(c_388, plain, (k1_enumset1('#skF_5', '#skF_6', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_375, c_50])).
% 2.25/1.37  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.37  tff(c_488, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_388, c_6])).
% 2.25/1.37  tff(c_28, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.37  tff(c_515, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_488, c_28])).
% 2.25/1.37  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_515])).
% 2.25/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.37  
% 2.25/1.37  Inference rules
% 2.25/1.37  ----------------------
% 2.25/1.37  #Ref     : 0
% 2.25/1.37  #Sup     : 57
% 2.25/1.37  #Fact    : 0
% 2.25/1.37  #Define  : 0
% 2.25/1.37  #Split   : 0
% 2.25/1.37  #Chain   : 0
% 2.25/1.37  #Close   : 0
% 2.25/1.37  
% 2.25/1.37  Ordering : KBO
% 2.25/1.37  
% 2.25/1.37  Simplification rules
% 2.25/1.37  ----------------------
% 2.25/1.37  #Subsume      : 0
% 2.25/1.37  #Demod        : 6
% 2.25/1.37  #Tautology    : 25
% 2.25/1.37  #SimpNegUnit  : 1
% 2.25/1.37  #BackRed      : 0
% 2.25/1.37  
% 2.25/1.37  #Partial instantiations: 247
% 2.25/1.37  #Strategies tried      : 1
% 2.25/1.37  
% 2.25/1.37  Timing (in seconds)
% 2.25/1.37  ----------------------
% 2.25/1.38  Preprocessing        : 0.29
% 2.25/1.38  Parsing              : 0.14
% 2.25/1.38  CNF conversion       : 0.02
% 2.25/1.38  Main loop            : 0.25
% 2.25/1.38  Inferencing          : 0.14
% 2.25/1.38  Reduction            : 0.06
% 2.25/1.38  Demodulation         : 0.05
% 2.25/1.38  BG Simplification    : 0.02
% 2.25/1.38  Subsumption          : 0.03
% 2.25/1.38  Abstraction          : 0.01
% 2.25/1.38  MUC search           : 0.00
% 2.25/1.38  Cooper               : 0.00
% 2.25/1.38  Total                : 0.57
% 2.25/1.38  Index Insertion      : 0.00
% 2.25/1.38  Index Deletion       : 0.00
% 2.25/1.38  Index Matching       : 0.00
% 2.25/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
