%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:29 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :   40 (  40 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_106,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_321,plain,(
    ! [A_118,B_119] : k1_enumset1(A_118,A_118,B_119) = k2_tarski(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    ! [E_22,B_17,C_18] : r2_hidden(E_22,k1_enumset1(E_22,B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_330,plain,(
    ! [A_118,B_119] : r2_hidden(A_118,k2_tarski(A_118,B_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_24])).

tff(c_428,plain,(
    ! [B_130,A_131] :
      ( k3_xboole_0(B_130,k1_tarski(A_131)) = k1_tarski(A_131)
      | ~ r2_hidden(A_131,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8014,plain,(
    ! [A_13299,B_13300] :
      ( k3_xboole_0(k1_tarski(A_13299),B_13300) = k1_tarski(A_13299)
      | ~ r2_hidden(A_13299,B_13300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_2])).

tff(c_136,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k2_tarski('#skF_7','#skF_8')) != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8106,plain,(
    ~ r2_hidden('#skF_7',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8014,c_136])).

tff(c_8229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_8106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.48  
% 7.08/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.49  %$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 7.08/2.49  
% 7.08/2.49  %Foreground sorts:
% 7.08/2.49  
% 7.08/2.49  
% 7.08/2.49  %Background operators:
% 7.08/2.49  
% 7.08/2.49  
% 7.08/2.49  %Foreground operators:
% 7.08/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.08/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.08/2.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.08/2.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.08/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.08/2.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.08/2.49  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.49  tff('#skF_7', type, '#skF_7': $i).
% 7.08/2.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.08/2.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.08/2.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.08/2.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.08/2.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.08/2.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.08/2.49  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.49  tff('#skF_8', type, '#skF_8': $i).
% 7.08/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.08/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.08/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.08/2.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.08/2.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.08/2.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.08/2.49  
% 7.08/2.49  tff(f_106, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.08/2.49  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.08/2.49  tff(f_120, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 7.08/2.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.08/2.49  tff(f_123, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 7.08/2.49  tff(c_321, plain, (![A_118, B_119]: (k1_enumset1(A_118, A_118, B_119)=k2_tarski(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.08/2.49  tff(c_24, plain, (![E_22, B_17, C_18]: (r2_hidden(E_22, k1_enumset1(E_22, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.08/2.49  tff(c_330, plain, (![A_118, B_119]: (r2_hidden(A_118, k2_tarski(A_118, B_119)))), inference(superposition, [status(thm), theory('equality')], [c_321, c_24])).
% 7.08/2.49  tff(c_428, plain, (![B_130, A_131]: (k3_xboole_0(B_130, k1_tarski(A_131))=k1_tarski(A_131) | ~r2_hidden(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.08/2.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.08/2.49  tff(c_8014, plain, (![A_13299, B_13300]: (k3_xboole_0(k1_tarski(A_13299), B_13300)=k1_tarski(A_13299) | ~r2_hidden(A_13299, B_13300))), inference(superposition, [status(thm), theory('equality')], [c_428, c_2])).
% 7.08/2.49  tff(c_136, plain, (k3_xboole_0(k1_tarski('#skF_7'), k2_tarski('#skF_7', '#skF_8'))!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.08/2.49  tff(c_8106, plain, (~r2_hidden('#skF_7', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8014, c_136])).
% 7.08/2.49  tff(c_8229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_330, c_8106])).
% 7.08/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.49  
% 7.08/2.49  Inference rules
% 7.08/2.49  ----------------------
% 7.08/2.49  #Ref     : 0
% 7.08/2.49  #Sup     : 1584
% 7.08/2.49  #Fact    : 0
% 7.08/2.49  #Define  : 0
% 7.08/2.49  #Split   : 12
% 7.08/2.49  #Chain   : 0
% 7.08/2.49  #Close   : 0
% 7.08/2.49  
% 7.08/2.49  Ordering : KBO
% 7.08/2.49  
% 7.08/2.49  Simplification rules
% 7.08/2.49  ----------------------
% 7.08/2.50  #Subsume      : 141
% 7.08/2.50  #Demod        : 1280
% 7.08/2.50  #Tautology    : 1122
% 7.08/2.50  #SimpNegUnit  : 0
% 7.08/2.50  #BackRed      : 0
% 7.08/2.50  
% 7.08/2.50  #Partial instantiations: 3322
% 7.08/2.50  #Strategies tried      : 1
% 7.08/2.50  
% 7.08/2.50  Timing (in seconds)
% 7.08/2.50  ----------------------
% 7.08/2.50  Preprocessing        : 0.40
% 7.08/2.50  Parsing              : 0.19
% 7.08/2.50  CNF conversion       : 0.04
% 7.08/2.50  Main loop            : 1.27
% 7.08/2.50  Inferencing          : 0.46
% 7.08/2.50  Reduction            : 0.47
% 7.08/2.50  Demodulation         : 0.37
% 7.08/2.50  BG Simplification    : 0.05
% 7.08/2.50  Subsumption          : 0.23
% 7.08/2.50  Abstraction          : 0.07
% 7.08/2.50  MUC search           : 0.00
% 7.08/2.50  Cooper               : 0.00
% 7.08/2.50  Total                : 1.70
% 7.08/2.50  Index Insertion      : 0.00
% 7.08/2.50  Index Deletion       : 0.00
% 7.08/2.50  Index Matching       : 0.00
% 7.08/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
