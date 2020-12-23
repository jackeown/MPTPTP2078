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
% DateTime   : Thu Dec  3 09:43:17 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r2_xboole_0(A_14,B_15)
      | B_15 = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    r2_xboole_0('#skF_1',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [B_12,A_13] :
      ( ~ r2_xboole_0(B_12,A_13)
      | ~ r2_xboole_0(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_25,plain,(
    ~ r2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_22])).

tff(c_29,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_25])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_49,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_14])).

tff(c_51,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:27:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.10  
% 1.56/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.10  %$ r2_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_1
% 1.56/1.10  
% 1.56/1.10  %Foreground sorts:
% 1.56/1.10  
% 1.56/1.10  
% 1.56/1.10  %Background operators:
% 1.56/1.10  
% 1.56/1.10  
% 1.56/1.10  %Foreground operators:
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.10  
% 1.56/1.11  tff(f_40, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.56/1.11  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.56/1.11  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.56/1.11  tff(f_46, negated_conjecture, ~(![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_xboole_1)).
% 1.56/1.11  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.56/1.11  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.11  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.56/1.11  tff(c_26, plain, (![A_14, B_15]: (r2_xboole_0(A_14, B_15) | B_15=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.56/1.11  tff(c_14, plain, (r2_xboole_0('#skF_1', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.56/1.11  tff(c_22, plain, (![B_12, A_13]: (~r2_xboole_0(B_12, A_13) | ~r2_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.56/1.11  tff(c_25, plain, (~r2_xboole_0(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_14, c_22])).
% 1.56/1.11  tff(c_29, plain, (k1_xboole_0='#skF_1' | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_26, c_25])).
% 1.56/1.11  tff(c_41, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_29])).
% 1.56/1.11  tff(c_49, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_14])).
% 1.56/1.11  tff(c_51, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_49])).
% 1.56/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.11  
% 1.56/1.11  Inference rules
% 1.56/1.11  ----------------------
% 1.56/1.11  #Ref     : 0
% 1.56/1.11  #Sup     : 6
% 1.56/1.11  #Fact    : 0
% 1.56/1.11  #Define  : 0
% 1.56/1.11  #Split   : 0
% 1.56/1.11  #Chain   : 0
% 1.56/1.11  #Close   : 0
% 1.56/1.11  
% 1.56/1.11  Ordering : KBO
% 1.56/1.11  
% 1.56/1.11  Simplification rules
% 1.56/1.11  ----------------------
% 1.56/1.11  #Subsume      : 2
% 1.56/1.11  #Demod        : 5
% 1.56/1.11  #Tautology    : 2
% 1.56/1.11  #SimpNegUnit  : 1
% 1.56/1.11  #BackRed      : 4
% 1.56/1.11  
% 1.56/1.11  #Partial instantiations: 0
% 1.56/1.11  #Strategies tried      : 1
% 1.56/1.11  
% 1.56/1.11  Timing (in seconds)
% 1.56/1.11  ----------------------
% 1.56/1.12  Preprocessing        : 0.24
% 1.56/1.12  Parsing              : 0.13
% 1.56/1.12  CNF conversion       : 0.01
% 1.56/1.12  Main loop            : 0.09
% 1.56/1.12  Inferencing          : 0.04
% 1.56/1.12  Reduction            : 0.02
% 1.56/1.12  Demodulation         : 0.02
% 1.56/1.12  BG Simplification    : 0.01
% 1.56/1.12  Subsumption          : 0.01
% 1.56/1.12  Abstraction          : 0.00
% 1.56/1.12  MUC search           : 0.00
% 1.56/1.12  Cooper               : 0.00
% 1.56/1.12  Total                : 0.34
% 1.56/1.12  Index Insertion      : 0.00
% 1.56/1.12  Index Deletion       : 0.00
% 1.56/1.12  Index Matching       : 0.00
% 1.56/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
