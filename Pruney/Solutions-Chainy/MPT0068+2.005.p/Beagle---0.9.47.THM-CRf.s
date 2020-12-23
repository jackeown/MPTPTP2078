%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:16 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(c_12,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r2_xboole_0(A_14,B_15)
      | B_15 = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ~ r2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_14])).

tff(c_48,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_42])).

tff(c_51,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.08  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.62/1.08  
% 1.62/1.08  %Foreground sorts:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Background operators:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Foreground operators:
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.08  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.08  
% 1.62/1.09  tff(f_38, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.62/1.09  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.62/1.09  tff(f_44, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 1.62/1.09  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.62/1.09  tff(c_12, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.09  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.09  tff(c_16, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.09  tff(c_32, plain, (![A_14, B_15]: (r2_xboole_0(A_14, B_15) | B_15=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.09  tff(c_14, plain, (~r2_xboole_0(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.09  tff(c_42, plain, (k1_xboole_0='#skF_1' | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_32, c_14])).
% 1.62/1.09  tff(c_48, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_16, c_42])).
% 1.62/1.09  tff(c_51, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_48])).
% 1.62/1.09  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_51])).
% 1.62/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  Inference rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Ref     : 0
% 1.62/1.09  #Sup     : 7
% 1.62/1.09  #Fact    : 0
% 1.62/1.09  #Define  : 0
% 1.62/1.09  #Split   : 0
% 1.62/1.09  #Chain   : 0
% 1.62/1.09  #Close   : 0
% 1.62/1.09  
% 1.62/1.09  Ordering : KBO
% 1.62/1.09  
% 1.62/1.09  Simplification rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Subsume      : 0
% 1.62/1.09  #Demod        : 1
% 1.62/1.09  #Tautology    : 5
% 1.62/1.09  #SimpNegUnit  : 1
% 1.62/1.09  #BackRed      : 0
% 1.62/1.09  
% 1.62/1.09  #Partial instantiations: 0
% 1.62/1.09  #Strategies tried      : 1
% 1.62/1.09  
% 1.62/1.09  Timing (in seconds)
% 1.62/1.09  ----------------------
% 1.62/1.09  Preprocessing        : 0.26
% 1.62/1.09  Parsing              : 0.14
% 1.62/1.09  CNF conversion       : 0.01
% 1.62/1.09  Main loop            : 0.08
% 1.62/1.09  Inferencing          : 0.03
% 1.62/1.09  Reduction            : 0.02
% 1.62/1.09  Demodulation         : 0.01
% 1.62/1.09  BG Simplification    : 0.01
% 1.62/1.09  Subsumption          : 0.01
% 1.62/1.09  Abstraction          : 0.00
% 1.62/1.09  MUC search           : 0.00
% 1.62/1.09  Cooper               : 0.00
% 1.62/1.09  Total                : 0.35
% 1.62/1.09  Index Insertion      : 0.00
% 1.62/1.09  Index Deletion       : 0.00
% 1.62/1.09  Index Matching       : 0.00
% 1.62/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
