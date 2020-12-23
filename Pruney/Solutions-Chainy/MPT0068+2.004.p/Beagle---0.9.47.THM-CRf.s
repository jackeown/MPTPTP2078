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
% DateTime   : Thu Dec  3 09:43:16 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   11 (  12 expanded)
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
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,negated_conjecture,(
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
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [B_6] : k4_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_21])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_110,plain,(
    ! [A_24,B_25] :
      ( r2_xboole_0(A_24,B_25)
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ~ r2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_16])).

tff(c_126,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_120])).

tff(c_129,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.14  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.77/1.14  
% 1.77/1.14  %Foreground sorts:
% 1.77/1.14  
% 1.77/1.14  
% 1.77/1.14  %Background operators:
% 1.77/1.14  
% 1.77/1.14  
% 1.77/1.14  %Foreground operators:
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.14  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.14  
% 1.77/1.15  tff(f_38, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.77/1.15  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.77/1.15  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.77/1.15  tff(f_48, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 1.77/1.15  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.77/1.15  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.77/1.15  tff(c_21, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.77/1.15  tff(c_26, plain, (![B_6]: (k4_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_21])).
% 1.77/1.15  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.77/1.15  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.15  tff(c_110, plain, (![A_24, B_25]: (r2_xboole_0(A_24, B_25) | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.77/1.15  tff(c_16, plain, (~r2_xboole_0(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.15  tff(c_120, plain, (k1_xboole_0='#skF_1' | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_110, c_16])).
% 1.77/1.15  tff(c_126, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_18, c_120])).
% 1.77/1.15  tff(c_129, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_126])).
% 1.77/1.15  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_129])).
% 1.77/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  Inference rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Ref     : 0
% 1.77/1.15  #Sup     : 24
% 1.77/1.15  #Fact    : 0
% 1.77/1.15  #Define  : 0
% 1.77/1.15  #Split   : 0
% 1.77/1.15  #Chain   : 0
% 1.77/1.15  #Close   : 0
% 1.77/1.15  
% 1.77/1.15  Ordering : KBO
% 1.77/1.15  
% 1.77/1.15  Simplification rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Subsume      : 0
% 1.77/1.15  #Demod        : 9
% 1.77/1.15  #Tautology    : 17
% 1.77/1.15  #SimpNegUnit  : 1
% 1.77/1.15  #BackRed      : 0
% 1.77/1.15  
% 1.77/1.15  #Partial instantiations: 0
% 1.77/1.15  #Strategies tried      : 1
% 1.77/1.15  
% 1.77/1.15  Timing (in seconds)
% 1.77/1.15  ----------------------
% 1.77/1.16  Preprocessing        : 0.30
% 1.77/1.16  Parsing              : 0.15
% 1.77/1.16  CNF conversion       : 0.02
% 1.77/1.16  Main loop            : 0.11
% 1.77/1.16  Inferencing          : 0.05
% 1.77/1.16  Reduction            : 0.03
% 1.77/1.16  Demodulation         : 0.02
% 1.77/1.16  BG Simplification    : 0.01
% 1.77/1.16  Subsumption          : 0.02
% 1.77/1.16  Abstraction          : 0.01
% 1.77/1.16  MUC search           : 0.00
% 1.77/1.16  Cooper               : 0.00
% 1.77/1.16  Total                : 0.43
% 1.77/1.16  Index Insertion      : 0.00
% 1.77/1.16  Index Deletion       : 0.00
% 1.77/1.16  Index Matching       : 0.00
% 1.77/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
