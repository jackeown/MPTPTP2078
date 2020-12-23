%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:16 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    6 (   7 expanded)
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

tff(f_40,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_xboole_0(A_8,B_9)
      | B_9 = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ~ r2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_10])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_34,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.23  
% 1.79/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.23  %$ r2_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_1
% 1.79/1.23  
% 1.79/1.23  %Foreground sorts:
% 1.79/1.23  
% 1.79/1.23  
% 1.79/1.23  %Background operators:
% 1.79/1.23  
% 1.79/1.23  
% 1.79/1.23  %Foreground operators:
% 1.79/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.23  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.79/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.23  
% 1.79/1.24  tff(f_40, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 1.79/1.24  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.79/1.24  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.79/1.24  tff(c_12, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.24  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.79/1.24  tff(c_16, plain, (![A_8, B_9]: (r2_xboole_0(A_8, B_9) | B_9=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.24  tff(c_10, plain, (~r2_xboole_0(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.24  tff(c_26, plain, (k1_xboole_0='#skF_1' | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_16, c_10])).
% 1.79/1.24  tff(c_32, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26])).
% 1.79/1.24  tff(c_34, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_32])).
% 1.79/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.24  
% 1.79/1.24  Inference rules
% 1.79/1.24  ----------------------
% 1.79/1.24  #Ref     : 0
% 1.79/1.24  #Sup     : 3
% 1.79/1.24  #Fact    : 0
% 1.79/1.24  #Define  : 0
% 1.79/1.24  #Split   : 0
% 1.79/1.24  #Chain   : 0
% 1.79/1.24  #Close   : 0
% 1.79/1.24  
% 1.79/1.24  Ordering : KBO
% 1.79/1.24  
% 1.79/1.24  Simplification rules
% 1.79/1.24  ----------------------
% 1.79/1.24  #Subsume      : 0
% 1.79/1.24  #Demod        : 1
% 1.79/1.24  #Tautology    : 2
% 1.79/1.24  #SimpNegUnit  : 1
% 1.79/1.24  #BackRed      : 0
% 1.79/1.24  
% 1.79/1.24  #Partial instantiations: 0
% 1.79/1.24  #Strategies tried      : 1
% 1.79/1.24  
% 1.79/1.24  Timing (in seconds)
% 1.79/1.24  ----------------------
% 1.79/1.24  Preprocessing        : 0.31
% 1.79/1.24  Parsing              : 0.17
% 1.79/1.24  CNF conversion       : 0.02
% 1.79/1.24  Main loop            : 0.07
% 1.79/1.24  Inferencing          : 0.03
% 1.79/1.24  Reduction            : 0.02
% 1.79/1.24  Demodulation         : 0.01
% 1.79/1.24  BG Simplification    : 0.01
% 1.79/1.24  Subsumption          : 0.01
% 1.79/1.24  Abstraction          : 0.00
% 1.79/1.24  MUC search           : 0.00
% 1.79/1.24  Cooper               : 0.00
% 1.79/1.24  Total                : 0.41
% 1.79/1.24  Index Insertion      : 0.00
% 1.79/1.24  Index Deletion       : 0.00
% 1.79/1.24  Index Matching       : 0.00
% 1.79/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
