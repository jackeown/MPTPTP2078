%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:17 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   18 (  20 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_33,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_4,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_xboole_0(k1_xboole_0,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    r2_xboole_0('#skF_1',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    ! [B_8,A_9] :
      ( ~ r2_xboole_0(B_8,A_9)
      | ~ r2_xboole_0(A_9,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23,plain,(
    ~ r2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_17])).

tff(c_27,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_42,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_8])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.07  
% 1.56/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.07  %$ r2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.56/1.07  
% 1.56/1.07  %Foreground sorts:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Background operators:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Foreground operators:
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.07  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.07  
% 1.61/1.08  tff(f_33, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.61/1.08  tff(f_38, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 1.61/1.08  tff(f_42, negated_conjecture, ~(![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_xboole_1)).
% 1.61/1.08  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.61/1.08  tff(c_4, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.08  tff(c_6, plain, (![A_5]: (r2_xboole_0(k1_xboole_0, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.61/1.08  tff(c_8, plain, (r2_xboole_0('#skF_1', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.08  tff(c_17, plain, (![B_8, A_9]: (~r2_xboole_0(B_8, A_9) | ~r2_xboole_0(A_9, B_8))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.61/1.08  tff(c_23, plain, (~r2_xboole_0(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_8, c_17])).
% 1.61/1.08  tff(c_27, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_23])).
% 1.61/1.08  tff(c_42, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27, c_8])).
% 1.61/1.08  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_42])).
% 1.61/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.08  
% 1.61/1.08  Inference rules
% 1.61/1.08  ----------------------
% 1.61/1.08  #Ref     : 0
% 1.61/1.08  #Sup     : 6
% 1.61/1.08  #Fact    : 0
% 1.61/1.08  #Define  : 0
% 1.61/1.08  #Split   : 0
% 1.61/1.08  #Chain   : 0
% 1.61/1.08  #Close   : 0
% 1.61/1.08  
% 1.61/1.08  Ordering : KBO
% 1.61/1.08  
% 1.61/1.08  Simplification rules
% 1.61/1.08  ----------------------
% 1.61/1.08  #Subsume      : 1
% 1.61/1.08  #Demod        : 6
% 1.61/1.08  #Tautology    : 2
% 1.61/1.08  #SimpNegUnit  : 1
% 1.61/1.08  #BackRed      : 4
% 1.61/1.08  
% 1.61/1.08  #Partial instantiations: 0
% 1.61/1.08  #Strategies tried      : 1
% 1.61/1.08  
% 1.61/1.08  Timing (in seconds)
% 1.61/1.08  ----------------------
% 1.61/1.08  Preprocessing        : 0.24
% 1.61/1.08  Parsing              : 0.13
% 1.61/1.08  CNF conversion       : 0.01
% 1.61/1.08  Main loop            : 0.08
% 1.61/1.08  Inferencing          : 0.04
% 1.61/1.08  Reduction            : 0.02
% 1.61/1.08  Demodulation         : 0.02
% 1.61/1.08  BG Simplification    : 0.01
% 1.61/1.08  Subsumption          : 0.01
% 1.61/1.09  Abstraction          : 0.00
% 1.61/1.09  MUC search           : 0.00
% 1.61/1.09  Cooper               : 0.00
% 1.61/1.09  Total                : 0.34
% 1.61/1.09  Index Insertion      : 0.00
% 1.61/1.09  Index Deletion       : 0.00
% 1.61/1.09  Index Matching       : 0.00
% 1.61/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
