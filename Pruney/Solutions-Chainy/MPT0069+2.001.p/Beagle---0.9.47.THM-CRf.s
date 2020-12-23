%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:16 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   18 (  33 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  36 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
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
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_xboole_0(k1_xboole_0,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    r2_xboole_0('#skF_1',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [B_10,A_11] :
      ( ~ r2_xboole_0(B_10,A_11)
      | ~ r2_xboole_0(A_11,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_26,plain,(
    ~ r2_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_20])).

tff(c_30,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_26])).

tff(c_31,plain,(
    ~ r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_35,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_40,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:42:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.05  
% 1.48/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.05  %$ r2_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_1
% 1.48/1.05  
% 1.48/1.05  %Foreground sorts:
% 1.48/1.05  
% 1.48/1.05  
% 1.48/1.05  %Background operators:
% 1.48/1.05  
% 1.48/1.05  
% 1.48/1.05  %Foreground operators:
% 1.48/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.48/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.48/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.05  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.48/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.05  
% 1.48/1.06  tff(f_40, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 1.48/1.06  tff(f_44, negated_conjecture, ~(![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_xboole_1)).
% 1.48/1.06  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.48/1.06  tff(c_6, plain, (![A_5]: (r2_xboole_0(k1_xboole_0, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.48/1.06  tff(c_8, plain, (r2_xboole_0('#skF_1', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.48/1.06  tff(c_20, plain, (![B_10, A_11]: (~r2_xboole_0(B_10, A_11) | ~r2_xboole_0(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.48/1.06  tff(c_26, plain, (~r2_xboole_0(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_8, c_20])).
% 1.48/1.06  tff(c_30, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_26])).
% 1.48/1.06  tff(c_31, plain, (~r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26])).
% 1.48/1.06  tff(c_35, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8])).
% 1.48/1.06  tff(c_40, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_35])).
% 1.48/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.06  
% 1.48/1.06  Inference rules
% 1.48/1.06  ----------------------
% 1.48/1.06  #Ref     : 0
% 1.48/1.06  #Sup     : 7
% 1.48/1.06  #Fact    : 0
% 1.48/1.06  #Define  : 0
% 1.48/1.06  #Split   : 0
% 1.48/1.06  #Chain   : 0
% 1.48/1.06  #Close   : 0
% 1.48/1.06  
% 1.48/1.06  Ordering : KBO
% 1.48/1.06  
% 1.48/1.06  Simplification rules
% 1.48/1.06  ----------------------
% 1.48/1.06  #Subsume      : 0
% 1.48/1.06  #Demod        : 7
% 1.48/1.06  #Tautology    : 2
% 1.48/1.06  #SimpNegUnit  : 1
% 1.48/1.06  #BackRed      : 5
% 1.48/1.06  
% 1.48/1.06  #Partial instantiations: 0
% 1.48/1.06  #Strategies tried      : 1
% 1.48/1.06  
% 1.48/1.06  Timing (in seconds)
% 1.48/1.06  ----------------------
% 1.48/1.06  Preprocessing        : 0.24
% 1.48/1.06  Parsing              : 0.13
% 1.48/1.06  CNF conversion       : 0.01
% 1.48/1.06  Main loop            : 0.08
% 1.48/1.06  Inferencing          : 0.04
% 1.48/1.06  Reduction            : 0.02
% 1.48/1.06  Demodulation         : 0.01
% 1.48/1.06  BG Simplification    : 0.01
% 1.48/1.06  Subsumption          : 0.01
% 1.48/1.06  Abstraction          : 0.00
% 1.48/1.06  MUC search           : 0.00
% 1.48/1.06  Cooper               : 0.00
% 1.48/1.06  Total                : 0.34
% 1.48/1.06  Index Insertion      : 0.00
% 1.48/1.06  Index Deletion       : 0.00
% 1.48/1.06  Index Matching       : 0.00
% 1.48/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
