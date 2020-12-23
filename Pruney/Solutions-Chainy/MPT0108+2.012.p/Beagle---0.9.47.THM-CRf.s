%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:02 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_18,B_19] : k4_xboole_0(k2_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(k4_xboole_0(A_18,B_19),k4_xboole_0(B_19,A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k5_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) != k5_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_28,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:46:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.08  
% 1.59/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.08  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.08  
% 1.68/1.08  %Foreground sorts:
% 1.68/1.08  
% 1.68/1.08  
% 1.68/1.08  %Background operators:
% 1.68/1.08  
% 1.68/1.08  
% 1.68/1.08  %Foreground operators:
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.68/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.08  
% 1.68/1.08  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.68/1.08  tff(f_49, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 1.68/1.08  tff(f_64, negated_conjecture, ~(![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 1.68/1.08  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.08  tff(c_18, plain, (![A_18, B_19]: (k4_xboole_0(k2_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(k4_xboole_0(A_18, B_19), k4_xboole_0(B_19, A_18)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.08  tff(c_24, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k5_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.68/1.08  tff(c_25, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))!=k5_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 1.68/1.08  tff(c_28, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_25])).
% 1.68/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.08  
% 1.68/1.08  Inference rules
% 1.68/1.08  ----------------------
% 1.68/1.08  #Ref     : 0
% 1.68/1.08  #Sup     : 0
% 1.68/1.08  #Fact    : 0
% 1.68/1.08  #Define  : 0
% 1.68/1.08  #Split   : 0
% 1.68/1.08  #Chain   : 0
% 1.68/1.08  #Close   : 0
% 1.68/1.08  
% 1.68/1.08  Ordering : KBO
% 1.68/1.08  
% 1.68/1.08  Simplification rules
% 1.68/1.08  ----------------------
% 1.68/1.08  #Subsume      : 11
% 1.68/1.08  #Demod        : 3
% 1.68/1.08  #Tautology    : 0
% 1.68/1.08  #SimpNegUnit  : 0
% 1.68/1.09  #BackRed      : 0
% 1.68/1.09  
% 1.68/1.09  #Partial instantiations: 0
% 1.68/1.09  #Strategies tried      : 1
% 1.68/1.09  
% 1.68/1.09  Timing (in seconds)
% 1.68/1.09  ----------------------
% 1.68/1.09  Preprocessing        : 0.29
% 1.68/1.09  Parsing              : 0.16
% 1.68/1.09  CNF conversion       : 0.02
% 1.68/1.09  Main loop            : 0.04
% 1.68/1.09  Inferencing          : 0.00
% 1.68/1.09  Reduction            : 0.02
% 1.68/1.09  Demodulation         : 0.02
% 1.68/1.09  BG Simplification    : 0.01
% 1.68/1.09  Subsumption          : 0.01
% 1.68/1.09  Abstraction          : 0.01
% 1.68/1.09  MUC search           : 0.00
% 1.68/1.09  Cooper               : 0.00
% 1.68/1.09  Total                : 0.35
% 1.68/1.09  Index Insertion      : 0.00
% 1.68/1.09  Index Deletion       : 0.00
% 1.68/1.09  Index Matching       : 0.00
% 1.68/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
