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
% DateTime   : Thu Dec  3 09:45:08 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_30,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,B_2),k5_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.39/1.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/1.00  
% 1.39/1.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/1.01  %$ r1_xboole_0 > k5_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.39/1.01  
% 1.39/1.01  %Foreground sorts:
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  %Background operators:
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  %Foreground operators:
% 1.39/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.39/1.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.39/1.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.39/1.01  tff('#skF_2', type, '#skF_2': $i).
% 1.39/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.39/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.39/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.39/1.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.39/1.01  
% 1.39/1.02  tff(f_27, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 1.39/1.02  tff(f_30, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_xboole_1)).
% 1.39/1.02  tff(c_2, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, B_2), k5_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.39/1.02  tff(c_4, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.39/1.02  tff(c_6, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.39/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/1.02  
% 1.39/1.02  Inference rules
% 1.39/1.02  ----------------------
% 1.39/1.02  #Ref     : 0
% 1.39/1.02  #Sup     : 0
% 1.39/1.02  #Fact    : 0
% 1.39/1.02  #Define  : 0
% 1.39/1.02  #Split   : 0
% 1.39/1.02  #Chain   : 0
% 1.39/1.02  #Close   : 0
% 1.39/1.02  
% 1.39/1.02  Ordering : KBO
% 1.39/1.02  
% 1.39/1.02  Simplification rules
% 1.39/1.02  ----------------------
% 1.39/1.02  #Subsume      : 1
% 1.39/1.02  #Demod        : 1
% 1.39/1.02  #Tautology    : 0
% 1.39/1.02  #SimpNegUnit  : 0
% 1.39/1.02  #BackRed      : 0
% 1.39/1.02  
% 1.39/1.02  #Partial instantiations: 0
% 1.39/1.02  #Strategies tried      : 1
% 1.39/1.02  
% 1.39/1.02  Timing (in seconds)
% 1.39/1.02  ----------------------
% 1.39/1.02  Preprocessing        : 0.23
% 1.39/1.02  Parsing              : 0.12
% 1.39/1.02  CNF conversion       : 0.01
% 1.39/1.02  Main loop            : 0.02
% 1.39/1.02  Inferencing          : 0.00
% 1.39/1.02  Reduction            : 0.01
% 1.39/1.02  Demodulation         : 0.01
% 1.39/1.02  BG Simplification    : 0.01
% 1.39/1.02  Subsumption          : 0.00
% 1.39/1.02  Abstraction          : 0.00
% 1.39/1.03  MUC search           : 0.00
% 1.39/1.03  Cooper               : 0.00
% 1.39/1.03  Total                : 0.28
% 1.39/1.03  Index Insertion      : 0.00
% 1.39/1.03  Index Deletion       : 0.00
% 1.39/1.03  Index Matching       : 0.00
% 1.39/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
