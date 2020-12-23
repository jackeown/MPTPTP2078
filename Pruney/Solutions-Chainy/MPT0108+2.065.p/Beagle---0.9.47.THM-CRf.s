%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:07 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_30,negated_conjecture,(
    ~ ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k5_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.08  
% 1.48/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.09  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.56/1.09  
% 1.56/1.09  %Foreground sorts:
% 1.56/1.09  
% 1.56/1.09  
% 1.56/1.09  %Background operators:
% 1.56/1.09  
% 1.56/1.09  
% 1.56/1.09  %Foreground operators:
% 1.56/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.56/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.56/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.56/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.09  
% 1.56/1.10  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 1.56/1.10  tff(f_30, negated_conjecture, ~(![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 1.56/1.10  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.56/1.10  tff(c_4, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k5_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.56/1.10  tff(c_6, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.56/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.10  
% 1.56/1.10  Inference rules
% 1.56/1.10  ----------------------
% 1.56/1.10  #Ref     : 0
% 1.56/1.10  #Sup     : 0
% 1.56/1.10  #Fact    : 0
% 1.56/1.10  #Define  : 0
% 1.56/1.10  #Split   : 0
% 1.56/1.10  #Chain   : 0
% 1.56/1.10  #Close   : 0
% 1.56/1.10  
% 1.56/1.10  Ordering : KBO
% 1.56/1.10  
% 1.56/1.10  Simplification rules
% 1.56/1.10  ----------------------
% 1.56/1.10  #Subsume      : 1
% 1.56/1.10  #Demod        : 1
% 1.56/1.10  #Tautology    : 0
% 1.56/1.10  #SimpNegUnit  : 0
% 1.56/1.10  #BackRed      : 0
% 1.56/1.10  
% 1.56/1.10  #Partial instantiations: 0
% 1.56/1.10  #Strategies tried      : 1
% 1.56/1.10  
% 1.56/1.10  Timing (in seconds)
% 1.56/1.10  ----------------------
% 1.56/1.11  Preprocessing        : 0.24
% 1.56/1.11  Parsing              : 0.14
% 1.56/1.11  CNF conversion       : 0.01
% 1.56/1.11  Main loop            : 0.02
% 1.56/1.11  Inferencing          : 0.00
% 1.56/1.11  Reduction            : 0.01
% 1.56/1.11  Demodulation         : 0.01
% 1.56/1.11  BG Simplification    : 0.01
% 1.56/1.11  Subsumption          : 0.00
% 1.56/1.11  Abstraction          : 0.00
% 1.56/1.11  MUC search           : 0.00
% 1.56/1.11  Cooper               : 0.00
% 1.56/1.11  Total                : 0.29
% 1.56/1.11  Index Insertion      : 0.00
% 1.56/1.11  Index Deletion       : 0.00
% 1.56/1.11  Index Matching       : 0.00
% 1.56/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
