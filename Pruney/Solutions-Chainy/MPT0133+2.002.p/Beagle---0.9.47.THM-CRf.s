%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:42 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_30,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k2_tarski(D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.06  
% 1.54/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.07  %$ k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.54/1.07  
% 1.54/1.07  %Foreground sorts:
% 1.54/1.07  
% 1.54/1.07  
% 1.54/1.07  %Background operators:
% 1.54/1.07  
% 1.54/1.07  
% 1.54/1.07  %Foreground operators:
% 1.54/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.54/1.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.54/1.07  tff('#skF_5', type, '#skF_5': $i).
% 1.54/1.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.54/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.54/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.07  tff('#skF_4', type, '#skF_4': $i).
% 1.54/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.54/1.07  
% 1.54/1.08  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 1.54/1.08  tff(f_30, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_enumset1)).
% 1.54/1.08  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k1_enumset1(A_1, B_2, C_3), k2_tarski(D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.08  tff(c_4, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.54/1.08  tff(c_6, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.54/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.08  
% 1.54/1.08  Inference rules
% 1.54/1.08  ----------------------
% 1.54/1.08  #Ref     : 0
% 1.54/1.08  #Sup     : 0
% 1.54/1.08  #Fact    : 0
% 1.54/1.08  #Define  : 0
% 1.54/1.08  #Split   : 0
% 1.54/1.08  #Chain   : 0
% 1.54/1.08  #Close   : 0
% 1.54/1.08  
% 1.54/1.08  Ordering : KBO
% 1.54/1.08  
% 1.54/1.08  Simplification rules
% 1.54/1.08  ----------------------
% 1.54/1.08  #Subsume      : 1
% 1.54/1.08  #Demod        : 1
% 1.54/1.08  #Tautology    : 0
% 1.54/1.08  #SimpNegUnit  : 0
% 1.54/1.08  #BackRed      : 0
% 1.54/1.08  
% 1.54/1.08  #Partial instantiations: 0
% 1.54/1.08  #Strategies tried      : 1
% 1.54/1.08  
% 1.54/1.08  Timing (in seconds)
% 1.54/1.08  ----------------------
% 1.54/1.08  Preprocessing        : 0.25
% 1.54/1.08  Parsing              : 0.14
% 1.54/1.08  CNF conversion       : 0.01
% 1.54/1.08  Main loop            : 0.02
% 1.54/1.08  Inferencing          : 0.00
% 1.54/1.08  Reduction            : 0.01
% 1.54/1.08  Demodulation         : 0.01
% 1.54/1.08  BG Simplification    : 0.01
% 1.54/1.08  Subsumption          : 0.00
% 1.54/1.08  Abstraction          : 0.00
% 1.54/1.08  MUC search           : 0.00
% 1.54/1.09  Cooper               : 0.00
% 1.59/1.09  Total                : 0.30
% 1.59/1.09  Index Insertion      : 0.00
% 1.59/1.09  Index Deletion       : 0.00
% 1.59/1.09  Index Matching       : 0.00
% 1.59/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
