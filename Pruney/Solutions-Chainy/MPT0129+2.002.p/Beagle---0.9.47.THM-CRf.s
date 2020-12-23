%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:38 EST 2020

% Result     : Theorem 1.34s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_30,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:00:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.34/1.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.34/1.00  
% 1.34/1.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.01  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.47/1.01  
% 1.47/1.01  %Foreground sorts:
% 1.47/1.01  
% 1.47/1.01  
% 1.47/1.01  %Background operators:
% 1.47/1.01  
% 1.47/1.01  
% 1.47/1.01  %Foreground operators:
% 1.47/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.47/1.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.47/1.01  tff('#skF_2', type, '#skF_2': $i).
% 1.47/1.01  tff('#skF_3', type, '#skF_3': $i).
% 1.47/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.47/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.01  tff('#skF_4', type, '#skF_4': $i).
% 1.47/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.47/1.01  
% 1.47/1.02  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.47/1.02  tff(f_30, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 1.47/1.02  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.47/1.02  tff(c_4, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.47/1.02  tff(c_6, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.47/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.02  
% 1.47/1.02  Inference rules
% 1.47/1.02  ----------------------
% 1.47/1.02  #Ref     : 0
% 1.47/1.02  #Sup     : 0
% 1.47/1.02  #Fact    : 0
% 1.47/1.02  #Define  : 0
% 1.47/1.02  #Split   : 0
% 1.47/1.02  #Chain   : 0
% 1.47/1.02  #Close   : 0
% 1.47/1.02  
% 1.47/1.02  Ordering : KBO
% 1.47/1.02  
% 1.47/1.02  Simplification rules
% 1.47/1.02  ----------------------
% 1.47/1.02  #Subsume      : 1
% 1.47/1.02  #Demod        : 1
% 1.47/1.02  #Tautology    : 0
% 1.47/1.02  #SimpNegUnit  : 0
% 1.47/1.02  #BackRed      : 0
% 1.47/1.02  
% 1.47/1.02  #Partial instantiations: 0
% 1.47/1.02  #Strategies tried      : 1
% 1.47/1.02  
% 1.47/1.02  Timing (in seconds)
% 1.47/1.02  ----------------------
% 1.47/1.02  Preprocessing        : 0.23
% 1.47/1.02  Parsing              : 0.12
% 1.47/1.02  CNF conversion       : 0.01
% 1.47/1.02  Main loop            : 0.02
% 1.47/1.02  Inferencing          : 0.00
% 1.47/1.02  Reduction            : 0.01
% 1.47/1.02  Demodulation         : 0.01
% 1.47/1.02  BG Simplification    : 0.01
% 1.47/1.02  Subsumption          : 0.00
% 1.47/1.02  Abstraction          : 0.00
% 1.47/1.02  MUC search           : 0.00
% 1.47/1.02  Cooper               : 0.00
% 1.47/1.02  Total                : 0.28
% 1.47/1.02  Index Insertion      : 0.00
% 1.47/1.02  Index Deletion       : 0.00
% 1.47/1.02  Index Matching       : 0.00
% 1.47/1.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
