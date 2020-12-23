%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:58 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_30,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,H_8,E_5,D_4,G_7,F_6] : k2_xboole_0(k2_enumset1(A_1,B_2,C_3,D_4),k2_enumset1(E_5,F_6,G_7,H_8)) = k6_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7,H_8) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_enumset1('#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.44/1.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.01  
% 1.44/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.02  %$ k6_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 1.44/1.02  
% 1.44/1.02  %Foreground sorts:
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  %Background operators:
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  %Foreground operators:
% 1.44/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.44/1.02  tff('#skF_7', type, '#skF_7': $i).
% 1.44/1.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.44/1.02  tff('#skF_5', type, '#skF_5': $i).
% 1.44/1.02  tff('#skF_6', type, '#skF_6': $i).
% 1.44/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.44/1.02  tff('#skF_3', type, '#skF_3': $i).
% 1.44/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.44/1.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.44/1.02  tff('#skF_8', type, '#skF_8': $i).
% 1.44/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.44/1.02  tff('#skF_4', type, '#skF_4': $i).
% 1.44/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.44/1.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.44/1.02  
% 1.44/1.03  tff(f_27, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 1.44/1.03  tff(f_30, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_enumset1)).
% 1.44/1.03  tff(c_2, plain, (![B_2, C_3, A_1, H_8, E_5, D_4, G_7, F_6]: (k2_xboole_0(k2_enumset1(A_1, B_2, C_3, D_4), k2_enumset1(E_5, F_6, G_7, H_8))=k6_enumset1(A_1, B_2, C_3, D_4, E_5, F_6, G_7, H_8))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.44/1.03  tff(c_4, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.44/1.03  tff(c_6, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.44/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.03  
% 1.44/1.03  Inference rules
% 1.44/1.03  ----------------------
% 1.44/1.03  #Ref     : 0
% 1.44/1.03  #Sup     : 0
% 1.44/1.03  #Fact    : 0
% 1.44/1.03  #Define  : 0
% 1.44/1.03  #Split   : 0
% 1.44/1.03  #Chain   : 0
% 1.44/1.03  #Close   : 0
% 1.44/1.03  
% 1.44/1.03  Ordering : KBO
% 1.44/1.03  
% 1.44/1.03  Simplification rules
% 1.44/1.03  ----------------------
% 1.44/1.03  #Subsume      : 1
% 1.44/1.03  #Demod        : 1
% 1.44/1.03  #Tautology    : 0
% 1.44/1.03  #SimpNegUnit  : 0
% 1.44/1.03  #BackRed      : 0
% 1.44/1.03  
% 1.44/1.03  #Partial instantiations: 0
% 1.44/1.03  #Strategies tried      : 1
% 1.44/1.03  
% 1.44/1.03  Timing (in seconds)
% 1.44/1.03  ----------------------
% 1.44/1.03  Preprocessing        : 0.23
% 1.44/1.03  Parsing              : 0.12
% 1.44/1.03  CNF conversion       : 0.01
% 1.44/1.03  Main loop            : 0.02
% 1.44/1.03  Inferencing          : 0.00
% 1.44/1.03  Reduction            : 0.01
% 1.44/1.03  Demodulation         : 0.01
% 1.44/1.03  BG Simplification    : 0.01
% 1.44/1.03  Subsumption          : 0.00
% 1.44/1.03  Abstraction          : 0.00
% 1.44/1.03  MUC search           : 0.00
% 1.44/1.03  Cooper               : 0.00
% 1.44/1.03  Total                : 0.28
% 1.44/1.04  Index Insertion      : 0.00
% 1.44/1.04  Index Deletion       : 0.00
% 1.44/1.04  Index Matching       : 0.00
% 1.44/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
