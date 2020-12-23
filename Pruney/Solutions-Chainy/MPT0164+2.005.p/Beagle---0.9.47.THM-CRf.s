%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:25 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k4_enumset1(A_1,A_1,B_2,C_3,D_4,E_5) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_7,D_9,C_8,F_11,E_10,A_6] : k5_enumset1(A_6,A_6,B_7,C_8,D_9,E_10,F_11) = k4_enumset1(A_6,B_7,C_8,D_9,E_10,F_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:10:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.62/1.11  
% 1.62/1.11  %Foreground sorts:
% 1.62/1.11  
% 1.62/1.11  
% 1.62/1.11  %Background operators:
% 1.62/1.11  
% 1.62/1.11  
% 1.62/1.11  %Foreground operators:
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.62/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.62/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.62/1.11  
% 1.67/1.12  tff(f_27, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.67/1.12  tff(f_29, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.67/1.12  tff(f_32, negated_conjecture, ~(![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 1.67/1.12  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k4_enumset1(A_1, A_1, B_2, C_3, D_4, E_5)=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.12  tff(c_4, plain, (![B_7, D_9, C_8, F_11, E_10, A_6]: (k5_enumset1(A_6, A_6, B_7, C_8, D_9, E_10, F_11)=k4_enumset1(A_6, B_7, C_8, D_9, E_10, F_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.12  tff(c_6, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.67/1.12  tff(c_7, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.67/1.12  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.67/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  Inference rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Ref     : 0
% 1.67/1.12  #Sup     : 0
% 1.67/1.12  #Fact    : 0
% 1.67/1.12  #Define  : 0
% 1.67/1.12  #Split   : 0
% 1.67/1.12  #Chain   : 0
% 1.67/1.12  #Close   : 0
% 1.67/1.12  
% 1.67/1.12  Ordering : KBO
% 1.67/1.12  
% 1.67/1.12  Simplification rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Subsume      : 2
% 1.67/1.12  #Demod        : 2
% 1.67/1.12  #Tautology    : 0
% 1.67/1.12  #SimpNegUnit  : 0
% 1.67/1.12  #BackRed      : 0
% 1.67/1.12  
% 1.67/1.12  #Partial instantiations: 0
% 1.67/1.12  #Strategies tried      : 1
% 1.67/1.12  
% 1.67/1.12  Timing (in seconds)
% 1.67/1.12  ----------------------
% 1.67/1.13  Preprocessing        : 0.32
% 1.67/1.13  Parsing              : 0.18
% 1.67/1.13  CNF conversion       : 0.02
% 1.67/1.13  Main loop            : 0.03
% 1.67/1.13  Inferencing          : 0.00
% 1.67/1.13  Reduction            : 0.02
% 1.67/1.13  Demodulation         : 0.02
% 1.67/1.13  BG Simplification    : 0.01
% 1.67/1.13  Subsumption          : 0.01
% 1.67/1.13  Abstraction          : 0.00
% 1.67/1.13  MUC search           : 0.00
% 1.67/1.13  Cooper               : 0.00
% 1.67/1.13  Total                : 0.38
% 1.67/1.13  Index Insertion      : 0.00
% 1.67/1.13  Index Deletion       : 0.00
% 1.67/1.13  Index Matching       : 0.00
% 1.67/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
