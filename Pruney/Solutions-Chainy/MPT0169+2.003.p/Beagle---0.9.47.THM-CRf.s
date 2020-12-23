%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:28 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k5_enumset1(A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_enumset1)).

tff(c_4,plain,(
    ! [A_7,B_8,C_9,D_10] : k4_enumset1(A_7,A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k5_enumset1(A_1,A_1,B_2,C_3,D_4,E_5,F_6) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.04  
% 1.49/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.04  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.49/1.04  
% 1.49/1.04  %Foreground sorts:
% 1.49/1.04  
% 1.49/1.04  
% 1.49/1.04  %Background operators:
% 1.49/1.04  
% 1.49/1.04  
% 1.49/1.04  %Foreground operators:
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.49/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.04  tff('#skF_3', type, '#skF_3': $i).
% 1.49/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.04  tff('#skF_4', type, '#skF_4': $i).
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.04  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.49/1.04  
% 1.49/1.05  tff(f_29, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 1.49/1.05  tff(f_27, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.49/1.05  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k5_enumset1(A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_enumset1)).
% 1.49/1.05  tff(c_4, plain, (![A_7, B_8, C_9, D_10]: (k4_enumset1(A_7, A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.49/1.05  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k5_enumset1(A_1, A_1, B_2, C_3, D_4, E_5, F_6)=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.49/1.05  tff(c_6, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.49/1.05  tff(c_7, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.49/1.05  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_7])).
% 1.49/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  Inference rules
% 1.49/1.05  ----------------------
% 1.49/1.05  #Ref     : 0
% 1.49/1.05  #Sup     : 0
% 1.49/1.05  #Fact    : 0
% 1.49/1.05  #Define  : 0
% 1.49/1.05  #Split   : 0
% 1.49/1.05  #Chain   : 0
% 1.49/1.05  #Close   : 0
% 1.49/1.05  
% 1.49/1.05  Ordering : KBO
% 1.49/1.05  
% 1.49/1.05  Simplification rules
% 1.49/1.06  ----------------------
% 1.49/1.06  #Subsume      : 2
% 1.49/1.06  #Demod        : 2
% 1.49/1.06  #Tautology    : 0
% 1.49/1.06  #SimpNegUnit  : 0
% 1.49/1.06  #BackRed      : 0
% 1.49/1.06  
% 1.49/1.06  #Partial instantiations: 0
% 1.49/1.06  #Strategies tried      : 1
% 1.49/1.06  
% 1.49/1.06  Timing (in seconds)
% 1.49/1.06  ----------------------
% 1.49/1.06  Preprocessing        : 0.26
% 1.49/1.06  Parsing              : 0.13
% 1.49/1.06  CNF conversion       : 0.01
% 1.49/1.06  Main loop            : 0.02
% 1.49/1.06  Inferencing          : 0.00
% 1.49/1.06  Reduction            : 0.02
% 1.49/1.06  Demodulation         : 0.01
% 1.49/1.06  BG Simplification    : 0.01
% 1.49/1.06  Subsumption          : 0.00
% 1.49/1.06  Abstraction          : 0.00
% 1.49/1.06  MUC search           : 0.00
% 1.49/1.06  Cooper               : 0.00
% 1.49/1.06  Total                : 0.31
% 1.49/1.06  Index Insertion      : 0.00
% 1.49/1.06  Index Deletion       : 0.00
% 1.49/1.06  Index Matching       : 0.00
% 1.49/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
