%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:29 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k6_enumset1(A,A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).

tff(c_4,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] : k5_enumset1(A_8,A_8,A_8,B_9,C_10,D_11,E_12) = k3_enumset1(A_8,B_9,C_10,D_11,E_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,G_7,F_6] : k6_enumset1(A_1,A_1,B_2,C_3,D_4,E_5,F_6,G_7) = k5_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.05  
% 1.52/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.05  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.52/1.05  
% 1.52/1.05  %Foreground sorts:
% 1.52/1.05  
% 1.52/1.05  
% 1.52/1.05  %Background operators:
% 1.52/1.05  
% 1.52/1.05  
% 1.52/1.05  %Foreground operators:
% 1.52/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.52/1.05  tff('#skF_5', type, '#skF_5': $i).
% 1.52/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.52/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.05  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.52/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.05  tff('#skF_4', type, '#skF_4': $i).
% 1.52/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.05  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.52/1.05  
% 1.52/1.06  tff(f_29, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 1.52/1.06  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.52/1.06  tff(f_32, negated_conjecture, ~(![A, B, C, D, E]: (k6_enumset1(A, A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_enumset1)).
% 1.52/1.06  tff(c_4, plain, (![E_12, D_11, A_8, C_10, B_9]: (k5_enumset1(A_8, A_8, A_8, B_9, C_10, D_11, E_12)=k3_enumset1(A_8, B_9, C_10, D_11, E_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.06  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, G_7, F_6]: (k6_enumset1(A_1, A_1, B_2, C_3, D_4, E_5, F_6, G_7)=k5_enumset1(A_1, B_2, C_3, D_4, E_5, F_6, G_7))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.52/1.06  tff(c_6, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.52/1.06  tff(c_7, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.52/1.06  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_7])).
% 1.52/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  Inference rules
% 1.52/1.06  ----------------------
% 1.52/1.06  #Ref     : 0
% 1.52/1.06  #Sup     : 0
% 1.52/1.06  #Fact    : 0
% 1.52/1.06  #Define  : 0
% 1.52/1.06  #Split   : 0
% 1.52/1.06  #Chain   : 0
% 1.52/1.06  #Close   : 0
% 1.52/1.06  
% 1.52/1.06  Ordering : KBO
% 1.52/1.06  
% 1.52/1.06  Simplification rules
% 1.52/1.06  ----------------------
% 1.52/1.06  #Subsume      : 2
% 1.52/1.06  #Demod        : 2
% 1.52/1.06  #Tautology    : 0
% 1.52/1.06  #SimpNegUnit  : 0
% 1.52/1.06  #BackRed      : 0
% 1.52/1.06  
% 1.52/1.06  #Partial instantiations: 0
% 1.52/1.06  #Strategies tried      : 1
% 1.52/1.06  
% 1.52/1.06  Timing (in seconds)
% 1.52/1.06  ----------------------
% 1.52/1.07  Preprocessing        : 0.25
% 1.52/1.07  Parsing              : 0.13
% 1.52/1.07  CNF conversion       : 0.01
% 1.52/1.07  Main loop            : 0.02
% 1.52/1.07  Inferencing          : 0.00
% 1.52/1.07  Reduction            : 0.01
% 1.52/1.07  Demodulation         : 0.01
% 1.52/1.07  BG Simplification    : 0.01
% 1.52/1.07  Subsumption          : 0.00
% 1.52/1.07  Abstraction          : 0.00
% 1.52/1.07  MUC search           : 0.00
% 1.52/1.07  Cooper               : 0.00
% 1.52/1.07  Total                : 0.29
% 1.52/1.07  Index Insertion      : 0.00
% 1.52/1.07  Index Deletion       : 0.00
% 1.52/1.07  Index Matching       : 0.00
% 1.52/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
