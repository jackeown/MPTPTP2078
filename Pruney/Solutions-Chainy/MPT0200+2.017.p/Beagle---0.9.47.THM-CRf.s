%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:10 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   18 (  22 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  14 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(c_4,plain,(
    ! [C_7,D_8,B_6,A_5] : k2_enumset1(C_7,D_8,B_6,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_13,A_14,C_15,D_16] : k2_enumset1(B_13,A_14,C_15,D_16) = k2_enumset1(A_14,B_13,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_280,plain,(
    ! [C_25,D_26,B_27,A_28] : k2_enumset1(C_25,D_26,B_27,A_28) = k2_enumset1(B_27,A_28,C_25,D_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_340,plain,(
    ! [B_27,A_28,D_26,C_25] : k2_enumset1(B_27,A_28,D_26,C_25) = k2_enumset1(B_27,A_28,C_25,D_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_4])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.57  
% 2.79/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.57  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.57  
% 2.79/1.57  %Foreground sorts:
% 2.79/1.57  
% 2.79/1.57  
% 2.79/1.57  %Background operators:
% 2.79/1.57  
% 2.79/1.57  
% 2.79/1.57  %Foreground operators:
% 2.79/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.57  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.57  
% 2.79/1.58  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_enumset1)).
% 2.79/1.58  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 2.79/1.58  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 2.79/1.58  tff(c_4, plain, (![C_7, D_8, B_6, A_5]: (k2_enumset1(C_7, D_8, B_6, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.58  tff(c_37, plain, (![B_13, A_14, C_15, D_16]: (k2_enumset1(B_13, A_14, C_15, D_16)=k2_enumset1(A_14, B_13, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.79/1.58  tff(c_280, plain, (![C_25, D_26, B_27, A_28]: (k2_enumset1(C_25, D_26, B_27, A_28)=k2_enumset1(B_27, A_28, C_25, D_26))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 2.79/1.58  tff(c_340, plain, (![B_27, A_28, D_26, C_25]: (k2_enumset1(B_27, A_28, D_26, C_25)=k2_enumset1(B_27, A_28, C_25, D_26))), inference(superposition, [status(thm), theory('equality')], [c_280, c_4])).
% 2.79/1.58  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.58  tff(c_7, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.79/1.58  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_340, c_7])).
% 2.79/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.58  
% 2.79/1.58  Inference rules
% 2.79/1.58  ----------------------
% 2.79/1.58  #Ref     : 0
% 2.79/1.58  #Sup     : 120
% 2.79/1.58  #Fact    : 0
% 2.79/1.58  #Define  : 0
% 2.79/1.58  #Split   : 0
% 2.79/1.58  #Chain   : 0
% 2.79/1.58  #Close   : 0
% 2.79/1.58  
% 2.79/1.58  Ordering : KBO
% 2.79/1.58  
% 2.79/1.58  Simplification rules
% 2.79/1.58  ----------------------
% 2.79/1.58  #Subsume      : 57
% 2.79/1.58  #Demod        : 2
% 2.79/1.58  #Tautology    : 36
% 2.79/1.58  #SimpNegUnit  : 0
% 2.79/1.58  #BackRed      : 1
% 2.79/1.58  
% 2.79/1.58  #Partial instantiations: 0
% 2.79/1.58  #Strategies tried      : 1
% 2.79/1.58  
% 2.79/1.58  Timing (in seconds)
% 2.79/1.58  ----------------------
% 2.79/1.59  Preprocessing        : 0.38
% 2.79/1.59  Parsing              : 0.19
% 2.79/1.59  CNF conversion       : 0.03
% 2.79/1.59  Main loop            : 0.41
% 2.79/1.59  Inferencing          : 0.14
% 2.79/1.59  Reduction            : 0.17
% 2.79/1.59  Demodulation         : 0.15
% 2.79/1.59  BG Simplification    : 0.03
% 2.79/1.59  Subsumption          : 0.06
% 2.79/1.59  Abstraction          : 0.02
% 2.79/1.59  MUC search           : 0.00
% 2.79/1.59  Cooper               : 0.00
% 2.79/1.59  Total                : 0.83
% 2.79/1.59  Index Insertion      : 0.00
% 2.79/1.59  Index Deletion       : 0.00
% 2.79/1.59  Index Matching       : 0.00
% 2.79/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
