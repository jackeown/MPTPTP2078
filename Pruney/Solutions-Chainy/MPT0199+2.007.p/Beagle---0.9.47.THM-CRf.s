%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:07 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  17 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [A_25,C_26,D_27,B_28] : k2_enumset1(A_25,C_26,D_27,B_28) = k2_enumset1(A_25,B_28,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,D_8,B_6,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [C_11,D_12,B_10,A_9] : k2_enumset1(C_11,D_12,B_10,A_9) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_11])).

tff(c_13,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.35  
% 2.60/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  %$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.60/1.36  
% 2.60/1.36  %Foreground sorts:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Background operators:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Foreground operators:
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.60/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.36  
% 2.60/1.36  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 2.60/1.36  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 2.60/1.36  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_enumset1)).
% 2.60/1.36  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 2.60/1.36  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.36  tff(c_100, plain, (![A_25, C_26, D_27, B_28]: (k2_enumset1(A_25, C_26, D_27, B_28)=k2_enumset1(A_25, B_28, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.36  tff(c_151, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, D_8, B_6, C_7))), inference(superposition, [status(thm), theory('equality')], [c_4, c_100])).
% 2.60/1.36  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.36  tff(c_6, plain, (![C_11, D_12, B_10, A_9]: (k2_enumset1(C_11, D_12, B_10, A_9)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.36  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.60/1.36  tff(c_11, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.60/1.36  tff(c_12, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_11])).
% 2.60/1.36  tff(c_13, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 2.60/1.36  tff(c_748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_13])).
% 2.60/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  Inference rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Ref     : 0
% 2.60/1.36  #Sup     : 226
% 2.60/1.36  #Fact    : 0
% 2.60/1.36  #Define  : 0
% 2.60/1.36  #Split   : 0
% 2.60/1.36  #Chain   : 0
% 2.60/1.36  #Close   : 0
% 2.60/1.36  
% 2.60/1.36  Ordering : KBO
% 2.60/1.36  
% 2.60/1.36  Simplification rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Subsume      : 62
% 2.60/1.36  #Demod        : 4
% 2.60/1.36  #Tautology    : 46
% 2.60/1.36  #SimpNegUnit  : 0
% 2.60/1.36  #BackRed      : 1
% 2.60/1.36  
% 2.60/1.36  #Partial instantiations: 0
% 2.60/1.36  #Strategies tried      : 1
% 2.60/1.36  
% 2.60/1.36  Timing (in seconds)
% 2.60/1.36  ----------------------
% 2.60/1.37  Preprocessing        : 0.27
% 2.60/1.37  Parsing              : 0.14
% 2.60/1.37  CNF conversion       : 0.01
% 2.60/1.37  Main loop            : 0.35
% 2.60/1.37  Inferencing          : 0.11
% 2.60/1.37  Reduction            : 0.15
% 2.60/1.37  Demodulation         : 0.14
% 2.60/1.37  BG Simplification    : 0.02
% 2.60/1.37  Subsumption          : 0.05
% 2.60/1.37  Abstraction          : 0.02
% 2.60/1.37  MUC search           : 0.00
% 2.60/1.37  Cooper               : 0.00
% 2.60/1.37  Total                : 0.63
% 2.60/1.37  Index Insertion      : 0.00
% 2.60/1.37  Index Deletion       : 0.00
% 2.60/1.37  Index Matching       : 0.00
% 2.60/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
