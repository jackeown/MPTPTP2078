%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:03 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   26 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  21 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [C_11,B_10,A_9,D_12] : k2_enumset1(C_11,B_10,A_9,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_39,C_40,D_41,B_42] : k2_enumset1(A_39,C_40,D_41,B_42) = k2_enumset1(A_39,B_42,C_40,D_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_100,plain,(
    ! [C_11,A_9,D_12,B_10] : k2_enumset1(C_11,A_9,D_12,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_17])).

tff(c_587,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_18])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.97  
% 2.81/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.98  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.98  
% 2.81/1.98  %Foreground sorts:
% 2.81/1.98  
% 2.81/1.98  
% 2.81/1.98  %Background operators:
% 2.81/1.98  
% 2.81/1.98  
% 2.81/1.98  %Foreground operators:
% 2.81/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.98  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.98  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.98  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.98  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.98  
% 2.81/1.98  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 2.81/1.98  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_enumset1)).
% 2.81/1.98  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.81/1.98  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 2.81/1.98  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.98  tff(c_6, plain, (![C_11, B_10, A_9, D_12]: (k2_enumset1(C_11, B_10, A_9, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.98  tff(c_52, plain, (![A_39, C_40, D_41, B_42]: (k2_enumset1(A_39, C_40, D_41, B_42)=k2_enumset1(A_39, B_42, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.98  tff(c_100, plain, (![C_11, A_9, D_12, B_10]: (k2_enumset1(C_11, A_9, D_12, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_52])).
% 2.81/1.98  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.98  tff(c_16, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.81/1.98  tff(c_17, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.81/1.98  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_17])).
% 2.81/1.98  tff(c_587, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_18])).
% 2.81/1.98  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_587])).
% 2.81/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.98  
% 2.81/1.98  Inference rules
% 2.81/1.98  ----------------------
% 2.81/1.98  #Ref     : 0
% 2.81/1.98  #Sup     : 172
% 2.81/1.98  #Fact    : 0
% 2.81/1.98  #Define  : 0
% 2.81/1.98  #Split   : 0
% 2.81/1.98  #Chain   : 0
% 2.81/1.98  #Close   : 0
% 2.81/1.98  
% 2.81/1.98  Ordering : KBO
% 2.81/1.98  
% 2.81/1.98  Simplification rules
% 2.81/1.98  ----------------------
% 2.81/1.98  #Subsume      : 53
% 2.81/1.98  #Demod        : 6
% 2.81/1.98  #Tautology    : 44
% 2.81/1.98  #SimpNegUnit  : 0
% 2.81/1.98  #BackRed      : 1
% 2.81/1.98  
% 2.81/1.98  #Partial instantiations: 0
% 2.81/1.98  #Strategies tried      : 1
% 2.81/1.98  
% 2.81/1.98  Timing (in seconds)
% 2.81/1.98  ----------------------
% 2.81/1.99  Preprocessing        : 0.52
% 2.81/1.99  Parsing              : 0.29
% 2.81/1.99  CNF conversion       : 0.03
% 2.81/1.99  Main loop            : 0.54
% 2.81/1.99  Inferencing          : 0.17
% 2.81/1.99  Reduction            : 0.23
% 2.81/1.99  Demodulation         : 0.21
% 2.81/1.99  BG Simplification    : 0.05
% 2.81/1.99  Subsumption          : 0.09
% 2.81/1.99  Abstraction          : 0.04
% 2.81/1.99  MUC search           : 0.00
% 2.81/1.99  Cooper               : 0.00
% 2.81/1.99  Total                : 1.08
% 2.81/1.99  Index Insertion      : 0.00
% 2.81/1.99  Index Deletion       : 0.00
% 2.81/1.99  Index Matching       : 0.00
% 2.81/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
