%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:03 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   26 (  45 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  37 expanded)
%              Number of equality atoms :   17 (  36 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

tff(c_4,plain,(
    ! [B_6,D_8,A_5,C_7] : k2_enumset1(B_6,D_8,A_5,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [B_9,D_10,A_11,C_12] : k2_enumset1(B_9,D_10,A_11,C_12) = k2_enumset1(A_11,B_9,C_12,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_172,plain,(
    ! [D_21,C_22,B_23,A_24] : k2_enumset1(D_21,C_22,B_23,A_24) = k2_enumset1(A_24,B_23,C_22,D_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1,C_3,D_4] : k2_enumset1(B_2,A_1,C_3,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_552,plain,(
    ! [D_33,C_34,B_35,A_36] : k2_enumset1(D_33,C_34,B_35,A_36) = k2_enumset1(B_35,A_36,C_34,D_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2])).

tff(c_32,plain,(
    ! [D_8,C_7,B_6,A_5] : k2_enumset1(D_8,C_7,B_6,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_591,plain,(
    ! [D_33,C_34,B_35,A_36] : k2_enumset1(D_33,C_34,B_35,A_36) = k2_enumset1(D_33,C_34,A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_32])).

tff(c_37,plain,(
    ! [B_13,A_14,C_15,D_16] : k2_enumset1(B_13,A_14,C_15,D_16) = k2_enumset1(A_14,B_13,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [B_13,D_16,A_14,C_15] : k2_enumset1(B_13,D_16,A_14,C_15) = k2_enumset1(B_13,A_14,C_15,D_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_4])).

tff(c_85,plain,(
    ! [D_8,B_6,A_5,C_7] : k2_enumset1(D_8,B_6,A_5,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_6,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_94,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_7])).

tff(c_402,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_94])).

tff(c_2285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:00:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.74  
% 4.01/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.75  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.01/1.75  
% 4.01/1.75  %Foreground sorts:
% 4.01/1.75  
% 4.01/1.75  
% 4.01/1.75  %Background operators:
% 4.01/1.75  
% 4.01/1.75  
% 4.01/1.75  %Foreground operators:
% 4.01/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.01/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.75  
% 4.01/1.75  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 4.01/1.75  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 4.01/1.75  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 4.01/1.75  tff(c_4, plain, (![B_6, D_8, A_5, C_7]: (k2_enumset1(B_6, D_8, A_5, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.01/1.75  tff(c_8, plain, (![B_9, D_10, A_11, C_12]: (k2_enumset1(B_9, D_10, A_11, C_12)=k2_enumset1(A_11, B_9, C_12, D_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.01/1.75  tff(c_172, plain, (![D_21, C_22, B_23, A_24]: (k2_enumset1(D_21, C_22, B_23, A_24)=k2_enumset1(A_24, B_23, C_22, D_21))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8])).
% 4.01/1.75  tff(c_2, plain, (![B_2, A_1, C_3, D_4]: (k2_enumset1(B_2, A_1, C_3, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.01/1.75  tff(c_552, plain, (![D_33, C_34, B_35, A_36]: (k2_enumset1(D_33, C_34, B_35, A_36)=k2_enumset1(B_35, A_36, C_34, D_33))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2])).
% 4.01/1.75  tff(c_32, plain, (![D_8, C_7, B_6, A_5]: (k2_enumset1(D_8, C_7, B_6, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8])).
% 4.01/1.75  tff(c_591, plain, (![D_33, C_34, B_35, A_36]: (k2_enumset1(D_33, C_34, B_35, A_36)=k2_enumset1(D_33, C_34, A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_552, c_32])).
% 4.01/1.75  tff(c_37, plain, (![B_13, A_14, C_15, D_16]: (k2_enumset1(B_13, A_14, C_15, D_16)=k2_enumset1(A_14, B_13, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.01/1.75  tff(c_55, plain, (![B_13, D_16, A_14, C_15]: (k2_enumset1(B_13, D_16, A_14, C_15)=k2_enumset1(B_13, A_14, C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_37, c_4])).
% 4.01/1.75  tff(c_85, plain, (![D_8, B_6, A_5, C_7]: (k2_enumset1(D_8, B_6, A_5, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 4.01/1.75  tff(c_6, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.75  tff(c_7, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 4.01/1.75  tff(c_94, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_7])).
% 4.01/1.75  tff(c_402, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_94])).
% 4.01/1.75  tff(c_2285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_591, c_402])).
% 4.01/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.75  
% 4.01/1.75  Inference rules
% 4.01/1.75  ----------------------
% 4.01/1.75  #Ref     : 0
% 4.01/1.75  #Sup     : 728
% 4.01/1.75  #Fact    : 0
% 4.01/1.75  #Define  : 0
% 4.01/1.75  #Split   : 0
% 4.01/1.75  #Chain   : 0
% 4.01/1.75  #Close   : 0
% 4.01/1.75  
% 4.01/1.75  Ordering : KBO
% 4.01/1.75  
% 4.01/1.75  Simplification rules
% 4.01/1.75  ----------------------
% 4.01/1.75  #Subsume      : 444
% 4.01/1.75  #Demod        : 5
% 4.01/1.75  #Tautology    : 76
% 4.01/1.75  #SimpNegUnit  : 0
% 4.01/1.75  #BackRed      : 2
% 4.01/1.75  
% 4.01/1.75  #Partial instantiations: 0
% 4.01/1.75  #Strategies tried      : 1
% 4.01/1.75  
% 4.01/1.75  Timing (in seconds)
% 4.01/1.75  ----------------------
% 4.01/1.76  Preprocessing        : 0.26
% 4.01/1.76  Parsing              : 0.14
% 4.01/1.76  CNF conversion       : 0.01
% 4.01/1.76  Main loop            : 0.69
% 4.01/1.76  Inferencing          : 0.18
% 4.01/1.76  Reduction            : 0.37
% 4.01/1.76  Demodulation         : 0.34
% 4.01/1.76  BG Simplification    : 0.02
% 4.01/1.76  Subsumption          : 0.10
% 4.01/1.76  Abstraction          : 0.03
% 4.01/1.76  MUC search           : 0.00
% 4.01/1.76  Cooper               : 0.00
% 4.01/1.76  Total                : 0.97
% 4.01/1.76  Index Insertion      : 0.00
% 4.01/1.76  Index Deletion       : 0.00
% 4.01/1.76  Index Matching       : 0.00
% 4.01/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
