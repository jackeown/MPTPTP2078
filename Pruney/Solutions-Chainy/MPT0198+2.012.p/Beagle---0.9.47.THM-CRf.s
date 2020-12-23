%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:06 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  48 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  40 expanded)
%              Number of equality atoms :   17 (  39 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(c_4,plain,(
    ! [C_7,B_6,A_5,D_8] : k2_enumset1(C_7,B_6,A_5,D_8) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_13,C_14,D_15,B_16] : k2_enumset1(A_13,C_14,D_15,B_16) = k2_enumset1(A_13,B_16,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [C_7,D_8,B_6,A_5] : k2_enumset1(C_7,D_8,B_6,A_5) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_173,plain,(
    ! [C_21,D_22,B_23,A_24] : k2_enumset1(C_21,D_22,B_23,A_24) = k2_enumset1(A_24,B_23,C_21,D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_233,plain,(
    ! [B_6,A_5,D_8,C_7] : k2_enumset1(B_6,A_5,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_173])).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [C_17,B_18,A_19,D_20] : k2_enumset1(C_17,B_18,A_19,D_20) = k2_enumset1(A_19,C_17,D_20,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_1665,plain,(
    ! [C_53,A_54,D_55,B_56] : k2_enumset1(C_53,A_54,D_55,B_56) = k2_enumset1(A_54,C_53,D_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_1845,plain,(
    ! [A_5,B_6,D_8,C_7] : k2_enumset1(A_5,B_6,D_8,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_1665])).

tff(c_56,plain,(
    ! [C_14,B_16,A_13,D_15] : k2_enumset1(C_14,B_16,A_13,D_15) = k2_enumset1(A_13,C_14,D_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_6,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_94,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_7])).

tff(c_95,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_2630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.72  
% 4.20/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.72  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.20/1.72  
% 4.20/1.72  %Foreground sorts:
% 4.20/1.72  
% 4.20/1.72  
% 4.20/1.72  %Background operators:
% 4.20/1.72  
% 4.20/1.72  
% 4.20/1.72  %Foreground operators:
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.20/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.72  
% 4.20/1.73  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_enumset1)).
% 4.20/1.73  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 4.20/1.73  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 4.20/1.73  tff(c_4, plain, (![C_7, B_6, A_5, D_8]: (k2_enumset1(C_7, B_6, A_5, D_8)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.20/1.73  tff(c_41, plain, (![A_13, C_14, D_15, B_16]: (k2_enumset1(A_13, C_14, D_15, B_16)=k2_enumset1(A_13, B_16, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/1.73  tff(c_86, plain, (![C_7, D_8, B_6, A_5]: (k2_enumset1(C_7, D_8, B_6, A_5)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_4, c_41])).
% 4.20/1.73  tff(c_173, plain, (![C_21, D_22, B_23, A_24]: (k2_enumset1(C_21, D_22, B_23, A_24)=k2_enumset1(A_24, B_23, C_21, D_22))), inference(superposition, [status(thm), theory('equality')], [c_4, c_41])).
% 4.20/1.73  tff(c_233, plain, (![B_6, A_5, D_8, C_7]: (k2_enumset1(B_6, A_5, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_86, c_173])).
% 4.20/1.73  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/1.73  tff(c_96, plain, (![C_17, B_18, A_19, D_20]: (k2_enumset1(C_17, B_18, A_19, D_20)=k2_enumset1(A_19, C_17, D_20, B_18))), inference(superposition, [status(thm), theory('equality')], [c_41, c_4])).
% 4.20/1.73  tff(c_1665, plain, (![C_53, A_54, D_55, B_56]: (k2_enumset1(C_53, A_54, D_55, B_56)=k2_enumset1(A_54, C_53, D_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 4.20/1.73  tff(c_1845, plain, (![A_5, B_6, D_8, C_7]: (k2_enumset1(A_5, B_6, D_8, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_233, c_1665])).
% 4.20/1.73  tff(c_56, plain, (![C_14, B_16, A_13, D_15]: (k2_enumset1(C_14, B_16, A_13, D_15)=k2_enumset1(A_13, C_14, D_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_41, c_4])).
% 4.20/1.73  tff(c_6, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.20/1.73  tff(c_7, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 4.20/1.73  tff(c_94, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_7])).
% 4.20/1.73  tff(c_95, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_94])).
% 4.20/1.73  tff(c_2630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1845, c_95])).
% 4.20/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.73  
% 4.20/1.73  Inference rules
% 4.20/1.73  ----------------------
% 4.20/1.73  #Ref     : 0
% 4.20/1.73  #Sup     : 840
% 4.20/1.73  #Fact    : 0
% 4.20/1.73  #Define  : 0
% 4.20/1.73  #Split   : 0
% 4.20/1.73  #Chain   : 0
% 4.20/1.73  #Close   : 0
% 4.20/1.73  
% 4.20/1.73  Ordering : KBO
% 4.20/1.73  
% 4.20/1.73  Simplification rules
% 4.20/1.73  ----------------------
% 4.20/1.73  #Subsume      : 532
% 4.20/1.73  #Demod        : 5
% 4.20/1.73  #Tautology    : 84
% 4.20/1.73  #SimpNegUnit  : 0
% 4.20/1.73  #BackRed      : 2
% 4.20/1.73  
% 4.20/1.73  #Partial instantiations: 0
% 4.20/1.73  #Strategies tried      : 1
% 4.20/1.73  
% 4.20/1.73  Timing (in seconds)
% 4.20/1.73  ----------------------
% 4.20/1.73  Preprocessing        : 0.24
% 4.20/1.73  Parsing              : 0.12
% 4.20/1.73  CNF conversion       : 0.01
% 4.20/1.73  Main loop            : 0.73
% 4.20/1.73  Inferencing          : 0.19
% 4.20/1.73  Reduction            : 0.40
% 4.20/1.73  Demodulation         : 0.37
% 4.20/1.73  BG Simplification    : 0.02
% 4.20/1.73  Subsumption          : 0.10
% 4.20/1.73  Abstraction          : 0.03
% 4.20/1.73  MUC search           : 0.00
% 4.20/1.73  Cooper               : 0.00
% 4.20/1.73  Total                : 0.99
% 4.20/1.73  Index Insertion      : 0.00
% 4.20/1.73  Index Deletion       : 0.00
% 4.20/1.73  Index Matching       : 0.00
% 4.20/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
