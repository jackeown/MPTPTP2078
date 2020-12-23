%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:08 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   19 (  22 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  14 expanded)
%              Number of equality atoms :   10 (  13 expanded)
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

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1,D_4,C_3] : k2_enumset1(B_2,A_1,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [B_13,D_14,A_15,C_16] : k2_enumset1(B_13,D_14,A_15,C_16) = k2_enumset1(A_15,B_13,C_16,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_1,C_3,B_2,D_4] : k2_enumset1(A_1,C_3,B_2,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_4,plain,(
    ! [B_6,D_8,A_5,C_7] : k2_enumset1(B_6,D_8,A_5,C_7) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [C_16,A_15,D_14,B_13] : k2_enumset1(C_16,A_15,D_14,B_13) = k2_enumset1(B_13,D_14,A_15,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_6])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:01:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  %$ k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.20  
% 1.98/1.20  %Foreground sorts:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Background operators:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Foreground operators:
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.20  
% 1.98/1.20  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_enumset1)).
% 1.98/1.20  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 1.98/1.20  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 1.98/1.20  tff(c_2, plain, (![B_2, A_1, D_4, C_3]: (k2_enumset1(B_2, A_1, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.20  tff(c_40, plain, (![B_13, D_14, A_15, C_16]: (k2_enumset1(B_13, D_14, A_15, C_16)=k2_enumset1(A_15, B_13, C_16, D_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.20  tff(c_88, plain, (![A_1, C_3, B_2, D_4]: (k2_enumset1(A_1, C_3, B_2, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(superposition, [status(thm), theory('equality')], [c_2, c_40])).
% 1.98/1.20  tff(c_4, plain, (![B_6, D_8, A_5, C_7]: (k2_enumset1(B_6, D_8, A_5, C_7)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.20  tff(c_43, plain, (![C_16, A_15, D_14, B_13]: (k2_enumset1(C_16, A_15, D_14, B_13)=k2_enumset1(B_13, D_14, A_15, C_16))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 1.98/1.20  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.20  tff(c_93, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_6])).
% 1.98/1.20  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_93])).
% 1.98/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  Inference rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Ref     : 0
% 1.98/1.20  #Sup     : 80
% 1.98/1.20  #Fact    : 0
% 1.98/1.20  #Define  : 0
% 1.98/1.20  #Split   : 0
% 1.98/1.20  #Chain   : 0
% 1.98/1.20  #Close   : 0
% 1.98/1.20  
% 1.98/1.20  Ordering : KBO
% 1.98/1.20  
% 1.98/1.20  Simplification rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Subsume      : 22
% 1.98/1.20  #Demod        : 2
% 1.98/1.20  #Tautology    : 28
% 1.98/1.20  #SimpNegUnit  : 0
% 1.98/1.20  #BackRed      : 1
% 1.98/1.20  
% 1.98/1.20  #Partial instantiations: 0
% 1.98/1.20  #Strategies tried      : 1
% 1.98/1.20  
% 1.98/1.20  Timing (in seconds)
% 1.98/1.20  ----------------------
% 1.98/1.21  Preprocessing        : 0.25
% 1.98/1.21  Parsing              : 0.13
% 1.98/1.21  CNF conversion       : 0.01
% 1.98/1.21  Main loop            : 0.20
% 1.98/1.21  Inferencing          : 0.07
% 2.11/1.21  Reduction            : 0.08
% 2.11/1.21  Demodulation         : 0.07
% 2.11/1.21  BG Simplification    : 0.01
% 2.11/1.21  Subsumption          : 0.03
% 2.11/1.21  Abstraction          : 0.01
% 2.11/1.21  MUC search           : 0.00
% 2.11/1.21  Cooper               : 0.00
% 2.11/1.21  Total                : 0.47
% 2.11/1.21  Index Insertion      : 0.00
% 2.11/1.21  Index Deletion       : 0.00
% 2.11/1.21  Index Matching       : 0.00
% 2.11/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
