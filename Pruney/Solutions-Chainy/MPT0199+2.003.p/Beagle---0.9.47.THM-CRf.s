%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:06 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  19 expanded)
%              Number of equality atoms :   13 (  18 expanded)
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

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(c_6,plain,(
    ! [A_9,D_12,C_11,B_10] : k2_enumset1(A_9,D_12,C_11,B_10) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_25,C_26,D_27,B_28] : k2_enumset1(A_25,C_26,D_27,B_28) = k2_enumset1(A_25,B_28,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [A_9,D_12,C_11,B_10] : k2_enumset1(A_9,D_12,C_11,B_10) = k2_enumset1(A_9,D_12,B_10,C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_100])).

tff(c_4,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4] : k2_enumset1(B_2,C_3,A_1,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11])).

tff(c_13,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:03:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  %$ k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.26  
% 2.24/1.26  %Foreground sorts:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Background operators:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Foreground operators:
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.26  
% 2.24/1.26  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.24/1.26  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 2.24/1.26  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l123_enumset1)).
% 2.24/1.26  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 2.24/1.26  tff(c_6, plain, (![A_9, D_12, C_11, B_10]: (k2_enumset1(A_9, D_12, C_11, B_10)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.26  tff(c_100, plain, (![A_25, C_26, D_27, B_28]: (k2_enumset1(A_25, C_26, D_27, B_28)=k2_enumset1(A_25, B_28, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.26  tff(c_163, plain, (![A_9, D_12, C_11, B_10]: (k2_enumset1(A_9, D_12, C_11, B_10)=k2_enumset1(A_9, D_12, B_10, C_11))), inference(superposition, [status(thm), theory('equality')], [c_6, c_100])).
% 2.24/1.26  tff(c_4, plain, (![A_5, C_7, D_8, B_6]: (k2_enumset1(A_5, C_7, D_8, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.26  tff(c_2, plain, (![B_2, C_3, A_1, D_4]: (k2_enumset1(B_2, C_3, A_1, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.26  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.24/1.26  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_10])).
% 2.24/1.26  tff(c_12, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11])).
% 2.24/1.26  tff(c_13, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 2.24/1.26  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_13])).
% 2.24/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  Inference rules
% 2.24/1.26  ----------------------
% 2.24/1.26  #Ref     : 0
% 2.24/1.27  #Sup     : 122
% 2.24/1.27  #Fact    : 0
% 2.24/1.27  #Define  : 0
% 2.24/1.27  #Split   : 0
% 2.24/1.27  #Chain   : 0
% 2.24/1.27  #Close   : 0
% 2.24/1.27  
% 2.24/1.27  Ordering : KBO
% 2.24/1.27  
% 2.24/1.27  Simplification rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Subsume      : 27
% 2.24/1.27  #Demod        : 5
% 2.24/1.27  #Tautology    : 30
% 2.24/1.27  #SimpNegUnit  : 0
% 2.24/1.27  #BackRed      : 1
% 2.24/1.27  
% 2.24/1.27  #Partial instantiations: 0
% 2.24/1.27  #Strategies tried      : 1
% 2.24/1.27  
% 2.24/1.27  Timing (in seconds)
% 2.24/1.27  ----------------------
% 2.24/1.27  Preprocessing        : 0.26
% 2.24/1.27  Parsing              : 0.14
% 2.24/1.27  CNF conversion       : 0.01
% 2.24/1.27  Main loop            : 0.24
% 2.24/1.27  Inferencing          : 0.08
% 2.24/1.27  Reduction            : 0.10
% 2.24/1.27  Demodulation         : 0.09
% 2.24/1.27  BG Simplification    : 0.02
% 2.24/1.27  Subsumption          : 0.03
% 2.24/1.27  Abstraction          : 0.01
% 2.24/1.27  MUC search           : 0.00
% 2.24/1.27  Cooper               : 0.00
% 2.24/1.27  Total                : 0.52
% 2.24/1.27  Index Insertion      : 0.00
% 2.24/1.27  Index Deletion       : 0.00
% 2.24/1.27  Index Matching       : 0.00
% 2.24/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
