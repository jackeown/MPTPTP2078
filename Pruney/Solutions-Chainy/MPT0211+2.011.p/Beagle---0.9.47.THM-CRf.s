%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:16 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  27 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_22,plain,(
    ! [D_36,C_35,B_34,A_33] : k2_enumset1(D_36,C_35,B_34,A_33) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_450,plain,(
    ! [A_97,D_98,C_99,B_100] : k2_enumset1(A_97,D_98,C_99,B_100) = k2_enumset1(A_97,B_100,C_99,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_574,plain,(
    ! [B_101,D_102,C_103] : k2_enumset1(B_101,D_102,C_103,B_101) = k1_enumset1(B_101,C_103,D_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_34])).

tff(c_1029,plain,(
    ! [A_120,B_121,C_122] : k2_enumset1(A_120,B_121,C_122,A_120) = k1_enumset1(A_120,B_121,C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_574])).

tff(c_506,plain,(
    ! [B_100,D_98,C_99] : k2_enumset1(B_100,D_98,C_99,B_100) = k1_enumset1(B_100,C_99,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_34])).

tff(c_1045,plain,(
    ! [A_120,C_122,B_121] : k1_enumset1(A_120,C_122,B_121) = k1_enumset1(A_120,B_121,C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_506])).

tff(c_16,plain,(
    ! [A_21,C_23,B_22,D_24] : k2_enumset1(A_21,C_23,B_22,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_40,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16,c_22,c_39])).

tff(c_1150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:03:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.39  
% 2.85/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.39  %$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.85/1.39  
% 2.85/1.39  %Foreground sorts:
% 2.85/1.39  
% 2.85/1.39  
% 2.85/1.39  %Background operators:
% 2.85/1.39  
% 2.85/1.39  
% 2.85/1.39  %Foreground operators:
% 2.85/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.39  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.85/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.85/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.85/1.39  
% 2.85/1.40  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 2.85/1.40  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.85/1.40  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.85/1.40  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 2.85/1.40  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.85/1.40  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 2.85/1.40  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.85/1.40  tff(c_450, plain, (![A_97, D_98, C_99, B_100]: (k2_enumset1(A_97, D_98, C_99, B_100)=k2_enumset1(A_97, B_100, C_99, D_98))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.85/1.40  tff(c_34, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.40  tff(c_574, plain, (![B_101, D_102, C_103]: (k2_enumset1(B_101, D_102, C_103, B_101)=k1_enumset1(B_101, C_103, D_102))), inference(superposition, [status(thm), theory('equality')], [c_450, c_34])).
% 2.85/1.40  tff(c_1029, plain, (![A_120, B_121, C_122]: (k2_enumset1(A_120, B_121, C_122, A_120)=k1_enumset1(A_120, B_121, C_122))), inference(superposition, [status(thm), theory('equality')], [c_22, c_574])).
% 2.85/1.40  tff(c_506, plain, (![B_100, D_98, C_99]: (k2_enumset1(B_100, D_98, C_99, B_100)=k1_enumset1(B_100, C_99, D_98))), inference(superposition, [status(thm), theory('equality')], [c_450, c_34])).
% 2.85/1.40  tff(c_1045, plain, (![A_120, C_122, B_121]: (k1_enumset1(A_120, C_122, B_121)=k1_enumset1(A_120, B_121, C_122))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_506])).
% 2.85/1.40  tff(c_16, plain, (![A_21, C_23, B_22, D_24]: (k2_enumset1(A_21, C_23, B_22, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.85/1.40  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.40  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.85/1.40  tff(c_39, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 2.85/1.40  tff(c_40, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16, c_22, c_39])).
% 2.85/1.40  tff(c_1150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1045, c_40])).
% 2.85/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.40  
% 2.85/1.40  Inference rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Ref     : 0
% 2.85/1.40  #Sup     : 279
% 2.85/1.40  #Fact    : 0
% 2.85/1.40  #Define  : 0
% 2.85/1.40  #Split   : 0
% 2.85/1.40  #Chain   : 0
% 2.85/1.40  #Close   : 0
% 2.85/1.40  
% 2.85/1.40  Ordering : KBO
% 2.85/1.40  
% 2.85/1.40  Simplification rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Subsume      : 7
% 2.85/1.40  #Demod        : 104
% 2.85/1.40  #Tautology    : 159
% 2.85/1.40  #SimpNegUnit  : 0
% 2.85/1.40  #BackRed      : 1
% 2.85/1.40  
% 2.85/1.40  #Partial instantiations: 0
% 2.85/1.40  #Strategies tried      : 1
% 2.85/1.40  
% 2.85/1.40  Timing (in seconds)
% 2.85/1.40  ----------------------
% 2.85/1.40  Preprocessing        : 0.31
% 2.85/1.40  Parsing              : 0.17
% 2.85/1.40  CNF conversion       : 0.02
% 2.85/1.40  Main loop            : 0.35
% 2.85/1.40  Inferencing          : 0.12
% 2.85/1.40  Reduction            : 0.15
% 2.85/1.40  Demodulation         : 0.12
% 2.85/1.40  BG Simplification    : 0.02
% 2.85/1.40  Subsumption          : 0.05
% 2.85/1.40  Abstraction          : 0.02
% 2.85/1.40  MUC search           : 0.00
% 2.85/1.40  Cooper               : 0.00
% 2.85/1.40  Total                : 0.68
% 2.85/1.40  Index Insertion      : 0.00
% 2.85/1.40  Index Deletion       : 0.00
% 2.85/1.40  Index Matching       : 0.00
% 2.85/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
