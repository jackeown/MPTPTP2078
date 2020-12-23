%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:20 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  32 expanded)
%              Number of equality atoms :   21 (  31 expanded)
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

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_119,plain,(
    ! [B_77,D_78,C_79,A_80] : k2_enumset1(B_77,D_78,C_79,A_80) = k2_enumset1(A_80,B_77,C_79,D_78) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_135,plain,(
    ! [B_77,D_78,C_79] : k2_enumset1(B_77,D_78,C_79,B_77) = k1_enumset1(B_77,C_79,D_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_34])).

tff(c_379,plain,(
    ! [D_93,C_94,B_95,A_96] : k2_enumset1(D_93,C_94,B_95,A_96) = k2_enumset1(A_96,B_95,C_94,D_93) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_982,plain,(
    ! [B_114,C_115,D_116] : k2_enumset1(B_114,C_115,D_116,B_114) = k1_enumset1(B_114,C_115,D_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_379])).

tff(c_1012,plain,(
    ! [B_114,D_116,C_115] : k1_enumset1(B_114,D_116,C_115) = k1_enumset1(B_114,C_115,D_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_135])).

tff(c_20,plain,(
    ! [D_32,B_30,C_31,A_29] : k2_enumset1(D_32,B_30,C_31,A_29) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_502,plain,(
    ! [D_97,C_98,B_99] : k2_enumset1(D_97,C_98,B_99,B_99) = k1_enumset1(B_99,C_98,D_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_34])).

tff(c_558,plain,(
    ! [A_29,B_30,D_32] : k2_enumset1(A_29,B_30,A_29,D_32) = k1_enumset1(A_29,B_30,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_502])).

tff(c_22,plain,(
    ! [D_36,C_35,B_34,A_33] : k2_enumset1(D_36,C_35,B_34,A_33) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

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
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_39])).

tff(c_868,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_40])).

tff(c_1094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.44  
% 3.09/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.44  %$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.09/1.44  
% 3.09/1.44  %Foreground sorts:
% 3.09/1.44  
% 3.09/1.44  
% 3.09/1.44  %Background operators:
% 3.09/1.44  
% 3.09/1.44  
% 3.09/1.44  %Foreground operators:
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.44  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.44  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.44  
% 3.09/1.45  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.09/1.45  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.09/1.45  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.09/1.45  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 3.09/1.45  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.09/1.45  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.09/1.45  tff(c_119, plain, (![B_77, D_78, C_79, A_80]: (k2_enumset1(B_77, D_78, C_79, A_80)=k2_enumset1(A_80, B_77, C_79, D_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.45  tff(c_34, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.09/1.45  tff(c_135, plain, (![B_77, D_78, C_79]: (k2_enumset1(B_77, D_78, C_79, B_77)=k1_enumset1(B_77, C_79, D_78))), inference(superposition, [status(thm), theory('equality')], [c_119, c_34])).
% 3.09/1.45  tff(c_379, plain, (![D_93, C_94, B_95, A_96]: (k2_enumset1(D_93, C_94, B_95, A_96)=k2_enumset1(A_96, B_95, C_94, D_93))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.45  tff(c_982, plain, (![B_114, C_115, D_116]: (k2_enumset1(B_114, C_115, D_116, B_114)=k1_enumset1(B_114, C_115, D_116))), inference(superposition, [status(thm), theory('equality')], [c_135, c_379])).
% 3.09/1.45  tff(c_1012, plain, (![B_114, D_116, C_115]: (k1_enumset1(B_114, D_116, C_115)=k1_enumset1(B_114, C_115, D_116))), inference(superposition, [status(thm), theory('equality')], [c_982, c_135])).
% 3.09/1.45  tff(c_20, plain, (![D_32, B_30, C_31, A_29]: (k2_enumset1(D_32, B_30, C_31, A_29)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.45  tff(c_502, plain, (![D_97, C_98, B_99]: (k2_enumset1(D_97, C_98, B_99, B_99)=k1_enumset1(B_99, C_98, D_97))), inference(superposition, [status(thm), theory('equality')], [c_379, c_34])).
% 3.09/1.45  tff(c_558, plain, (![A_29, B_30, D_32]: (k2_enumset1(A_29, B_30, A_29, D_32)=k1_enumset1(A_29, B_30, D_32))), inference(superposition, [status(thm), theory('equality')], [c_20, c_502])).
% 3.09/1.45  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.45  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.09/1.45  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.45  tff(c_39, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 3.09/1.45  tff(c_40, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_39])).
% 3.09/1.45  tff(c_868, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_40])).
% 3.09/1.45  tff(c_1094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1012, c_868])).
% 3.09/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.45  
% 3.09/1.45  Inference rules
% 3.09/1.45  ----------------------
% 3.09/1.45  #Ref     : 0
% 3.09/1.45  #Sup     : 268
% 3.09/1.45  #Fact    : 0
% 3.09/1.45  #Define  : 0
% 3.09/1.45  #Split   : 0
% 3.09/1.45  #Chain   : 0
% 3.09/1.45  #Close   : 0
% 3.09/1.45  
% 3.09/1.45  Ordering : KBO
% 3.09/1.45  
% 3.09/1.45  Simplification rules
% 3.09/1.45  ----------------------
% 3.09/1.45  #Subsume      : 19
% 3.09/1.45  #Demod        : 95
% 3.09/1.45  #Tautology    : 145
% 3.09/1.45  #SimpNegUnit  : 0
% 3.09/1.45  #BackRed      : 2
% 3.09/1.45  
% 3.09/1.45  #Partial instantiations: 0
% 3.09/1.45  #Strategies tried      : 1
% 3.09/1.45  
% 3.09/1.45  Timing (in seconds)
% 3.09/1.45  ----------------------
% 3.09/1.46  Preprocessing        : 0.32
% 3.09/1.46  Parsing              : 0.17
% 3.09/1.46  CNF conversion       : 0.02
% 3.09/1.46  Main loop            : 0.38
% 3.09/1.46  Inferencing          : 0.13
% 3.09/1.46  Reduction            : 0.15
% 3.09/1.46  Demodulation         : 0.13
% 3.09/1.46  BG Simplification    : 0.02
% 3.09/1.46  Subsumption          : 0.05
% 3.09/1.46  Abstraction          : 0.02
% 3.09/1.46  MUC search           : 0.00
% 3.09/1.46  Cooper               : 0.00
% 3.09/1.46  Total                : 0.72
% 3.09/1.46  Index Insertion      : 0.00
% 3.09/1.46  Index Deletion       : 0.00
% 3.09/1.46  Index Matching       : 0.00
% 3.09/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
