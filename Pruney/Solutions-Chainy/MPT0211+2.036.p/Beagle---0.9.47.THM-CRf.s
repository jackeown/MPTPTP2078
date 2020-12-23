%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:19 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :   23 (  31 expanded)
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

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_34,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_197,plain,(
    ! [C_84,D_85,A_86,B_87] : k2_enumset1(C_84,D_85,A_86,B_87) = k2_enumset1(A_86,B_87,C_84,D_85) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_283,plain,(
    ! [B_88,C_89,A_90] : k2_enumset1(B_88,C_89,A_90,A_90) = k1_enumset1(A_90,B_88,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_197])).

tff(c_18,plain,(
    ! [B_26,D_28,C_27,A_25] : k2_enumset1(B_26,D_28,C_27,A_25) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_299,plain,(
    ! [A_90,B_88,C_89] : k2_enumset1(A_90,B_88,A_90,C_89) = k1_enumset1(A_90,B_88,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_18])).

tff(c_20,plain,(
    ! [C_31,D_32,A_29,B_30] : k2_enumset1(C_31,D_32,A_29,B_30) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_119,plain,(
    ! [B_77,D_78,C_79,A_80] : k2_enumset1(B_77,D_78,C_79,A_80) = k2_enumset1(A_80,B_77,C_79,D_78) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_417,plain,(
    ! [A_95,D_96,C_97] : k2_enumset1(A_95,D_96,C_97,D_96) = k1_enumset1(D_96,C_97,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_34])).

tff(c_641,plain,(
    ! [A_104,B_105,C_106] : k2_enumset1(A_104,B_105,C_106,B_105) = k1_enumset1(B_105,A_104,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_417])).

tff(c_139,plain,(
    ! [A_80,D_78,C_79] : k2_enumset1(A_80,D_78,C_79,D_78) = k1_enumset1(D_78,C_79,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_34])).

tff(c_647,plain,(
    ! [B_105,C_106,A_104] : k1_enumset1(B_105,C_106,A_104) = k1_enumset1(B_105,A_104,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_139])).

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

tff(c_893,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_40])).

tff(c_1082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:46:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  %$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.71/1.43  
% 2.71/1.43  %Foreground sorts:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Background operators:
% 2.71/1.43  
% 2.71/1.43  
% 2.71/1.43  %Foreground operators:
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.43  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.43  
% 2.71/1.44  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.71/1.44  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_enumset1)).
% 2.71/1.44  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 2.71/1.44  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 2.71/1.44  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.71/1.44  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 2.71/1.44  tff(c_34, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.71/1.44  tff(c_197, plain, (![C_84, D_85, A_86, B_87]: (k2_enumset1(C_84, D_85, A_86, B_87)=k2_enumset1(A_86, B_87, C_84, D_85))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.44  tff(c_283, plain, (![B_88, C_89, A_90]: (k2_enumset1(B_88, C_89, A_90, A_90)=k1_enumset1(A_90, B_88, C_89))), inference(superposition, [status(thm), theory('equality')], [c_34, c_197])).
% 2.71/1.44  tff(c_18, plain, (![B_26, D_28, C_27, A_25]: (k2_enumset1(B_26, D_28, C_27, A_25)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.44  tff(c_299, plain, (![A_90, B_88, C_89]: (k2_enumset1(A_90, B_88, A_90, C_89)=k1_enumset1(A_90, B_88, C_89))), inference(superposition, [status(thm), theory('equality')], [c_283, c_18])).
% 2.71/1.44  tff(c_20, plain, (![C_31, D_32, A_29, B_30]: (k2_enumset1(C_31, D_32, A_29, B_30)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.44  tff(c_119, plain, (![B_77, D_78, C_79, A_80]: (k2_enumset1(B_77, D_78, C_79, A_80)=k2_enumset1(A_80, B_77, C_79, D_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.44  tff(c_417, plain, (![A_95, D_96, C_97]: (k2_enumset1(A_95, D_96, C_97, D_96)=k1_enumset1(D_96, C_97, A_95))), inference(superposition, [status(thm), theory('equality')], [c_119, c_34])).
% 2.71/1.44  tff(c_641, plain, (![A_104, B_105, C_106]: (k2_enumset1(A_104, B_105, C_106, B_105)=k1_enumset1(B_105, A_104, C_106))), inference(superposition, [status(thm), theory('equality')], [c_20, c_417])).
% 2.71/1.44  tff(c_139, plain, (![A_80, D_78, C_79]: (k2_enumset1(A_80, D_78, C_79, D_78)=k1_enumset1(D_78, C_79, A_80))), inference(superposition, [status(thm), theory('equality')], [c_119, c_34])).
% 2.71/1.44  tff(c_647, plain, (![B_105, C_106, A_104]: (k1_enumset1(B_105, C_106, A_104)=k1_enumset1(B_105, A_104, C_106))), inference(superposition, [status(thm), theory('equality')], [c_641, c_139])).
% 2.71/1.44  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.71/1.44  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.44  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.44  tff(c_39, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 2.71/1.44  tff(c_40, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_39])).
% 2.71/1.44  tff(c_893, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_647, c_40])).
% 2.71/1.44  tff(c_1082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_893])).
% 2.71/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  
% 2.71/1.44  Inference rules
% 2.71/1.44  ----------------------
% 2.71/1.44  #Ref     : 0
% 2.71/1.44  #Sup     : 266
% 2.71/1.44  #Fact    : 0
% 2.71/1.44  #Define  : 0
% 2.71/1.44  #Split   : 0
% 2.71/1.44  #Chain   : 0
% 2.71/1.44  #Close   : 0
% 2.71/1.44  
% 2.71/1.44  Ordering : KBO
% 2.71/1.44  
% 2.71/1.44  Simplification rules
% 2.71/1.44  ----------------------
% 2.71/1.44  #Subsume      : 10
% 2.71/1.44  #Demod        : 83
% 2.71/1.44  #Tautology    : 143
% 2.71/1.44  #SimpNegUnit  : 0
% 2.71/1.44  #BackRed      : 2
% 2.71/1.44  
% 2.71/1.44  #Partial instantiations: 0
% 2.71/1.44  #Strategies tried      : 1
% 2.71/1.44  
% 2.71/1.44  Timing (in seconds)
% 2.71/1.44  ----------------------
% 2.71/1.45  Preprocessing        : 0.32
% 2.71/1.45  Parsing              : 0.18
% 2.71/1.45  CNF conversion       : 0.02
% 2.71/1.45  Main loop            : 0.36
% 2.71/1.45  Inferencing          : 0.12
% 2.71/1.45  Reduction            : 0.14
% 2.71/1.45  Demodulation         : 0.12
% 2.71/1.45  BG Simplification    : 0.02
% 2.71/1.45  Subsumption          : 0.05
% 2.71/1.45  Abstraction          : 0.02
% 2.71/1.45  MUC search           : 0.00
% 2.71/1.45  Cooper               : 0.00
% 2.71/1.45  Total                : 0.70
% 2.71/1.45  Index Insertion      : 0.00
% 2.71/1.45  Index Deletion       : 0.00
% 2.71/1.45  Index Matching       : 0.00
% 2.71/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
