%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:20 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  27 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_247,plain,(
    ! [A_93,C_94,B_95,D_96] : k2_enumset1(A_93,C_94,B_95,D_96) = k2_enumset1(A_93,B_95,C_94,D_96) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_60,B_61,C_62] : k2_enumset1(A_60,A_60,B_61,C_62) = k1_enumset1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_332,plain,(
    ! [B_97,C_98,D_99] : k2_enumset1(B_97,C_98,B_97,D_99) = k1_enumset1(B_97,C_98,D_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_34])).

tff(c_16,plain,(
    ! [A_20,D_23,C_22,B_21] : k2_enumset1(A_20,D_23,C_22,B_21) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1002,plain,(
    ! [B_125,D_126,C_127] : k2_enumset1(B_125,D_126,B_125,C_127) = k1_enumset1(B_125,C_127,D_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_16])).

tff(c_283,plain,(
    ! [B_95,C_94,D_96] : k2_enumset1(B_95,C_94,B_95,D_96) = k1_enumset1(B_95,C_94,D_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_34])).

tff(c_1028,plain,(
    ! [B_125,D_126,C_127] : k1_enumset1(B_125,D_126,C_127) = k1_enumset1(B_125,C_127,D_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_283])).

tff(c_14,plain,(
    ! [A_16,C_18,B_17,D_19] : k2_enumset1(A_16,C_18,B_17,D_19) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [D_31,C_30,B_29,A_28] : k2_enumset1(D_31,C_30,B_29,A_28) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_42,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14,c_20,c_41])).

tff(c_1119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  
% 2.79/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  %$ k7_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.79/1.44  
% 2.79/1.44  %Foreground sorts:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Background operators:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Foreground operators:
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.79/1.44  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.79/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.44  
% 2.79/1.45  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 2.79/1.45  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.79/1.45  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.79/1.45  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 2.79/1.45  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.79/1.45  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 2.79/1.45  tff(c_247, plain, (![A_93, C_94, B_95, D_96]: (k2_enumset1(A_93, C_94, B_95, D_96)=k2_enumset1(A_93, B_95, C_94, D_96))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.45  tff(c_34, plain, (![A_60, B_61, C_62]: (k2_enumset1(A_60, A_60, B_61, C_62)=k1_enumset1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_332, plain, (![B_97, C_98, D_99]: (k2_enumset1(B_97, C_98, B_97, D_99)=k1_enumset1(B_97, C_98, D_99))), inference(superposition, [status(thm), theory('equality')], [c_247, c_34])).
% 2.79/1.45  tff(c_16, plain, (![A_20, D_23, C_22, B_21]: (k2_enumset1(A_20, D_23, C_22, B_21)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.79/1.45  tff(c_1002, plain, (![B_125, D_126, C_127]: (k2_enumset1(B_125, D_126, B_125, C_127)=k1_enumset1(B_125, C_127, D_126))), inference(superposition, [status(thm), theory('equality')], [c_332, c_16])).
% 2.79/1.45  tff(c_283, plain, (![B_95, C_94, D_96]: (k2_enumset1(B_95, C_94, B_95, D_96)=k1_enumset1(B_95, C_94, D_96))), inference(superposition, [status(thm), theory('equality')], [c_247, c_34])).
% 2.79/1.45  tff(c_1028, plain, (![B_125, D_126, C_127]: (k1_enumset1(B_125, D_126, C_127)=k1_enumset1(B_125, C_127, D_126))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_283])).
% 2.79/1.45  tff(c_14, plain, (![A_16, C_18, B_17, D_19]: (k2_enumset1(A_16, C_18, B_17, D_19)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.45  tff(c_20, plain, (![D_31, C_30, B_29, A_28]: (k2_enumset1(D_31, C_30, B_29, A_28)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.45  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.45  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.79/1.45  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 2.79/1.45  tff(c_42, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14, c_20, c_41])).
% 2.79/1.45  tff(c_1119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1028, c_42])).
% 2.79/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  Inference rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Ref     : 0
% 2.79/1.45  #Sup     : 276
% 2.79/1.45  #Fact    : 0
% 2.79/1.45  #Define  : 0
% 2.79/1.45  #Split   : 0
% 2.79/1.45  #Chain   : 0
% 2.79/1.45  #Close   : 0
% 2.79/1.45  
% 2.79/1.45  Ordering : KBO
% 2.79/1.45  
% 2.79/1.45  Simplification rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Subsume      : 9
% 2.79/1.45  #Demod        : 98
% 2.79/1.45  #Tautology    : 141
% 2.79/1.45  #SimpNegUnit  : 0
% 2.79/1.45  #BackRed      : 1
% 2.79/1.45  
% 2.79/1.45  #Partial instantiations: 0
% 2.79/1.45  #Strategies tried      : 1
% 2.79/1.45  
% 2.79/1.45  Timing (in seconds)
% 2.79/1.45  ----------------------
% 2.79/1.45  Preprocessing        : 0.33
% 2.79/1.45  Parsing              : 0.18
% 2.79/1.45  CNF conversion       : 0.02
% 2.79/1.45  Main loop            : 0.35
% 2.79/1.45  Inferencing          : 0.12
% 2.79/1.45  Reduction            : 0.14
% 2.79/1.45  Demodulation         : 0.12
% 2.79/1.45  BG Simplification    : 0.03
% 2.79/1.45  Subsumption          : 0.05
% 2.79/1.45  Abstraction          : 0.02
% 2.79/1.45  MUC search           : 0.00
% 2.79/1.45  Cooper               : 0.00
% 2.79/1.45  Total                : 0.70
% 2.79/1.45  Index Insertion      : 0.00
% 2.79/1.45  Index Deletion       : 0.00
% 2.79/1.45  Index Matching       : 0.00
% 2.79/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
