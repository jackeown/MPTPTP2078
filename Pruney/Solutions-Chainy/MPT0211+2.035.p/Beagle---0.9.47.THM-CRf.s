%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:19 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  41 expanded)
%              Number of equality atoms :   21 (  40 expanded)
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

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

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

tff(c_119,plain,(
    ! [B_77,D_78,C_79,A_80] : k2_enumset1(B_77,D_78,C_79,A_80) = k2_enumset1(A_80,B_77,C_79,D_78) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_574,plain,(
    ! [C_103,A_104,B_105] : k2_enumset1(C_103,A_104,B_105,A_104) = k1_enumset1(A_104,B_105,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_119])).

tff(c_197,plain,(
    ! [C_84,B_85,D_86,A_87] : k2_enumset1(C_84,B_85,D_86,A_87) = k2_enumset1(A_87,B_85,C_84,D_86) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_273,plain,(
    ! [B_59,A_58,C_60] : k2_enumset1(B_59,A_58,C_60,A_58) = k1_enumset1(A_58,B_59,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_197])).

tff(c_584,plain,(
    ! [A_104,C_103,B_105] : k1_enumset1(A_104,C_103,B_105) = k1_enumset1(A_104,B_105,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_273])).

tff(c_135,plain,(
    ! [B_77,D_78,C_79] : k2_enumset1(B_77,D_78,C_79,B_77) = k1_enumset1(B_77,C_79,D_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_34])).

tff(c_217,plain,(
    ! [A_87,B_85,D_86] : k2_enumset1(A_87,B_85,A_87,D_86) = k1_enumset1(A_87,D_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_135])).

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

tff(c_651,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_40])).

tff(c_1747,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_651])).

tff(c_1750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_1747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  
% 3.09/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  %$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.09/1.52  
% 3.09/1.52  %Foreground sorts:
% 3.09/1.52  
% 3.09/1.52  
% 3.09/1.52  %Background operators:
% 3.09/1.52  
% 3.09/1.52  
% 3.09/1.52  %Foreground operators:
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.52  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.09/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.52  
% 3.09/1.53  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.09/1.53  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 3.09/1.53  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_enumset1)).
% 3.09/1.53  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.09/1.53  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.09/1.53  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.09/1.53  tff(c_34, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.09/1.53  tff(c_119, plain, (![B_77, D_78, C_79, A_80]: (k2_enumset1(B_77, D_78, C_79, A_80)=k2_enumset1(A_80, B_77, C_79, D_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.53  tff(c_574, plain, (![C_103, A_104, B_105]: (k2_enumset1(C_103, A_104, B_105, A_104)=k1_enumset1(A_104, B_105, C_103))), inference(superposition, [status(thm), theory('equality')], [c_34, c_119])).
% 3.09/1.53  tff(c_197, plain, (![C_84, B_85, D_86, A_87]: (k2_enumset1(C_84, B_85, D_86, A_87)=k2_enumset1(A_87, B_85, C_84, D_86))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.53  tff(c_273, plain, (![B_59, A_58, C_60]: (k2_enumset1(B_59, A_58, C_60, A_58)=k1_enumset1(A_58, B_59, C_60))), inference(superposition, [status(thm), theory('equality')], [c_34, c_197])).
% 3.09/1.53  tff(c_584, plain, (![A_104, C_103, B_105]: (k1_enumset1(A_104, C_103, B_105)=k1_enumset1(A_104, B_105, C_103))), inference(superposition, [status(thm), theory('equality')], [c_574, c_273])).
% 3.09/1.53  tff(c_135, plain, (![B_77, D_78, C_79]: (k2_enumset1(B_77, D_78, C_79, B_77)=k1_enumset1(B_77, C_79, D_78))), inference(superposition, [status(thm), theory('equality')], [c_119, c_34])).
% 3.09/1.53  tff(c_217, plain, (![A_87, B_85, D_86]: (k2_enumset1(A_87, B_85, A_87, D_86)=k1_enumset1(A_87, D_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_197, c_135])).
% 3.09/1.53  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.53  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.09/1.53  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.53  tff(c_39, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 3.09/1.53  tff(c_40, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_39])).
% 3.09/1.53  tff(c_651, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_584, c_40])).
% 3.09/1.53  tff(c_1747, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_651])).
% 3.09/1.53  tff(c_1750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_1747])).
% 3.09/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.53  
% 3.09/1.53  Inference rules
% 3.09/1.53  ----------------------
% 3.09/1.53  #Ref     : 0
% 3.09/1.53  #Sup     : 420
% 3.09/1.53  #Fact    : 0
% 3.09/1.53  #Define  : 0
% 3.09/1.53  #Split   : 0
% 3.09/1.53  #Chain   : 0
% 3.09/1.53  #Close   : 0
% 3.09/1.53  
% 3.09/1.53  Ordering : KBO
% 3.09/1.53  
% 3.09/1.53  Simplification rules
% 3.09/1.53  ----------------------
% 3.09/1.53  #Subsume      : 32
% 3.09/1.53  #Demod        : 234
% 3.09/1.53  #Tautology    : 247
% 3.09/1.53  #SimpNegUnit  : 0
% 3.09/1.53  #BackRed      : 2
% 3.09/1.53  
% 3.09/1.53  #Partial instantiations: 0
% 3.09/1.53  #Strategies tried      : 1
% 3.09/1.53  
% 3.09/1.53  Timing (in seconds)
% 3.09/1.53  ----------------------
% 3.15/1.53  Preprocessing        : 0.30
% 3.15/1.53  Parsing              : 0.16
% 3.15/1.53  CNF conversion       : 0.02
% 3.15/1.53  Main loop            : 0.43
% 3.15/1.53  Inferencing          : 0.15
% 3.15/1.53  Reduction            : 0.18
% 3.15/1.53  Demodulation         : 0.15
% 3.15/1.53  BG Simplification    : 0.03
% 3.15/1.53  Subsumption          : 0.05
% 3.15/1.53  Abstraction          : 0.03
% 3.15/1.53  MUC search           : 0.00
% 3.15/1.53  Cooper               : 0.00
% 3.15/1.53  Total                : 0.75
% 3.15/1.54  Index Insertion      : 0.00
% 3.15/1.54  Index Deletion       : 0.00
% 3.15/1.54  Index Matching       : 0.00
% 3.15/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
