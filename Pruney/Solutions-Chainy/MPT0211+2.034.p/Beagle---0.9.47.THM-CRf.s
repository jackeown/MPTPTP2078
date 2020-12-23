%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:19 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  30 expanded)
%              Number of equality atoms :   20 (  29 expanded)
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

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_45,axiom,(
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

tff(c_711,plain,(
    ! [A_107,C_108,D_109,B_110] : k2_enumset1(A_107,C_108,D_109,B_110) = k2_enumset1(A_107,B_110,C_108,D_109) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_884,plain,(
    ! [B_115,C_116,D_117] : k2_enumset1(B_115,C_116,D_117,B_115) = k1_enumset1(B_115,C_116,D_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_34])).

tff(c_119,plain,(
    ! [A_77,D_78,C_79,B_80] : k2_enumset1(A_77,D_78,C_79,B_80) = k2_enumset1(A_77,B_80,C_79,D_78) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [B_80,D_78,C_79] : k2_enumset1(B_80,D_78,C_79,B_80) = k1_enumset1(B_80,C_79,D_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_34])).

tff(c_916,plain,(
    ! [B_115,D_117,C_116] : k1_enumset1(B_115,D_117,C_116) = k1_enumset1(B_115,C_116,D_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_135])).

tff(c_16,plain,(
    ! [A_21,C_23,D_24,B_22] : k2_enumset1(A_21,C_23,D_24,B_22) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [B_30,D_32,C_31,A_29] : k2_enumset1(B_30,D_32,C_31,A_29) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

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
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16,c_16,c_20,c_22,c_16,c_39])).

tff(c_993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:17:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.40  
% 3.02/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.41  %$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.02/1.41  
% 3.02/1.41  %Foreground sorts:
% 3.02/1.41  
% 3.02/1.41  
% 3.02/1.41  %Background operators:
% 3.02/1.41  
% 3.02/1.41  
% 3.02/1.41  %Foreground operators:
% 3.02/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.41  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.41  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.41  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.41  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.41  
% 3.02/1.42  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 3.02/1.42  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.02/1.42  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 3.02/1.42  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 3.02/1.42  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.02/1.42  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.02/1.42  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.02/1.42  tff(c_711, plain, (![A_107, C_108, D_109, B_110]: (k2_enumset1(A_107, C_108, D_109, B_110)=k2_enumset1(A_107, B_110, C_108, D_109))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.42  tff(c_34, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.02/1.42  tff(c_884, plain, (![B_115, C_116, D_117]: (k2_enumset1(B_115, C_116, D_117, B_115)=k1_enumset1(B_115, C_116, D_117))), inference(superposition, [status(thm), theory('equality')], [c_711, c_34])).
% 3.02/1.42  tff(c_119, plain, (![A_77, D_78, C_79, B_80]: (k2_enumset1(A_77, D_78, C_79, B_80)=k2_enumset1(A_77, B_80, C_79, D_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.42  tff(c_135, plain, (![B_80, D_78, C_79]: (k2_enumset1(B_80, D_78, C_79, B_80)=k1_enumset1(B_80, C_79, D_78))), inference(superposition, [status(thm), theory('equality')], [c_119, c_34])).
% 3.02/1.42  tff(c_916, plain, (![B_115, D_117, C_116]: (k1_enumset1(B_115, D_117, C_116)=k1_enumset1(B_115, C_116, D_117))), inference(superposition, [status(thm), theory('equality')], [c_884, c_135])).
% 3.02/1.42  tff(c_16, plain, (![A_21, C_23, D_24, B_22]: (k2_enumset1(A_21, C_23, D_24, B_22)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.42  tff(c_20, plain, (![B_30, D_32, C_31, A_29]: (k2_enumset1(B_30, D_32, C_31, A_29)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.02/1.42  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.42  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.42  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.02/1.42  tff(c_39, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 3.02/1.42  tff(c_40, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16, c_16, c_20, c_22, c_16, c_39])).
% 3.02/1.42  tff(c_993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_916, c_40])).
% 3.02/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.42  
% 3.02/1.42  Inference rules
% 3.02/1.42  ----------------------
% 3.02/1.42  #Ref     : 0
% 3.02/1.42  #Sup     : 248
% 3.02/1.42  #Fact    : 0
% 3.02/1.42  #Define  : 0
% 3.02/1.42  #Split   : 0
% 3.02/1.42  #Chain   : 0
% 3.02/1.42  #Close   : 0
% 3.02/1.42  
% 3.02/1.42  Ordering : KBO
% 3.02/1.42  
% 3.02/1.42  Simplification rules
% 3.02/1.42  ----------------------
% 3.02/1.42  #Subsume      : 15
% 3.02/1.42  #Demod        : 72
% 3.02/1.42  #Tautology    : 120
% 3.02/1.42  #SimpNegUnit  : 0
% 3.02/1.42  #BackRed      : 1
% 3.02/1.42  
% 3.02/1.42  #Partial instantiations: 0
% 3.02/1.42  #Strategies tried      : 1
% 3.02/1.42  
% 3.02/1.42  Timing (in seconds)
% 3.02/1.42  ----------------------
% 3.02/1.42  Preprocessing        : 0.32
% 3.02/1.42  Parsing              : 0.18
% 3.02/1.42  CNF conversion       : 0.02
% 3.02/1.42  Main loop            : 0.35
% 3.02/1.42  Inferencing          : 0.12
% 3.02/1.42  Reduction            : 0.14
% 3.02/1.42  Demodulation         : 0.12
% 3.02/1.42  BG Simplification    : 0.02
% 3.02/1.42  Subsumption          : 0.05
% 3.02/1.42  Abstraction          : 0.02
% 3.02/1.42  MUC search           : 0.00
% 3.02/1.42  Cooper               : 0.00
% 3.02/1.42  Total                : 0.69
% 3.02/1.42  Index Insertion      : 0.00
% 3.02/1.42  Index Deletion       : 0.00
% 3.02/1.42  Index Matching       : 0.00
% 3.02/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
