%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:53 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   39 (  86 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  70 expanded)
%              Number of equality atoms :   22 (  69 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_4,plain,(
    ! [B_10,C_11,A_9] : k1_enumset1(B_10,C_11,A_9) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_44,B_45,C_46,D_47] : k3_enumset1(A_44,A_44,B_45,C_46,D_47) = k2_enumset1(A_44,B_45,C_46,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_41,B_42,C_43] : k2_enumset1(A_41,A_41,B_42,C_43) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [B_49,A_48,D_51,E_52,C_50] : k4_enumset1(A_48,A_48,B_49,C_50,D_51,E_52) = k3_enumset1(A_48,B_49,C_50,D_51,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_300,plain,(
    ! [F_101,B_102,A_104,C_106,D_105,E_103] : k2_xboole_0(k3_enumset1(A_104,B_102,C_106,D_105,E_103),k1_tarski(F_101)) = k4_enumset1(A_104,B_102,C_106,D_105,E_103,F_101) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_309,plain,(
    ! [C_46,F_101,A_44,B_45,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,F_101) = k2_xboole_0(k2_enumset1(A_44,B_45,C_46,D_47),k1_tarski(F_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_300])).

tff(c_313,plain,(
    ! [C_108,B_110,A_111,F_109,D_107] : k2_xboole_0(k2_enumset1(A_111,B_110,C_108,D_107),k1_tarski(F_109)) = k3_enumset1(A_111,B_110,C_108,D_107,F_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_309])).

tff(c_331,plain,(
    ! [A_41,B_42,C_43,F_109] : k3_enumset1(A_41,A_41,B_42,C_43,F_109) = k2_xboole_0(k1_enumset1(A_41,B_42,C_43),k1_tarski(F_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_313])).

tff(c_335,plain,(
    ! [A_112,B_113,C_114,F_115] : k2_xboole_0(k1_enumset1(A_112,B_113,C_114),k1_tarski(F_115)) = k2_enumset1(A_112,B_113,C_114,F_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_331])).

tff(c_450,plain,(
    ! [B_135,C_136,A_137,F_138] : k2_xboole_0(k1_enumset1(B_135,C_136,A_137),k1_tarski(F_138)) = k2_enumset1(A_137,B_135,C_136,F_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_335])).

tff(c_334,plain,(
    ! [A_41,B_42,C_43,F_109] : k2_xboole_0(k1_enumset1(A_41,B_42,C_43),k1_tarski(F_109)) = k2_enumset1(A_41,B_42,C_43,F_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_331])).

tff(c_456,plain,(
    ! [B_135,C_136,A_137,F_138] : k2_enumset1(B_135,C_136,A_137,F_138) = k2_enumset1(A_137,B_135,C_136,F_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_334])).

tff(c_6,plain,(
    ! [A_12,C_14,B_13,D_15] : k2_enumset1(A_12,C_14,B_13,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.28  
% 2.17/1.28  %Foreground sorts:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Background operators:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Foreground operators:
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.28  
% 2.17/1.29  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 2.17/1.29  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.17/1.29  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.17/1.29  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.17/1.29  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.17/1.29  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 2.17/1.29  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 2.17/1.29  tff(c_4, plain, (![B_10, C_11, A_9]: (k1_enumset1(B_10, C_11, A_9)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.29  tff(c_20, plain, (![A_44, B_45, C_46, D_47]: (k3_enumset1(A_44, A_44, B_45, C_46, D_47)=k2_enumset1(A_44, B_45, C_46, D_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.29  tff(c_18, plain, (![A_41, B_42, C_43]: (k2_enumset1(A_41, A_41, B_42, C_43)=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.29  tff(c_22, plain, (![B_49, A_48, D_51, E_52, C_50]: (k4_enumset1(A_48, A_48, B_49, C_50, D_51, E_52)=k3_enumset1(A_48, B_49, C_50, D_51, E_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.29  tff(c_300, plain, (![F_101, B_102, A_104, C_106, D_105, E_103]: (k2_xboole_0(k3_enumset1(A_104, B_102, C_106, D_105, E_103), k1_tarski(F_101))=k4_enumset1(A_104, B_102, C_106, D_105, E_103, F_101))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.29  tff(c_309, plain, (![C_46, F_101, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, F_101)=k2_xboole_0(k2_enumset1(A_44, B_45, C_46, D_47), k1_tarski(F_101)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_300])).
% 2.17/1.29  tff(c_313, plain, (![C_108, B_110, A_111, F_109, D_107]: (k2_xboole_0(k2_enumset1(A_111, B_110, C_108, D_107), k1_tarski(F_109))=k3_enumset1(A_111, B_110, C_108, D_107, F_109))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_309])).
% 2.17/1.29  tff(c_331, plain, (![A_41, B_42, C_43, F_109]: (k3_enumset1(A_41, A_41, B_42, C_43, F_109)=k2_xboole_0(k1_enumset1(A_41, B_42, C_43), k1_tarski(F_109)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_313])).
% 2.17/1.29  tff(c_335, plain, (![A_112, B_113, C_114, F_115]: (k2_xboole_0(k1_enumset1(A_112, B_113, C_114), k1_tarski(F_115))=k2_enumset1(A_112, B_113, C_114, F_115))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_331])).
% 2.17/1.29  tff(c_450, plain, (![B_135, C_136, A_137, F_138]: (k2_xboole_0(k1_enumset1(B_135, C_136, A_137), k1_tarski(F_138))=k2_enumset1(A_137, B_135, C_136, F_138))), inference(superposition, [status(thm), theory('equality')], [c_4, c_335])).
% 2.17/1.29  tff(c_334, plain, (![A_41, B_42, C_43, F_109]: (k2_xboole_0(k1_enumset1(A_41, B_42, C_43), k1_tarski(F_109))=k2_enumset1(A_41, B_42, C_43, F_109))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_331])).
% 2.17/1.29  tff(c_456, plain, (![B_135, C_136, A_137, F_138]: (k2_enumset1(B_135, C_136, A_137, F_138)=k2_enumset1(A_137, B_135, C_136, F_138))), inference(superposition, [status(thm), theory('equality')], [c_450, c_334])).
% 2.17/1.29  tff(c_6, plain, (![A_12, C_14, B_13, D_15]: (k2_enumset1(A_12, C_14, B_13, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.29  tff(c_28, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.29  tff(c_29, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 2.17/1.29  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_29])).
% 2.17/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  Inference rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Ref     : 0
% 2.17/1.29  #Sup     : 115
% 2.17/1.29  #Fact    : 0
% 2.17/1.29  #Define  : 0
% 2.17/1.29  #Split   : 0
% 2.17/1.29  #Chain   : 0
% 2.17/1.29  #Close   : 0
% 2.17/1.29  
% 2.17/1.29  Ordering : KBO
% 2.17/1.29  
% 2.17/1.29  Simplification rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Subsume      : 4
% 2.17/1.29  #Demod        : 65
% 2.17/1.29  #Tautology    : 86
% 2.17/1.29  #SimpNegUnit  : 0
% 2.17/1.29  #BackRed      : 1
% 2.17/1.29  
% 2.17/1.29  #Partial instantiations: 0
% 2.17/1.29  #Strategies tried      : 1
% 2.17/1.29  
% 2.17/1.29  Timing (in seconds)
% 2.17/1.29  ----------------------
% 2.17/1.30  Preprocessing        : 0.31
% 2.17/1.30  Parsing              : 0.17
% 2.17/1.30  CNF conversion       : 0.02
% 2.17/1.30  Main loop            : 0.23
% 2.17/1.30  Inferencing          : 0.09
% 2.17/1.30  Reduction            : 0.09
% 2.17/1.30  Demodulation         : 0.08
% 2.17/1.30  BG Simplification    : 0.02
% 2.17/1.30  Subsumption          : 0.03
% 2.17/1.30  Abstraction          : 0.02
% 2.17/1.30  MUC search           : 0.00
% 2.17/1.30  Cooper               : 0.00
% 2.17/1.30  Total                : 0.57
% 2.17/1.30  Index Insertion      : 0.00
% 2.17/1.30  Index Deletion       : 0.00
% 2.17/1.30  Index Matching       : 0.00
% 2.17/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
