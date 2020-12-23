%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:51 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_6,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k4_enumset1(A_17,A_17,B_18,C_19,D_20,E_21) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [C_46,D_44,A_47,E_43,F_42,B_45] : k2_xboole_0(k3_enumset1(A_47,B_45,C_46,D_44,E_43),k1_tarski(F_42)) = k4_enumset1(A_47,B_45,C_46,D_44,E_43,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_101,plain,(
    ! [A_13,F_42,B_14,C_15,D_16] : k4_enumset1(A_13,A_13,B_14,C_15,D_16,F_42) = k2_xboole_0(k2_enumset1(A_13,B_14,C_15,D_16),k1_tarski(F_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_105,plain,(
    ! [B_49,D_48,C_52,A_51,F_50] : k2_xboole_0(k2_enumset1(A_51,B_49,C_52,D_48),k1_tarski(F_50)) = k3_enumset1(A_51,B_49,C_52,D_48,F_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_101])).

tff(c_114,plain,(
    ! [A_10,B_11,C_12,F_50] : k3_enumset1(A_10,A_10,B_11,C_12,F_50) = k2_xboole_0(k1_enumset1(A_10,B_11,C_12),k1_tarski(F_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_118,plain,(
    ! [A_53,B_54,C_55,F_56] : k2_xboole_0(k1_enumset1(A_53,B_54,C_55),k1_tarski(F_56)) = k2_enumset1(A_53,B_54,C_55,F_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_127,plain,(
    ! [A_8,B_9,F_56] : k2_xboole_0(k2_tarski(A_8,B_9),k1_tarski(F_56)) = k2_enumset1(A_8,A_8,B_9,F_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_118])).

tff(c_131,plain,(
    ! [A_57,B_58,F_59] : k2_xboole_0(k2_tarski(A_57,B_58),k1_tarski(F_59)) = k1_enumset1(A_57,B_58,F_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_127])).

tff(c_140,plain,(
    ! [A_7,F_59] : k2_xboole_0(k1_tarski(A_7),k1_tarski(F_59)) = k1_enumset1(A_7,A_7,F_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_143,plain,(
    ! [A_7,F_59] : k2_xboole_0(k1_tarski(A_7),k1_tarski(F_59)) = k2_tarski(A_7,F_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_140])).

tff(c_14,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.52  
% 2.12/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.53  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.24/1.53  
% 2.24/1.53  %Foreground sorts:
% 2.24/1.53  
% 2.24/1.53  
% 2.24/1.53  %Background operators:
% 2.24/1.53  
% 2.24/1.53  
% 2.24/1.53  %Foreground operators:
% 2.24/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.24/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.53  
% 2.24/1.54  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.54  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/1.54  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.24/1.54  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.24/1.54  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.24/1.54  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.24/1.54  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.24/1.54  tff(f_42, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.24/1.54  tff(c_6, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.54  tff(c_4, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.54  tff(c_8, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.54  tff(c_10, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.54  tff(c_12, plain, (![E_21, D_20, C_19, B_18, A_17]: (k4_enumset1(A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.54  tff(c_92, plain, (![C_46, D_44, A_47, E_43, F_42, B_45]: (k2_xboole_0(k3_enumset1(A_47, B_45, C_46, D_44, E_43), k1_tarski(F_42))=k4_enumset1(A_47, B_45, C_46, D_44, E_43, F_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.54  tff(c_101, plain, (![A_13, F_42, B_14, C_15, D_16]: (k4_enumset1(A_13, A_13, B_14, C_15, D_16, F_42)=k2_xboole_0(k2_enumset1(A_13, B_14, C_15, D_16), k1_tarski(F_42)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_92])).
% 2.24/1.54  tff(c_105, plain, (![B_49, D_48, C_52, A_51, F_50]: (k2_xboole_0(k2_enumset1(A_51, B_49, C_52, D_48), k1_tarski(F_50))=k3_enumset1(A_51, B_49, C_52, D_48, F_50))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_101])).
% 2.24/1.54  tff(c_114, plain, (![A_10, B_11, C_12, F_50]: (k3_enumset1(A_10, A_10, B_11, C_12, F_50)=k2_xboole_0(k1_enumset1(A_10, B_11, C_12), k1_tarski(F_50)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_105])).
% 2.24/1.54  tff(c_118, plain, (![A_53, B_54, C_55, F_56]: (k2_xboole_0(k1_enumset1(A_53, B_54, C_55), k1_tarski(F_56))=k2_enumset1(A_53, B_54, C_55, F_56))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_114])).
% 2.24/1.54  tff(c_127, plain, (![A_8, B_9, F_56]: (k2_xboole_0(k2_tarski(A_8, B_9), k1_tarski(F_56))=k2_enumset1(A_8, A_8, B_9, F_56))), inference(superposition, [status(thm), theory('equality')], [c_6, c_118])).
% 2.24/1.54  tff(c_131, plain, (![A_57, B_58, F_59]: (k2_xboole_0(k2_tarski(A_57, B_58), k1_tarski(F_59))=k1_enumset1(A_57, B_58, F_59))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_127])).
% 2.24/1.54  tff(c_140, plain, (![A_7, F_59]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(F_59))=k1_enumset1(A_7, A_7, F_59))), inference(superposition, [status(thm), theory('equality')], [c_4, c_131])).
% 2.24/1.54  tff(c_143, plain, (![A_7, F_59]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(F_59))=k2_tarski(A_7, F_59))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_140])).
% 2.24/1.54  tff(c_14, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.54  tff(c_16, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.54  tff(c_17, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.24/1.54  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_17])).
% 2.24/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.54  
% 2.24/1.54  Inference rules
% 2.24/1.54  ----------------------
% 2.24/1.54  #Ref     : 0
% 2.24/1.54  #Sup     : 29
% 2.24/1.54  #Fact    : 0
% 2.24/1.54  #Define  : 0
% 2.24/1.54  #Split   : 0
% 2.24/1.54  #Chain   : 0
% 2.24/1.54  #Close   : 0
% 2.24/1.54  
% 2.24/1.54  Ordering : KBO
% 2.24/1.54  
% 2.24/1.54  Simplification rules
% 2.24/1.54  ----------------------
% 2.24/1.54  #Subsume      : 0
% 2.24/1.54  #Demod        : 6
% 2.24/1.54  #Tautology    : 24
% 2.24/1.54  #SimpNegUnit  : 0
% 2.24/1.54  #BackRed      : 1
% 2.24/1.54  
% 2.24/1.54  #Partial instantiations: 0
% 2.24/1.54  #Strategies tried      : 1
% 2.24/1.54  
% 2.24/1.54  Timing (in seconds)
% 2.24/1.54  ----------------------
% 2.24/1.55  Preprocessing        : 0.45
% 2.24/1.55  Parsing              : 0.23
% 2.29/1.55  CNF conversion       : 0.03
% 2.29/1.55  Main loop            : 0.19
% 2.29/1.55  Inferencing          : 0.08
% 2.29/1.55  Reduction            : 0.06
% 2.29/1.55  Demodulation         : 0.05
% 2.29/1.55  BG Simplification    : 0.02
% 2.29/1.55  Subsumption          : 0.02
% 2.29/1.55  Abstraction          : 0.02
% 2.29/1.55  MUC search           : 0.00
% 2.29/1.55  Cooper               : 0.00
% 2.29/1.55  Total                : 0.68
% 2.29/1.55  Index Insertion      : 0.00
% 2.29/1.55  Index Deletion       : 0.00
% 2.29/1.55  Index Matching       : 0.00
% 2.29/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
