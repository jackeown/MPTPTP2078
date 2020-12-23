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
% DateTime   : Thu Dec  3 09:47:48 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_10,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_19,B_20,C_21,D_22] : k3_enumset1(A_19,A_19,B_20,C_21,D_22) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : k4_enumset1(A_23,A_23,B_24,C_25,D_26,E_27) = k3_enumset1(A_23,B_24,C_25,D_26,E_27) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [C_70,E_73,F_72,D_68,B_69,A_71] : k2_xboole_0(k3_enumset1(A_71,B_69,C_70,D_68,E_73),k1_tarski(F_72)) = k4_enumset1(A_71,B_69,C_70,D_68,E_73,F_72) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    ! [D_74,C_75,A_78,E_79,F_77,B_76] : r1_tarski(k3_enumset1(A_78,B_76,C_75,D_74,E_79),k4_enumset1(A_78,B_76,C_75,D_74,E_79,F_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_4])).

tff(c_117,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : r1_tarski(k3_enumset1(A_23,A_23,B_24,C_25,D_26),k3_enumset1(A_23,B_24,C_25,D_26,E_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_114])).

tff(c_123,plain,(
    ! [C_80,B_82,E_81,D_83,A_84] : r1_tarski(k2_enumset1(A_84,B_82,C_80,D_83),k3_enumset1(A_84,B_82,C_80,D_83,E_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_117])).

tff(c_126,plain,(
    ! [A_19,B_20,C_21,D_22] : r1_tarski(k2_enumset1(A_19,A_19,B_20,C_21),k2_enumset1(A_19,B_20,C_21,D_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_123])).

tff(c_132,plain,(
    ! [A_85,B_86,C_87,D_88] : r1_tarski(k1_enumset1(A_85,B_86,C_87),k2_enumset1(A_85,B_86,C_87,D_88)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_126])).

tff(c_135,plain,(
    ! [A_16,B_17,C_18] : r1_tarski(k1_enumset1(A_16,A_16,B_17),k1_enumset1(A_16,B_17,C_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_132])).

tff(c_141,plain,(
    ! [A_89,B_90,C_91] : r1_tarski(k2_tarski(A_89,B_90),k1_enumset1(A_89,B_90,C_91)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_135])).

tff(c_144,plain,(
    ! [A_14,B_15] : r1_tarski(k2_tarski(A_14,A_14),k2_tarski(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_141])).

tff(c_148,plain,(
    ! [A_14,B_15] : r1_tarski(k1_tarski(A_14),k2_tarski(A_14,B_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_144])).

tff(c_24,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.17  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.85/1.17  
% 1.85/1.17  %Foreground sorts:
% 1.85/1.17  
% 1.85/1.17  
% 1.85/1.17  %Background operators:
% 1.85/1.17  
% 1.85/1.17  
% 1.85/1.17  %Foreground operators:
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.85/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.85/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.17  
% 1.94/1.18  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.94/1.18  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.94/1.18  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.94/1.18  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.94/1.18  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.94/1.18  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 1.94/1.18  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.94/1.18  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.94/1.18  tff(c_10, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.18  tff(c_12, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.18  tff(c_14, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.18  tff(c_16, plain, (![A_19, B_20, C_21, D_22]: (k3_enumset1(A_19, A_19, B_20, C_21, D_22)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.18  tff(c_18, plain, (![A_23, B_24, D_26, C_25, E_27]: (k4_enumset1(A_23, A_23, B_24, C_25, D_26, E_27)=k3_enumset1(A_23, B_24, C_25, D_26, E_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.18  tff(c_98, plain, (![C_70, E_73, F_72, D_68, B_69, A_71]: (k2_xboole_0(k3_enumset1(A_71, B_69, C_70, D_68, E_73), k1_tarski(F_72))=k4_enumset1(A_71, B_69, C_70, D_68, E_73, F_72))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.18  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.18  tff(c_114, plain, (![D_74, C_75, A_78, E_79, F_77, B_76]: (r1_tarski(k3_enumset1(A_78, B_76, C_75, D_74, E_79), k4_enumset1(A_78, B_76, C_75, D_74, E_79, F_77)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_4])).
% 1.94/1.18  tff(c_117, plain, (![A_23, B_24, D_26, C_25, E_27]: (r1_tarski(k3_enumset1(A_23, A_23, B_24, C_25, D_26), k3_enumset1(A_23, B_24, C_25, D_26, E_27)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_114])).
% 1.94/1.18  tff(c_123, plain, (![C_80, B_82, E_81, D_83, A_84]: (r1_tarski(k2_enumset1(A_84, B_82, C_80, D_83), k3_enumset1(A_84, B_82, C_80, D_83, E_81)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_117])).
% 1.94/1.18  tff(c_126, plain, (![A_19, B_20, C_21, D_22]: (r1_tarski(k2_enumset1(A_19, A_19, B_20, C_21), k2_enumset1(A_19, B_20, C_21, D_22)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_123])).
% 1.94/1.18  tff(c_132, plain, (![A_85, B_86, C_87, D_88]: (r1_tarski(k1_enumset1(A_85, B_86, C_87), k2_enumset1(A_85, B_86, C_87, D_88)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_126])).
% 1.94/1.18  tff(c_135, plain, (![A_16, B_17, C_18]: (r1_tarski(k1_enumset1(A_16, A_16, B_17), k1_enumset1(A_16, B_17, C_18)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_132])).
% 1.94/1.18  tff(c_141, plain, (![A_89, B_90, C_91]: (r1_tarski(k2_tarski(A_89, B_90), k1_enumset1(A_89, B_90, C_91)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_135])).
% 1.94/1.18  tff(c_144, plain, (![A_14, B_15]: (r1_tarski(k2_tarski(A_14, A_14), k2_tarski(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_141])).
% 1.94/1.18  tff(c_148, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), k2_tarski(A_14, B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_144])).
% 1.94/1.18  tff(c_24, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.94/1.18  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_24])).
% 1.94/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  Inference rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Ref     : 0
% 1.94/1.18  #Sup     : 30
% 1.94/1.18  #Fact    : 0
% 1.94/1.18  #Define  : 0
% 1.94/1.18  #Split   : 0
% 1.94/1.18  #Chain   : 0
% 1.94/1.18  #Close   : 0
% 1.94/1.18  
% 1.94/1.18  Ordering : KBO
% 1.94/1.18  
% 1.94/1.18  Simplification rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Subsume      : 0
% 1.94/1.18  #Demod        : 10
% 1.94/1.18  #Tautology    : 20
% 1.94/1.18  #SimpNegUnit  : 0
% 1.94/1.18  #BackRed      : 1
% 1.94/1.18  
% 1.94/1.18  #Partial instantiations: 0
% 1.94/1.18  #Strategies tried      : 1
% 1.94/1.18  
% 1.94/1.18  Timing (in seconds)
% 1.94/1.18  ----------------------
% 1.94/1.18  Preprocessing        : 0.29
% 1.94/1.18  Parsing              : 0.16
% 1.94/1.18  CNF conversion       : 0.02
% 1.94/1.18  Main loop            : 0.13
% 1.94/1.18  Inferencing          : 0.06
% 1.94/1.19  Reduction            : 0.04
% 1.94/1.19  Demodulation         : 0.03
% 1.94/1.19  BG Simplification    : 0.01
% 1.94/1.19  Subsumption          : 0.01
% 1.94/1.19  Abstraction          : 0.01
% 1.94/1.19  MUC search           : 0.00
% 1.94/1.19  Cooper               : 0.00
% 1.94/1.19  Total                : 0.45
% 1.94/1.19  Index Insertion      : 0.00
% 1.94/1.19  Index Deletion       : 0.00
% 1.94/1.19  Index Matching       : 0.00
% 1.94/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
