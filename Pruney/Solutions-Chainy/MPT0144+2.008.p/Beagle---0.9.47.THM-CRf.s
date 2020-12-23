%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:52 EST 2020

% Result     : Theorem 6.08s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :   50 (  64 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   30 (  44 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,G_21,E_19,F_20,C_17] : k2_xboole_0(k2_enumset1(A_15,B_16,C_17,D_18),k1_enumset1(E_19,F_20,G_21)) = k5_enumset1(A_15,B_16,C_17,D_18,E_19,F_20,G_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k1_tarski(A_24),k2_tarski(B_25,C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_269,plain,(
    ! [A_74,E_73,C_75,B_72,D_71] : k2_xboole_0(k1_tarski(A_74),k2_enumset1(B_72,C_75,D_71,E_73)) = k3_enumset1(A_74,B_72,C_75,D_71,E_73) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_278,plain,(
    ! [A_74,E_73,C_75,B_72,C_5,D_71] : k2_xboole_0(k1_tarski(A_74),k2_xboole_0(k2_enumset1(B_72,C_75,D_71,E_73),C_5)) = k2_xboole_0(k3_enumset1(A_74,B_72,C_75,D_71,E_73),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_4])).

tff(c_18,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_xboole_0(k1_tarski(A_27),k1_enumset1(B_28,C_29,D_30)) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    ! [A_48,B_49,C_50] : k2_xboole_0(k2_xboole_0(A_48,B_49),C_50) = k2_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_227,plain,(
    ! [A_65,B_66,C_67] : k2_xboole_0(k1_tarski(A_65),k2_xboole_0(k1_tarski(B_66),C_67)) = k2_xboole_0(k2_tarski(A_65,B_66),C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_98])).

tff(c_251,plain,(
    ! [A_65,A_22,B_23] : k2_xboole_0(k2_tarski(A_65,A_22),k1_tarski(B_23)) = k2_xboole_0(k1_tarski(A_65),k2_tarski(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_227])).

tff(c_256,plain,(
    ! [A_65,A_22,B_23] : k2_xboole_0(k2_tarski(A_65,A_22),k1_tarski(B_23)) = k1_enumset1(A_65,A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_251])).

tff(c_472,plain,(
    ! [A_89,B_90,C_91,C_92] : k2_xboole_0(k1_tarski(A_89),k2_xboole_0(k2_tarski(B_90,C_91),C_92)) = k2_xboole_0(k1_enumset1(A_89,B_90,C_91),C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_98])).

tff(c_487,plain,(
    ! [A_89,A_65,A_22,B_23] : k2_xboole_0(k1_enumset1(A_89,A_65,A_22),k1_tarski(B_23)) = k2_xboole_0(k1_tarski(A_89),k1_enumset1(A_65,A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_472])).

tff(c_496,plain,(
    ! [A_93,A_94,A_95,B_96] : k2_xboole_0(k1_enumset1(A_93,A_94,A_95),k1_tarski(B_96)) = k2_enumset1(A_93,A_94,A_95,B_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_487])).

tff(c_1366,plain,(
    ! [B_161,C_163,A_159,A_160,A_162] : k2_xboole_0(k1_enumset1(A_162,A_159,A_160),k2_xboole_0(k1_tarski(B_161),C_163)) = k2_xboole_0(k2_enumset1(A_162,A_159,A_160,B_161),C_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_4])).

tff(c_133,plain,(
    ! [A_55,B_56,C_57,D_58] : k2_xboole_0(k1_tarski(A_55),k1_enumset1(B_56,C_57,D_58)) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    ! [B_56,C_57,A_55,C_5,D_58] : k2_xboole_0(k1_tarski(A_55),k2_xboole_0(k1_enumset1(B_56,C_57,D_58),C_5)) = k2_xboole_0(k2_enumset1(A_55,B_56,C_57,D_58),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_4])).

tff(c_1390,plain,(
    ! [B_161,C_163,A_159,A_160,A_55,A_162] : k2_xboole_0(k2_enumset1(A_55,A_162,A_159,A_160),k2_xboole_0(k1_tarski(B_161),C_163)) = k2_xboole_0(k1_tarski(A_55),k2_xboole_0(k2_enumset1(A_162,A_159,A_160,B_161),C_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_139])).

tff(c_2990,plain,(
    ! [A_235,C_230,A_233,A_234,A_232,B_231] : k2_xboole_0(k2_enumset1(A_232,A_233,A_234,A_235),k2_xboole_0(k1_tarski(B_231),C_230)) = k2_xboole_0(k3_enumset1(A_232,A_233,A_234,A_235,B_231),C_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_1390])).

tff(c_3056,plain,(
    ! [A_24,A_235,B_25,A_233,A_234,C_26,A_232] : k2_xboole_0(k3_enumset1(A_232,A_233,A_234,A_235,A_24),k2_tarski(B_25,C_26)) = k2_xboole_0(k2_enumset1(A_232,A_233,A_234,A_235),k1_enumset1(A_24,B_25,C_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2990])).

tff(c_3070,plain,(
    ! [A_24,A_235,B_25,A_233,A_234,C_26,A_232] : k2_xboole_0(k3_enumset1(A_232,A_233,A_234,A_235,A_24),k2_tarski(B_25,C_26)) = k5_enumset1(A_232,A_233,A_234,A_235,A_24,B_25,C_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3056])).

tff(c_22,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3070,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.08/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.34  
% 6.08/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.34  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.08/2.34  
% 6.08/2.34  %Foreground sorts:
% 6.08/2.34  
% 6.08/2.34  
% 6.08/2.34  %Background operators:
% 6.08/2.34  
% 6.08/2.34  
% 6.08/2.34  %Foreground operators:
% 6.08/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.08/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.08/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.08/2.34  tff('#skF_7', type, '#skF_7': $i).
% 6.08/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.08/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.08/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.08/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.08/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.08/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.08/2.34  tff('#skF_2', type, '#skF_2': $i).
% 6.08/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.08/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.08/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.08/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.08/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.08/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.08/2.34  
% 6.08/2.35  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 6.08/2.35  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 6.08/2.35  tff(f_45, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 6.08/2.35  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.08/2.35  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 6.08/2.35  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 6.08/2.35  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 6.08/2.35  tff(c_12, plain, (![B_16, A_15, D_18, G_21, E_19, F_20, C_17]: (k2_xboole_0(k2_enumset1(A_15, B_16, C_17, D_18), k1_enumset1(E_19, F_20, G_21))=k5_enumset1(A_15, B_16, C_17, D_18, E_19, F_20, G_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.08/2.35  tff(c_16, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(B_25, C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.08/2.35  tff(c_269, plain, (![A_74, E_73, C_75, B_72, D_71]: (k2_xboole_0(k1_tarski(A_74), k2_enumset1(B_72, C_75, D_71, E_73))=k3_enumset1(A_74, B_72, C_75, D_71, E_73))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.08/2.35  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.08/2.35  tff(c_278, plain, (![A_74, E_73, C_75, B_72, C_5, D_71]: (k2_xboole_0(k1_tarski(A_74), k2_xboole_0(k2_enumset1(B_72, C_75, D_71, E_73), C_5))=k2_xboole_0(k3_enumset1(A_74, B_72, C_75, D_71, E_73), C_5))), inference(superposition, [status(thm), theory('equality')], [c_269, c_4])).
% 6.08/2.35  tff(c_18, plain, (![A_27, B_28, C_29, D_30]: (k2_xboole_0(k1_tarski(A_27), k1_enumset1(B_28, C_29, D_30))=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.08/2.35  tff(c_14, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.08/2.35  tff(c_98, plain, (![A_48, B_49, C_50]: (k2_xboole_0(k2_xboole_0(A_48, B_49), C_50)=k2_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.08/2.35  tff(c_227, plain, (![A_65, B_66, C_67]: (k2_xboole_0(k1_tarski(A_65), k2_xboole_0(k1_tarski(B_66), C_67))=k2_xboole_0(k2_tarski(A_65, B_66), C_67))), inference(superposition, [status(thm), theory('equality')], [c_14, c_98])).
% 6.08/2.35  tff(c_251, plain, (![A_65, A_22, B_23]: (k2_xboole_0(k2_tarski(A_65, A_22), k1_tarski(B_23))=k2_xboole_0(k1_tarski(A_65), k2_tarski(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_227])).
% 6.08/2.35  tff(c_256, plain, (![A_65, A_22, B_23]: (k2_xboole_0(k2_tarski(A_65, A_22), k1_tarski(B_23))=k1_enumset1(A_65, A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_251])).
% 6.08/2.35  tff(c_472, plain, (![A_89, B_90, C_91, C_92]: (k2_xboole_0(k1_tarski(A_89), k2_xboole_0(k2_tarski(B_90, C_91), C_92))=k2_xboole_0(k1_enumset1(A_89, B_90, C_91), C_92))), inference(superposition, [status(thm), theory('equality')], [c_16, c_98])).
% 6.08/2.35  tff(c_487, plain, (![A_89, A_65, A_22, B_23]: (k2_xboole_0(k1_enumset1(A_89, A_65, A_22), k1_tarski(B_23))=k2_xboole_0(k1_tarski(A_89), k1_enumset1(A_65, A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_472])).
% 6.08/2.35  tff(c_496, plain, (![A_93, A_94, A_95, B_96]: (k2_xboole_0(k1_enumset1(A_93, A_94, A_95), k1_tarski(B_96))=k2_enumset1(A_93, A_94, A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_487])).
% 6.08/2.35  tff(c_1366, plain, (![B_161, C_163, A_159, A_160, A_162]: (k2_xboole_0(k1_enumset1(A_162, A_159, A_160), k2_xboole_0(k1_tarski(B_161), C_163))=k2_xboole_0(k2_enumset1(A_162, A_159, A_160, B_161), C_163))), inference(superposition, [status(thm), theory('equality')], [c_496, c_4])).
% 6.08/2.35  tff(c_133, plain, (![A_55, B_56, C_57, D_58]: (k2_xboole_0(k1_tarski(A_55), k1_enumset1(B_56, C_57, D_58))=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.08/2.35  tff(c_139, plain, (![B_56, C_57, A_55, C_5, D_58]: (k2_xboole_0(k1_tarski(A_55), k2_xboole_0(k1_enumset1(B_56, C_57, D_58), C_5))=k2_xboole_0(k2_enumset1(A_55, B_56, C_57, D_58), C_5))), inference(superposition, [status(thm), theory('equality')], [c_133, c_4])).
% 6.08/2.35  tff(c_1390, plain, (![B_161, C_163, A_159, A_160, A_55, A_162]: (k2_xboole_0(k2_enumset1(A_55, A_162, A_159, A_160), k2_xboole_0(k1_tarski(B_161), C_163))=k2_xboole_0(k1_tarski(A_55), k2_xboole_0(k2_enumset1(A_162, A_159, A_160, B_161), C_163)))), inference(superposition, [status(thm), theory('equality')], [c_1366, c_139])).
% 6.08/2.35  tff(c_2990, plain, (![A_235, C_230, A_233, A_234, A_232, B_231]: (k2_xboole_0(k2_enumset1(A_232, A_233, A_234, A_235), k2_xboole_0(k1_tarski(B_231), C_230))=k2_xboole_0(k3_enumset1(A_232, A_233, A_234, A_235, B_231), C_230))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_1390])).
% 6.08/2.35  tff(c_3056, plain, (![A_24, A_235, B_25, A_233, A_234, C_26, A_232]: (k2_xboole_0(k3_enumset1(A_232, A_233, A_234, A_235, A_24), k2_tarski(B_25, C_26))=k2_xboole_0(k2_enumset1(A_232, A_233, A_234, A_235), k1_enumset1(A_24, B_25, C_26)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2990])).
% 6.08/2.35  tff(c_3070, plain, (![A_24, A_235, B_25, A_233, A_234, C_26, A_232]: (k2_xboole_0(k3_enumset1(A_232, A_233, A_234, A_235, A_24), k2_tarski(B_25, C_26))=k5_enumset1(A_232, A_233, A_234, A_235, A_24, B_25, C_26))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3056])).
% 6.08/2.35  tff(c_22, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.08/2.35  tff(c_3683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3070, c_22])).
% 6.08/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.35  
% 6.08/2.35  Inference rules
% 6.08/2.35  ----------------------
% 6.08/2.35  #Ref     : 0
% 6.08/2.35  #Sup     : 928
% 6.08/2.35  #Fact    : 0
% 6.08/2.35  #Define  : 0
% 6.08/2.35  #Split   : 0
% 6.08/2.35  #Chain   : 0
% 6.08/2.35  #Close   : 0
% 6.08/2.35  
% 6.08/2.35  Ordering : KBO
% 6.08/2.35  
% 6.08/2.35  Simplification rules
% 6.08/2.35  ----------------------
% 6.08/2.35  #Subsume      : 0
% 6.08/2.35  #Demod        : 1399
% 6.08/2.35  #Tautology    : 389
% 6.08/2.35  #SimpNegUnit  : 0
% 6.08/2.35  #BackRed      : 1
% 6.08/2.35  
% 6.08/2.35  #Partial instantiations: 0
% 6.08/2.35  #Strategies tried      : 1
% 6.08/2.35  
% 6.08/2.35  Timing (in seconds)
% 6.08/2.35  ----------------------
% 6.08/2.35  Preprocessing        : 0.28
% 6.08/2.35  Parsing              : 0.16
% 6.08/2.35  CNF conversion       : 0.02
% 6.08/2.36  Main loop            : 1.31
% 6.08/2.36  Inferencing          : 0.46
% 6.08/2.36  Reduction            : 0.60
% 6.08/2.36  Demodulation         : 0.53
% 6.08/2.36  BG Simplification    : 0.08
% 6.08/2.36  Subsumption          : 0.11
% 6.08/2.36  Abstraction          : 0.13
% 6.08/2.36  MUC search           : 0.00
% 6.08/2.36  Cooper               : 0.00
% 6.08/2.36  Total                : 1.61
% 6.08/2.36  Index Insertion      : 0.00
% 6.08/2.36  Index Deletion       : 0.00
% 6.08/2.36  Index Matching       : 0.00
% 6.08/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
