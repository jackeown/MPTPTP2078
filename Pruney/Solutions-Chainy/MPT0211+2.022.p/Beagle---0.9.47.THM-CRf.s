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
% DateTime   : Thu Dec  3 09:47:17 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :   54 (  77 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  59 expanded)
%              Number of equality atoms :   35 (  58 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_225,plain,(
    ! [A_94,C_95,D_96,B_97] : k2_enumset1(A_94,C_95,D_96,B_97) = k2_enumset1(A_94,B_97,C_95,D_96) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_49,B_50,C_51] : k2_enumset1(A_49,A_49,B_50,C_51) = k1_enumset1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_306,plain,(
    ! [B_98,C_99,D_100] : k2_enumset1(B_98,C_99,D_100,B_98) = k1_enumset1(B_98,C_99,D_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_24])).

tff(c_138,plain,(
    ! [A_87,D_88,C_89,B_90] : k2_enumset1(A_87,D_88,C_89,B_90) = k2_enumset1(A_87,B_90,C_89,D_88) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_154,plain,(
    ! [B_90,D_88,C_89] : k2_enumset1(B_90,D_88,C_89,B_90) = k1_enumset1(B_90,C_89,D_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_24])).

tff(c_318,plain,(
    ! [B_98,D_100,C_99] : k1_enumset1(B_98,D_100,C_99) = k1_enumset1(B_98,C_99,D_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_154])).

tff(c_8,plain,(
    ! [A_7,C_9,D_10,B_8] : k2_enumset1(A_7,C_9,D_10,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,D_14,C_13,B_12] : k2_enumset1(A_11,D_14,C_13,B_12) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [B_16,D_18,C_17,A_15] : k2_enumset1(B_16,D_18,C_17,A_15) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [D_22,C_21,B_20,A_19] : k2_enumset1(D_22,C_21,B_20,A_19) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_52,B_53,C_54,D_55] : k3_enumset1(A_52,A_52,B_53,C_54,D_55) = k2_enumset1(A_52,B_53,C_54,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [D_59,A_56,B_57,C_58,E_60] : k4_enumset1(A_56,A_56,B_57,C_58,D_59,E_60) = k3_enumset1(A_56,B_57,C_58,D_59,E_60) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_61,B_62,E_65,C_63,D_64,F_66] : k5_enumset1(A_61,A_61,B_62,C_63,D_64,E_65,F_66) = k4_enumset1(A_61,B_62,C_63,D_64,E_65,F_66) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1679,plain,(
    ! [A_163,C_162,G_165,E_159,F_161,B_160,D_164] : k2_xboole_0(k3_enumset1(A_163,B_160,C_162,D_164,E_159),k2_tarski(F_161,G_165)) = k5_enumset1(A_163,B_160,C_162,D_164,E_159,F_161,G_165) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1688,plain,(
    ! [D_55,G_165,B_53,A_52,F_161,C_54] : k5_enumset1(A_52,A_52,B_53,C_54,D_55,F_161,G_165) = k2_xboole_0(k2_enumset1(A_52,B_53,C_54,D_55),k2_tarski(F_161,G_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1679])).

tff(c_7113,plain,(
    ! [C_238,A_233,G_236,F_234,D_237,B_235] : k2_xboole_0(k2_enumset1(A_233,B_235,C_238,D_237),k2_tarski(F_234,G_236)) = k4_enumset1(A_233,B_235,C_238,D_237,F_234,G_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1688])).

tff(c_7245,plain,(
    ! [C_51,G_236,F_234,B_50,A_49] : k4_enumset1(A_49,A_49,B_50,C_51,F_234,G_236) = k2_xboole_0(k1_enumset1(A_49,B_50,C_51),k2_tarski(F_234,G_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7113])).

tff(c_8051,plain,(
    ! [F_277,C_273,B_274,A_276,G_275] : k2_xboole_0(k1_enumset1(A_276,B_274,C_273),k2_tarski(F_277,G_275)) = k3_enumset1(A_276,B_274,C_273,F_277,G_275) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7245])).

tff(c_8075,plain,(
    ! [A_47,B_48,F_277,G_275] : k3_enumset1(A_47,A_47,B_48,F_277,G_275) = k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(F_277,G_275)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8051])).

tff(c_8078,plain,(
    ! [A_47,B_48,F_277,G_275] : k2_xboole_0(k2_tarski(A_47,B_48),k2_tarski(F_277,G_275)) = k2_enumset1(A_47,B_48,F_277,G_275) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8075])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_512,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_34])).

tff(c_8171,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8078,c_512])).

tff(c_8174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_24,c_8,c_10,c_12,c_14,c_8,c_8171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.71/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/2.71  
% 7.71/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/2.71  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 7.71/2.71  
% 7.71/2.71  %Foreground sorts:
% 7.71/2.71  
% 7.71/2.71  
% 7.71/2.71  %Background operators:
% 7.71/2.71  
% 7.71/2.71  
% 7.71/2.71  %Foreground operators:
% 7.71/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.71/2.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.71/2.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.71/2.71  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.71/2.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.71/2.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.71/2.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.71/2.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.71/2.71  tff('#skF_2', type, '#skF_2': $i).
% 7.71/2.71  tff('#skF_3', type, '#skF_3': $i).
% 7.71/2.71  tff('#skF_1', type, '#skF_1': $i).
% 7.71/2.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.71/2.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.71/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.71/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.71/2.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.71/2.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.71/2.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.71/2.71  
% 7.77/2.72  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 7.77/2.72  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 7.77/2.72  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 7.77/2.72  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 7.77/2.72  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 7.77/2.72  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 7.77/2.72  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.77/2.72  tff(f_53, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 7.77/2.72  tff(f_55, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 7.77/2.72  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 7.77/2.72  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 7.77/2.72  tff(c_225, plain, (![A_94, C_95, D_96, B_97]: (k2_enumset1(A_94, C_95, D_96, B_97)=k2_enumset1(A_94, B_97, C_95, D_96))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.77/2.72  tff(c_24, plain, (![A_49, B_50, C_51]: (k2_enumset1(A_49, A_49, B_50, C_51)=k1_enumset1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.77/2.72  tff(c_306, plain, (![B_98, C_99, D_100]: (k2_enumset1(B_98, C_99, D_100, B_98)=k1_enumset1(B_98, C_99, D_100))), inference(superposition, [status(thm), theory('equality')], [c_225, c_24])).
% 7.77/2.72  tff(c_138, plain, (![A_87, D_88, C_89, B_90]: (k2_enumset1(A_87, D_88, C_89, B_90)=k2_enumset1(A_87, B_90, C_89, D_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.77/2.72  tff(c_154, plain, (![B_90, D_88, C_89]: (k2_enumset1(B_90, D_88, C_89, B_90)=k1_enumset1(B_90, C_89, D_88))), inference(superposition, [status(thm), theory('equality')], [c_138, c_24])).
% 7.77/2.72  tff(c_318, plain, (![B_98, D_100, C_99]: (k1_enumset1(B_98, D_100, C_99)=k1_enumset1(B_98, C_99, D_100))), inference(superposition, [status(thm), theory('equality')], [c_306, c_154])).
% 7.77/2.72  tff(c_8, plain, (![A_7, C_9, D_10, B_8]: (k2_enumset1(A_7, C_9, D_10, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.77/2.72  tff(c_10, plain, (![A_11, D_14, C_13, B_12]: (k2_enumset1(A_11, D_14, C_13, B_12)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.77/2.72  tff(c_12, plain, (![B_16, D_18, C_17, A_15]: (k2_enumset1(B_16, D_18, C_17, A_15)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.77/2.72  tff(c_14, plain, (![D_22, C_21, B_20, A_19]: (k2_enumset1(D_22, C_21, B_20, A_19)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.77/2.72  tff(c_26, plain, (![A_52, B_53, C_54, D_55]: (k3_enumset1(A_52, A_52, B_53, C_54, D_55)=k2_enumset1(A_52, B_53, C_54, D_55))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.77/2.72  tff(c_22, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.77/2.72  tff(c_28, plain, (![D_59, A_56, B_57, C_58, E_60]: (k4_enumset1(A_56, A_56, B_57, C_58, D_59, E_60)=k3_enumset1(A_56, B_57, C_58, D_59, E_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.77/2.72  tff(c_30, plain, (![A_61, B_62, E_65, C_63, D_64, F_66]: (k5_enumset1(A_61, A_61, B_62, C_63, D_64, E_65, F_66)=k4_enumset1(A_61, B_62, C_63, D_64, E_65, F_66))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.77/2.72  tff(c_1679, plain, (![A_163, C_162, G_165, E_159, F_161, B_160, D_164]: (k2_xboole_0(k3_enumset1(A_163, B_160, C_162, D_164, E_159), k2_tarski(F_161, G_165))=k5_enumset1(A_163, B_160, C_162, D_164, E_159, F_161, G_165))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.77/2.72  tff(c_1688, plain, (![D_55, G_165, B_53, A_52, F_161, C_54]: (k5_enumset1(A_52, A_52, B_53, C_54, D_55, F_161, G_165)=k2_xboole_0(k2_enumset1(A_52, B_53, C_54, D_55), k2_tarski(F_161, G_165)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1679])).
% 7.77/2.72  tff(c_7113, plain, (![C_238, A_233, G_236, F_234, D_237, B_235]: (k2_xboole_0(k2_enumset1(A_233, B_235, C_238, D_237), k2_tarski(F_234, G_236))=k4_enumset1(A_233, B_235, C_238, D_237, F_234, G_236))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1688])).
% 7.77/2.72  tff(c_7245, plain, (![C_51, G_236, F_234, B_50, A_49]: (k4_enumset1(A_49, A_49, B_50, C_51, F_234, G_236)=k2_xboole_0(k1_enumset1(A_49, B_50, C_51), k2_tarski(F_234, G_236)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7113])).
% 7.77/2.72  tff(c_8051, plain, (![F_277, C_273, B_274, A_276, G_275]: (k2_xboole_0(k1_enumset1(A_276, B_274, C_273), k2_tarski(F_277, G_275))=k3_enumset1(A_276, B_274, C_273, F_277, G_275))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7245])).
% 7.77/2.72  tff(c_8075, plain, (![A_47, B_48, F_277, G_275]: (k3_enumset1(A_47, A_47, B_48, F_277, G_275)=k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(F_277, G_275)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8051])).
% 7.77/2.72  tff(c_8078, plain, (![A_47, B_48, F_277, G_275]: (k2_xboole_0(k2_tarski(A_47, B_48), k2_tarski(F_277, G_275))=k2_enumset1(A_47, B_48, F_277, G_275))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8075])).
% 7.77/2.72  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.77/2.72  tff(c_512, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_34])).
% 7.77/2.72  tff(c_8171, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8078, c_512])).
% 7.77/2.72  tff(c_8174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_24, c_8, c_10, c_12, c_14, c_8, c_8171])).
% 7.77/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/2.72  
% 7.77/2.72  Inference rules
% 7.77/2.72  ----------------------
% 7.77/2.72  #Ref     : 0
% 7.77/2.72  #Sup     : 2184
% 7.77/2.72  #Fact    : 0
% 7.77/2.72  #Define  : 0
% 7.77/2.72  #Split   : 0
% 7.77/2.72  #Chain   : 0
% 7.77/2.72  #Close   : 0
% 7.77/2.73  
% 7.77/2.73  Ordering : KBO
% 7.77/2.73  
% 7.77/2.73  Simplification rules
% 7.77/2.73  ----------------------
% 7.77/2.73  #Subsume      : 1019
% 7.77/2.73  #Demod        : 944
% 7.77/2.73  #Tautology    : 1013
% 7.77/2.73  #SimpNegUnit  : 0
% 7.77/2.73  #BackRed      : 2
% 7.77/2.73  
% 7.77/2.73  #Partial instantiations: 0
% 7.77/2.73  #Strategies tried      : 1
% 7.77/2.73  
% 7.77/2.73  Timing (in seconds)
% 7.77/2.73  ----------------------
% 7.81/2.73  Preprocessing        : 0.31
% 7.81/2.73  Parsing              : 0.16
% 7.81/2.73  CNF conversion       : 0.02
% 7.81/2.73  Main loop            : 1.66
% 7.81/2.73  Inferencing          : 0.40
% 7.81/2.73  Reduction            : 1.00
% 7.81/2.73  Demodulation         : 0.93
% 7.81/2.73  BG Simplification    : 0.04
% 7.81/2.73  Subsumption          : 0.17
% 7.81/2.73  Abstraction          : 0.08
% 7.81/2.73  MUC search           : 0.00
% 7.81/2.73  Cooper               : 0.00
% 7.81/2.73  Total                : 2.00
% 7.81/2.73  Index Insertion      : 0.00
% 7.81/2.73  Index Deletion       : 0.00
% 7.81/2.73  Index Matching       : 0.00
% 7.81/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
