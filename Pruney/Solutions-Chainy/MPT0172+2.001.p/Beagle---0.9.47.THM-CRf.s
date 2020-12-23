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
% DateTime   : Thu Dec  3 09:46:30 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   27 (  44 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k5_enumset1(A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

tff(c_10,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k1_tarski(A_5),k2_tarski(B_6,C_7)) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_31] : k2_enumset1(A_31,A_31,A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] : k6_enumset1(A_25,A_25,A_25,B_26,C_27,D_28,E_29,F_30) = k4_enumset1(A_25,B_26,C_27,D_28,E_29,F_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_56,C_57,E_58,G_62,F_59,B_61,D_60] : k6_enumset1(A_56,A_56,B_61,C_57,D_60,E_58,F_59,G_62) = k5_enumset1(A_56,B_61,C_57,D_60,E_58,F_59,G_62) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [G_72,C_75,B_74,E_71,F_73,D_76] : k5_enumset1(B_74,B_74,C_75,D_76,E_71,F_73,G_72) = k4_enumset1(B_74,C_75,D_76,E_71,F_73,G_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_14])).

tff(c_18,plain,(
    ! [A_32,B_33,C_34,D_35] : k5_enumset1(A_32,A_32,A_32,A_32,B_33,C_34,D_35) = k2_enumset1(A_32,B_33,C_34,D_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [D_77,E_78,F_79,G_80] : k4_enumset1(D_77,D_77,D_77,E_78,F_79,G_80) = k2_enumset1(D_77,E_78,F_79,G_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_18])).

tff(c_8,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,H_15,F_13,G_14] : k2_xboole_0(k4_enumset1(A_8,B_9,C_10,D_11,E_12,F_13),k2_tarski(G_14,H_15)) = k6_enumset1(A_8,B_9,C_10,D_11,E_12,F_13,G_14,H_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_132,plain,(
    ! [D_77,F_79,G_80,H_15,G_14,E_78] : k6_enumset1(D_77,D_77,D_77,E_78,F_79,G_80,G_14,H_15) = k2_xboole_0(k2_enumset1(D_77,E_78,F_79,G_80),k2_tarski(G_14,H_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_8])).

tff(c_141,plain,(
    ! [H_86,E_84,G_82,F_81,G_85,D_83] : k2_xboole_0(k2_enumset1(D_83,E_84,F_81,G_82),k2_tarski(G_85,H_86)) = k4_enumset1(D_83,E_84,F_81,G_82,G_85,H_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_132])).

tff(c_150,plain,(
    ! [A_31,G_85,H_86] : k4_enumset1(A_31,A_31,A_31,A_31,G_85,H_86) = k2_xboole_0(k1_tarski(A_31),k2_tarski(G_85,H_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_141])).

tff(c_154,plain,(
    ! [A_87,G_88,H_89] : k4_enumset1(A_87,A_87,A_87,A_87,G_88,H_89) = k1_enumset1(A_87,G_88,H_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_150])).

tff(c_116,plain,(
    ! [D_76,E_71,F_73,G_72] : k4_enumset1(D_76,D_76,D_76,E_71,F_73,G_72) = k2_enumset1(D_76,E_71,F_73,G_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_18])).

tff(c_160,plain,(
    ! [A_87,G_88,H_89] : k2_enumset1(A_87,A_87,G_88,H_89) = k1_enumset1(A_87,G_88,H_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_116])).

tff(c_20,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_125,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_173,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_125])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:24:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.94/1.20  
% 1.94/1.20  %Foreground sorts:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Background operators:
% 1.94/1.20  
% 1.94/1.20  
% 1.94/1.20  %Foreground operators:
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.20  
% 1.94/1.21  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.94/1.21  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 1.94/1.21  tff(f_41, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 1.94/1.21  tff(f_39, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_enumset1)).
% 1.94/1.21  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.94/1.21  tff(f_43, axiom, (![A, B, C, D]: (k5_enumset1(A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_enumset1)).
% 1.94/1.21  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 1.94/1.21  tff(f_46, negated_conjecture, ~(![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_enumset1)).
% 1.94/1.21  tff(c_10, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.21  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k1_tarski(A_5), k2_tarski(B_6, C_7))=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.21  tff(c_16, plain, (![A_31]: (k2_enumset1(A_31, A_31, A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.21  tff(c_14, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (k6_enumset1(A_25, A_25, A_25, B_26, C_27, D_28, E_29, F_30)=k4_enumset1(A_25, B_26, C_27, D_28, E_29, F_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.22  tff(c_84, plain, (![A_56, C_57, E_58, G_62, F_59, B_61, D_60]: (k6_enumset1(A_56, A_56, B_61, C_57, D_60, E_58, F_59, G_62)=k5_enumset1(A_56, B_61, C_57, D_60, E_58, F_59, G_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.22  tff(c_109, plain, (![G_72, C_75, B_74, E_71, F_73, D_76]: (k5_enumset1(B_74, B_74, C_75, D_76, E_71, F_73, G_72)=k4_enumset1(B_74, C_75, D_76, E_71, F_73, G_72))), inference(superposition, [status(thm), theory('equality')], [c_84, c_14])).
% 1.94/1.22  tff(c_18, plain, (![A_32, B_33, C_34, D_35]: (k5_enumset1(A_32, A_32, A_32, A_32, B_33, C_34, D_35)=k2_enumset1(A_32, B_33, C_34, D_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.22  tff(c_126, plain, (![D_77, E_78, F_79, G_80]: (k4_enumset1(D_77, D_77, D_77, E_78, F_79, G_80)=k2_enumset1(D_77, E_78, F_79, G_80))), inference(superposition, [status(thm), theory('equality')], [c_109, c_18])).
% 1.94/1.22  tff(c_8, plain, (![E_12, D_11, A_8, C_10, B_9, H_15, F_13, G_14]: (k2_xboole_0(k4_enumset1(A_8, B_9, C_10, D_11, E_12, F_13), k2_tarski(G_14, H_15))=k6_enumset1(A_8, B_9, C_10, D_11, E_12, F_13, G_14, H_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.22  tff(c_132, plain, (![D_77, F_79, G_80, H_15, G_14, E_78]: (k6_enumset1(D_77, D_77, D_77, E_78, F_79, G_80, G_14, H_15)=k2_xboole_0(k2_enumset1(D_77, E_78, F_79, G_80), k2_tarski(G_14, H_15)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_8])).
% 1.94/1.22  tff(c_141, plain, (![H_86, E_84, G_82, F_81, G_85, D_83]: (k2_xboole_0(k2_enumset1(D_83, E_84, F_81, G_82), k2_tarski(G_85, H_86))=k4_enumset1(D_83, E_84, F_81, G_82, G_85, H_86))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_132])).
% 1.94/1.22  tff(c_150, plain, (![A_31, G_85, H_86]: (k4_enumset1(A_31, A_31, A_31, A_31, G_85, H_86)=k2_xboole_0(k1_tarski(A_31), k2_tarski(G_85, H_86)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_141])).
% 1.94/1.22  tff(c_154, plain, (![A_87, G_88, H_89]: (k4_enumset1(A_87, A_87, A_87, A_87, G_88, H_89)=k1_enumset1(A_87, G_88, H_89))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_150])).
% 1.94/1.22  tff(c_116, plain, (![D_76, E_71, F_73, G_72]: (k4_enumset1(D_76, D_76, D_76, E_71, F_73, G_72)=k2_enumset1(D_76, E_71, F_73, G_72))), inference(superposition, [status(thm), theory('equality')], [c_109, c_18])).
% 1.94/1.22  tff(c_160, plain, (![A_87, G_88, H_89]: (k2_enumset1(A_87, A_87, G_88, H_89)=k1_enumset1(A_87, G_88, H_89))), inference(superposition, [status(thm), theory('equality')], [c_154, c_116])).
% 1.94/1.22  tff(c_20, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.22  tff(c_125, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_20])).
% 1.94/1.22  tff(c_173, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_125])).
% 1.94/1.22  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_173])).
% 1.94/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  Inference rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Ref     : 0
% 1.94/1.22  #Sup     : 35
% 1.94/1.22  #Fact    : 0
% 1.94/1.22  #Define  : 0
% 1.94/1.22  #Split   : 0
% 1.94/1.22  #Chain   : 0
% 1.94/1.22  #Close   : 0
% 1.94/1.22  
% 1.94/1.22  Ordering : KBO
% 1.94/1.22  
% 1.94/1.22  Simplification rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Subsume      : 0
% 1.94/1.22  #Demod        : 7
% 1.94/1.22  #Tautology    : 28
% 1.94/1.22  #SimpNegUnit  : 0
% 1.94/1.22  #BackRed      : 2
% 1.94/1.22  
% 1.94/1.22  #Partial instantiations: 0
% 1.94/1.22  #Strategies tried      : 1
% 1.94/1.22  
% 1.94/1.22  Timing (in seconds)
% 1.94/1.22  ----------------------
% 1.94/1.22  Preprocessing        : 0.27
% 1.94/1.22  Parsing              : 0.14
% 1.94/1.22  CNF conversion       : 0.02
% 1.94/1.22  Main loop            : 0.13
% 1.94/1.22  Inferencing          : 0.06
% 1.94/1.22  Reduction            : 0.04
% 1.94/1.22  Demodulation         : 0.03
% 1.94/1.22  BG Simplification    : 0.01
% 1.94/1.22  Subsumption          : 0.01
% 1.94/1.22  Abstraction          : 0.01
% 1.94/1.22  MUC search           : 0.00
% 1.94/1.22  Cooper               : 0.00
% 1.94/1.22  Total                : 0.43
% 1.94/1.22  Index Insertion      : 0.00
% 1.94/1.22  Index Deletion       : 0.00
% 1.94/1.22  Index Matching       : 0.00
% 1.94/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
