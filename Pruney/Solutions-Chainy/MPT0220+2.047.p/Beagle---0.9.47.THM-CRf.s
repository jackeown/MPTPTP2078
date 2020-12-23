%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:10 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_12,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23,D_24] : k3_enumset1(A_21,A_21,B_22,C_23,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : k4_enumset1(A_25,A_25,B_26,C_27,D_28,E_29) = k3_enumset1(A_25,B_26,C_27,D_28,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,C_38,B_37] : k6_enumset1(A_36,A_36,B_37,C_38,D_39,E_40,F_41,G_42) = k5_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_173,plain,(
    ! [F_84,H_86,C_81,A_82,G_83,D_79,E_85,B_80] : k2_xboole_0(k2_tarski(A_82,B_80),k4_enumset1(C_81,D_79,E_85,F_84,G_83,H_86)) = k6_enumset1(A_82,B_80,C_81,D_79,E_85,F_84,G_83,H_86) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_185,plain,(
    ! [F_84,H_86,A_15,C_81,G_83,D_79,E_85] : k6_enumset1(A_15,A_15,C_81,D_79,E_85,F_84,G_83,H_86) = k2_xboole_0(k1_tarski(A_15),k4_enumset1(C_81,D_79,E_85,F_84,G_83,H_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_173])).

tff(c_189,plain,(
    ! [G_92,H_90,F_89,E_87,A_91,C_88,D_93] : k2_xboole_0(k1_tarski(A_91),k4_enumset1(C_88,D_93,E_87,F_89,G_92,H_90)) = k5_enumset1(A_91,C_88,D_93,E_87,F_89,G_92,H_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_234,plain,(
    ! [C_103,B_104,A_102,A_106,E_105,D_101] : k5_enumset1(A_106,A_102,A_102,B_104,C_103,D_101,E_105) = k2_xboole_0(k1_tarski(A_106),k3_enumset1(A_102,B_104,C_103,D_101,E_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_189])).

tff(c_20,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35) = k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_244,plain,(
    ! [C_103,B_104,A_102,E_105,D_101] : k2_xboole_0(k1_tarski(A_102),k3_enumset1(A_102,B_104,C_103,D_101,E_105)) = k4_enumset1(A_102,A_102,B_104,C_103,D_101,E_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_20])).

tff(c_264,plain,(
    ! [A_110,D_108,C_111,B_109,E_107] : k2_xboole_0(k1_tarski(A_110),k3_enumset1(A_110,B_109,C_111,D_108,E_107)) = k3_enumset1(A_110,B_109,C_111,D_108,E_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_244])).

tff(c_280,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k1_tarski(A_21),k2_enumset1(A_21,B_22,C_23,D_24)) = k3_enumset1(A_21,A_21,B_22,C_23,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_264])).

tff(c_284,plain,(
    ! [A_112,B_113,C_114,D_115] : k2_xboole_0(k1_tarski(A_112),k2_enumset1(A_112,B_113,C_114,D_115)) = k2_enumset1(A_112,B_113,C_114,D_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_280])).

tff(c_293,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k1_tarski(A_18),k1_enumset1(A_18,B_19,C_20)) = k2_enumset1(A_18,A_18,B_19,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_284])).

tff(c_343,plain,(
    ! [A_121,B_122,C_123] : k2_xboole_0(k1_tarski(A_121),k1_enumset1(A_121,B_122,C_123)) = k1_enumset1(A_121,B_122,C_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_293])).

tff(c_352,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k2_tarski(A_16,B_17)) = k1_enumset1(A_16,A_16,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_343])).

tff(c_355,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k2_tarski(A_16,B_17)) = k2_tarski(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_352])).

tff(c_24,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.23  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.14/1.23  
% 2.14/1.23  %Foreground sorts:
% 2.14/1.23  
% 2.14/1.23  
% 2.14/1.23  %Background operators:
% 2.14/1.23  
% 2.14/1.23  
% 2.14/1.23  %Foreground operators:
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.14/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.23  
% 2.17/1.24  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.17/1.24  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.17/1.24  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.17/1.24  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.17/1.24  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.17/1.24  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.17/1.24  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 2.17/1.24  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.17/1.24  tff(f_50, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 2.17/1.24  tff(c_12, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.24  tff(c_14, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.24  tff(c_16, plain, (![A_21, B_22, C_23, D_24]: (k3_enumset1(A_21, A_21, B_22, C_23, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.24  tff(c_18, plain, (![A_25, E_29, C_27, D_28, B_26]: (k4_enumset1(A_25, A_25, B_26, C_27, D_28, E_29)=k3_enumset1(A_25, B_26, C_27, D_28, E_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.24  tff(c_22, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (k6_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, F_41, G_42)=k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.24  tff(c_10, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.24  tff(c_173, plain, (![F_84, H_86, C_81, A_82, G_83, D_79, E_85, B_80]: (k2_xboole_0(k2_tarski(A_82, B_80), k4_enumset1(C_81, D_79, E_85, F_84, G_83, H_86))=k6_enumset1(A_82, B_80, C_81, D_79, E_85, F_84, G_83, H_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.24  tff(c_185, plain, (![F_84, H_86, A_15, C_81, G_83, D_79, E_85]: (k6_enumset1(A_15, A_15, C_81, D_79, E_85, F_84, G_83, H_86)=k2_xboole_0(k1_tarski(A_15), k4_enumset1(C_81, D_79, E_85, F_84, G_83, H_86)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_173])).
% 2.17/1.24  tff(c_189, plain, (![G_92, H_90, F_89, E_87, A_91, C_88, D_93]: (k2_xboole_0(k1_tarski(A_91), k4_enumset1(C_88, D_93, E_87, F_89, G_92, H_90))=k5_enumset1(A_91, C_88, D_93, E_87, F_89, G_92, H_90))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_185])).
% 2.17/1.24  tff(c_234, plain, (![C_103, B_104, A_102, A_106, E_105, D_101]: (k5_enumset1(A_106, A_102, A_102, B_104, C_103, D_101, E_105)=k2_xboole_0(k1_tarski(A_106), k3_enumset1(A_102, B_104, C_103, D_101, E_105)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_189])).
% 2.17/1.24  tff(c_20, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35)=k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.24  tff(c_244, plain, (![C_103, B_104, A_102, E_105, D_101]: (k2_xboole_0(k1_tarski(A_102), k3_enumset1(A_102, B_104, C_103, D_101, E_105))=k4_enumset1(A_102, A_102, B_104, C_103, D_101, E_105))), inference(superposition, [status(thm), theory('equality')], [c_234, c_20])).
% 2.17/1.24  tff(c_264, plain, (![A_110, D_108, C_111, B_109, E_107]: (k2_xboole_0(k1_tarski(A_110), k3_enumset1(A_110, B_109, C_111, D_108, E_107))=k3_enumset1(A_110, B_109, C_111, D_108, E_107))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_244])).
% 2.17/1.24  tff(c_280, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k1_tarski(A_21), k2_enumset1(A_21, B_22, C_23, D_24))=k3_enumset1(A_21, A_21, B_22, C_23, D_24))), inference(superposition, [status(thm), theory('equality')], [c_16, c_264])).
% 2.17/1.24  tff(c_284, plain, (![A_112, B_113, C_114, D_115]: (k2_xboole_0(k1_tarski(A_112), k2_enumset1(A_112, B_113, C_114, D_115))=k2_enumset1(A_112, B_113, C_114, D_115))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_280])).
% 2.17/1.24  tff(c_293, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k1_tarski(A_18), k1_enumset1(A_18, B_19, C_20))=k2_enumset1(A_18, A_18, B_19, C_20))), inference(superposition, [status(thm), theory('equality')], [c_14, c_284])).
% 2.17/1.24  tff(c_343, plain, (![A_121, B_122, C_123]: (k2_xboole_0(k1_tarski(A_121), k1_enumset1(A_121, B_122, C_123))=k1_enumset1(A_121, B_122, C_123))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_293])).
% 2.17/1.24  tff(c_352, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k2_tarski(A_16, B_17))=k1_enumset1(A_16, A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_343])).
% 2.17/1.24  tff(c_355, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k2_tarski(A_16, B_17))=k2_tarski(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_352])).
% 2.17/1.24  tff(c_24, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.24  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_24])).
% 2.17/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  Inference rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Ref     : 0
% 2.17/1.24  #Sup     : 78
% 2.17/1.24  #Fact    : 0
% 2.17/1.24  #Define  : 0
% 2.17/1.24  #Split   : 0
% 2.17/1.24  #Chain   : 0
% 2.17/1.24  #Close   : 0
% 2.17/1.24  
% 2.17/1.24  Ordering : KBO
% 2.17/1.24  
% 2.17/1.24  Simplification rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Subsume      : 0
% 2.17/1.24  #Demod        : 20
% 2.17/1.24  #Tautology    : 59
% 2.17/1.24  #SimpNegUnit  : 0
% 2.17/1.24  #BackRed      : 1
% 2.17/1.24  
% 2.17/1.24  #Partial instantiations: 0
% 2.17/1.24  #Strategies tried      : 1
% 2.17/1.24  
% 2.17/1.24  Timing (in seconds)
% 2.17/1.24  ----------------------
% 2.17/1.24  Preprocessing        : 0.28
% 2.17/1.24  Parsing              : 0.15
% 2.17/1.24  CNF conversion       : 0.02
% 2.17/1.24  Main loop            : 0.20
% 2.17/1.24  Inferencing          : 0.10
% 2.17/1.25  Reduction            : 0.07
% 2.17/1.25  Demodulation         : 0.05
% 2.17/1.25  BG Simplification    : 0.02
% 2.17/1.25  Subsumption          : 0.02
% 2.17/1.25  Abstraction          : 0.02
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.17/1.25  Total                : 0.51
% 2.17/1.25  Index Insertion      : 0.00
% 2.17/1.25  Index Deletion       : 0.00
% 2.17/1.25  Index Matching       : 0.00
% 2.17/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
