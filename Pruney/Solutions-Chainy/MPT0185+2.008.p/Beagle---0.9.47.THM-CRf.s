%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:47 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   29 (  47 expanded)
%              Number of equality atoms :   28 (  46 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(c_10,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k5_enumset1(A_21,A_21,B_22,C_23,D_24,E_25,F_26) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_34,C_36,B_35] : k1_enumset1(A_34,C_36,B_35) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [C_29,D_30,B_28,G_33,F_32,A_27,E_31] : k6_enumset1(A_27,A_27,B_28,C_29,D_30,E_31,F_32,G_33) = k5_enumset1(A_27,B_28,C_29,D_30,E_31,F_32,G_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [C_70,H_72,F_65,G_66,D_68,B_69,A_71,E_67] : k2_xboole_0(k3_enumset1(A_71,B_69,C_70,D_68,E_67),k1_enumset1(F_65,G_66,H_72)) = k6_enumset1(A_71,B_69,C_70,D_68,E_67,F_65,G_66,H_72) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [D_15,H_72,F_65,G_66,C_14,A_12,B_13] : k6_enumset1(A_12,A_12,B_13,C_14,D_15,F_65,G_66,H_72) = k2_xboole_0(k2_enumset1(A_12,B_13,C_14,D_15),k1_enumset1(F_65,G_66,H_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_95])).

tff(c_114,plain,(
    ! [C_78,B_73,D_77,H_79,F_76,G_74,A_75] : k2_xboole_0(k2_enumset1(A_75,B_73,C_78,D_77),k1_enumset1(F_76,G_74,H_79)) = k5_enumset1(A_75,B_73,C_78,D_77,F_76,G_74,H_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104])).

tff(c_133,plain,(
    ! [C_85,C_86,B_81,B_84,A_83,A_80,D_82] : k2_xboole_0(k2_enumset1(A_83,B_81,C_85,D_82),k1_enumset1(A_80,B_84,C_86)) = k5_enumset1(A_83,B_81,C_85,D_82,A_80,C_86,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_114])).

tff(c_148,plain,(
    ! [C_11,B_10,C_86,B_84,A_80,A_9] : k5_enumset1(A_9,A_9,B_10,C_11,A_80,C_86,B_84) = k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(A_80,B_84,C_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_133])).

tff(c_181,plain,(
    ! [A_98,C_96,B_95,B_97,C_93,A_94] : k2_xboole_0(k1_enumset1(A_98,B_95,C_96),k1_enumset1(A_94,B_97,C_93)) = k4_enumset1(A_98,B_95,C_96,A_94,C_93,B_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_148])).

tff(c_123,plain,(
    ! [C_11,H_79,B_10,F_76,G_74,A_9] : k5_enumset1(A_9,A_9,B_10,C_11,F_76,G_74,H_79) = k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(F_76,G_74,H_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_114])).

tff(c_132,plain,(
    ! [C_11,H_79,B_10,F_76,G_74,A_9] : k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(F_76,G_74,H_79)) = k4_enumset1(A_9,B_10,C_11,F_76,G_74,H_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_123])).

tff(c_210,plain,(
    ! [C_103,A_102,C_104,A_99,B_101,B_100] : k4_enumset1(A_102,B_101,C_103,A_99,C_104,B_100) = k4_enumset1(A_102,B_101,C_103,A_99,B_100,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_132])).

tff(c_8,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k4_enumset1(A_16,A_16,B_17,C_18,D_19,E_20) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_257,plain,(
    ! [B_107,A_105,B_108,C_109,C_106] : k4_enumset1(B_108,B_108,C_109,A_105,C_106,B_107) = k3_enumset1(B_108,C_109,A_105,B_107,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_8])).

tff(c_290,plain,(
    ! [C_110,B_111,A_112,C_114,B_113] : k3_enumset1(B_111,C_110,A_112,C_114,B_113) = k3_enumset1(B_111,C_110,A_112,B_113,C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_8])).

tff(c_376,plain,(
    ! [C_123,A_124,C_125,B_126] : k3_enumset1(C_123,C_123,A_124,C_125,B_126) = k2_enumset1(C_123,A_124,B_126,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_6])).

tff(c_394,plain,(
    ! [C_123,A_124,C_125,B_126] : k2_enumset1(C_123,A_124,C_125,B_126) = k2_enumset1(C_123,A_124,B_126,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_6])).

tff(c_16,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:21:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.24  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.21/1.24  
% 2.21/1.24  %Foreground sorts:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Background operators:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Foreground operators:
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.24  
% 2.21/1.25  tff(f_35, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.21/1.25  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.21/1.25  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 2.21/1.25  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.21/1.25  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.21/1.25  tff(f_27, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 2.21/1.25  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.21/1.25  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 2.21/1.25  tff(c_10, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k5_enumset1(A_21, A_21, B_22, C_23, D_24, E_25, F_26)=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.25  tff(c_4, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.25  tff(c_14, plain, (![A_34, C_36, B_35]: (k1_enumset1(A_34, C_36, B_35)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.25  tff(c_12, plain, (![C_29, D_30, B_28, G_33, F_32, A_27, E_31]: (k6_enumset1(A_27, A_27, B_28, C_29, D_30, E_31, F_32, G_33)=k5_enumset1(A_27, B_28, C_29, D_30, E_31, F_32, G_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.25  tff(c_6, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.25  tff(c_95, plain, (![C_70, H_72, F_65, G_66, D_68, B_69, A_71, E_67]: (k2_xboole_0(k3_enumset1(A_71, B_69, C_70, D_68, E_67), k1_enumset1(F_65, G_66, H_72))=k6_enumset1(A_71, B_69, C_70, D_68, E_67, F_65, G_66, H_72))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.25  tff(c_104, plain, (![D_15, H_72, F_65, G_66, C_14, A_12, B_13]: (k6_enumset1(A_12, A_12, B_13, C_14, D_15, F_65, G_66, H_72)=k2_xboole_0(k2_enumset1(A_12, B_13, C_14, D_15), k1_enumset1(F_65, G_66, H_72)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_95])).
% 2.21/1.25  tff(c_114, plain, (![C_78, B_73, D_77, H_79, F_76, G_74, A_75]: (k2_xboole_0(k2_enumset1(A_75, B_73, C_78, D_77), k1_enumset1(F_76, G_74, H_79))=k5_enumset1(A_75, B_73, C_78, D_77, F_76, G_74, H_79))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_104])).
% 2.21/1.25  tff(c_133, plain, (![C_85, C_86, B_81, B_84, A_83, A_80, D_82]: (k2_xboole_0(k2_enumset1(A_83, B_81, C_85, D_82), k1_enumset1(A_80, B_84, C_86))=k5_enumset1(A_83, B_81, C_85, D_82, A_80, C_86, B_84))), inference(superposition, [status(thm), theory('equality')], [c_14, c_114])).
% 2.21/1.25  tff(c_148, plain, (![C_11, B_10, C_86, B_84, A_80, A_9]: (k5_enumset1(A_9, A_9, B_10, C_11, A_80, C_86, B_84)=k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(A_80, B_84, C_86)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_133])).
% 2.21/1.25  tff(c_181, plain, (![A_98, C_96, B_95, B_97, C_93, A_94]: (k2_xboole_0(k1_enumset1(A_98, B_95, C_96), k1_enumset1(A_94, B_97, C_93))=k4_enumset1(A_98, B_95, C_96, A_94, C_93, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_148])).
% 2.21/1.25  tff(c_123, plain, (![C_11, H_79, B_10, F_76, G_74, A_9]: (k5_enumset1(A_9, A_9, B_10, C_11, F_76, G_74, H_79)=k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(F_76, G_74, H_79)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_114])).
% 2.21/1.25  tff(c_132, plain, (![C_11, H_79, B_10, F_76, G_74, A_9]: (k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(F_76, G_74, H_79))=k4_enumset1(A_9, B_10, C_11, F_76, G_74, H_79))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_123])).
% 2.21/1.25  tff(c_210, plain, (![C_103, A_102, C_104, A_99, B_101, B_100]: (k4_enumset1(A_102, B_101, C_103, A_99, C_104, B_100)=k4_enumset1(A_102, B_101, C_103, A_99, B_100, C_104))), inference(superposition, [status(thm), theory('equality')], [c_181, c_132])).
% 2.21/1.25  tff(c_8, plain, (![C_18, B_17, A_16, D_19, E_20]: (k4_enumset1(A_16, A_16, B_17, C_18, D_19, E_20)=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.25  tff(c_257, plain, (![B_107, A_105, B_108, C_109, C_106]: (k4_enumset1(B_108, B_108, C_109, A_105, C_106, B_107)=k3_enumset1(B_108, C_109, A_105, B_107, C_106))), inference(superposition, [status(thm), theory('equality')], [c_210, c_8])).
% 2.21/1.25  tff(c_290, plain, (![C_110, B_111, A_112, C_114, B_113]: (k3_enumset1(B_111, C_110, A_112, C_114, B_113)=k3_enumset1(B_111, C_110, A_112, B_113, C_114))), inference(superposition, [status(thm), theory('equality')], [c_257, c_8])).
% 2.21/1.25  tff(c_376, plain, (![C_123, A_124, C_125, B_126]: (k3_enumset1(C_123, C_123, A_124, C_125, B_126)=k2_enumset1(C_123, A_124, B_126, C_125))), inference(superposition, [status(thm), theory('equality')], [c_290, c_6])).
% 2.21/1.25  tff(c_394, plain, (![C_123, A_124, C_125, B_126]: (k2_enumset1(C_123, A_124, C_125, B_126)=k2_enumset1(C_123, A_124, B_126, C_125))), inference(superposition, [status(thm), theory('equality')], [c_376, c_6])).
% 2.21/1.25  tff(c_16, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.21/1.25  tff(c_419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_394, c_16])).
% 2.21/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.25  
% 2.21/1.25  Inference rules
% 2.21/1.25  ----------------------
% 2.21/1.25  #Ref     : 0
% 2.21/1.25  #Sup     : 102
% 2.21/1.25  #Fact    : 0
% 2.21/1.25  #Define  : 0
% 2.21/1.25  #Split   : 0
% 2.21/1.25  #Chain   : 0
% 2.21/1.25  #Close   : 0
% 2.21/1.25  
% 2.21/1.25  Ordering : KBO
% 2.21/1.25  
% 2.21/1.25  Simplification rules
% 2.21/1.25  ----------------------
% 2.21/1.25  #Subsume      : 0
% 2.21/1.25  #Demod        : 24
% 2.21/1.25  #Tautology    : 64
% 2.21/1.25  #SimpNegUnit  : 0
% 2.21/1.25  #BackRed      : 1
% 2.21/1.25  
% 2.21/1.25  #Partial instantiations: 0
% 2.21/1.25  #Strategies tried      : 1
% 2.21/1.25  
% 2.21/1.25  Timing (in seconds)
% 2.21/1.25  ----------------------
% 2.21/1.25  Preprocessing        : 0.28
% 2.21/1.25  Parsing              : 0.15
% 2.21/1.25  CNF conversion       : 0.02
% 2.21/1.25  Main loop            : 0.23
% 2.21/1.25  Inferencing          : 0.10
% 2.21/1.25  Reduction            : 0.08
% 2.21/1.25  Demodulation         : 0.07
% 2.21/1.25  BG Simplification    : 0.02
% 2.21/1.25  Subsumption          : 0.02
% 2.21/1.25  Abstraction          : 0.02
% 2.21/1.26  MUC search           : 0.00
% 2.21/1.26  Cooper               : 0.00
% 2.21/1.26  Total                : 0.54
% 2.21/1.26  Index Insertion      : 0.00
% 2.21/1.26  Index Deletion       : 0.00
% 2.21/1.26  Index Matching       : 0.00
% 2.21/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
