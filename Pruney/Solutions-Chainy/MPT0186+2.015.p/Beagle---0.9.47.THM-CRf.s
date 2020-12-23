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
% DateTime   : Thu Dec  3 09:46:49 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 127 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :   28 ( 111 expanded)
%              Number of equality atoms :   27 ( 110 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,D_6,C_5] : k2_enumset1(A_3,B_4,D_6,C_5) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k4_enumset1(A_19,A_19,B_20,C_21,D_22,E_23) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k5_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,G_36,F_35] : k6_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35,G_36) = k5_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [B_66,F_70,H_72,C_67,G_69,D_65,E_71,A_68] : k2_xboole_0(k5_enumset1(A_68,B_66,C_67,D_65,E_71,F_70,G_69),k1_tarski(H_72)) = k6_enumset1(A_68,B_66,C_67,D_65,E_71,F_70,G_69,H_72) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_24,H_72,B_25,F_29,D_27,C_26,E_28] : k6_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29,H_72) = k2_xboole_0(k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29),k1_tarski(H_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_109,plain,(
    ! [H_78,A_77,C_73,B_74,D_79,F_76,E_75] : k2_xboole_0(k4_enumset1(A_77,B_74,C_73,D_79,E_75,F_76),k1_tarski(H_78)) = k5_enumset1(A_77,B_74,C_73,D_79,E_75,F_76,H_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_118,plain,(
    ! [A_19,H_78,C_21,D_22,B_20,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,H_78) = k2_xboole_0(k3_enumset1(A_19,B_20,C_21,D_22,E_23),k1_tarski(H_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_109])).

tff(c_122,plain,(
    ! [C_81,D_85,B_83,H_80,E_82,A_84] : k2_xboole_0(k3_enumset1(A_84,B_83,C_81,D_85,E_82),k1_tarski(H_80)) = k4_enumset1(A_84,B_83,C_81,D_85,E_82,H_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_131,plain,(
    ! [B_16,A_15,D_18,H_80,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,H_80) = k2_xboole_0(k2_enumset1(A_15,B_16,C_17,D_18),k1_tarski(H_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_135,plain,(
    ! [C_86,B_89,H_88,D_87,A_90] : k2_xboole_0(k2_enumset1(A_90,B_89,C_86,D_87),k1_tarski(H_88)) = k3_enumset1(A_90,B_89,C_86,D_87,H_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_131])).

tff(c_150,plain,(
    ! [H_93,D_91,A_92,B_95,C_94] : k2_xboole_0(k2_enumset1(A_92,B_95,D_91,C_94),k1_tarski(H_93)) = k3_enumset1(A_92,B_95,C_94,D_91,H_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_134,plain,(
    ! [B_16,A_15,D_18,H_80,C_17] : k2_xboole_0(k2_enumset1(A_15,B_16,C_17,D_18),k1_tarski(H_80)) = k3_enumset1(A_15,B_16,C_17,D_18,H_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_131])).

tff(c_173,plain,(
    ! [B_98,D_96,H_100,A_99,C_97] : k3_enumset1(A_99,B_98,D_96,C_97,H_100) = k3_enumset1(A_99,B_98,C_97,D_96,H_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_134])).

tff(c_226,plain,(
    ! [B_101,D_102,C_103,H_104] : k3_enumset1(B_101,B_101,D_102,C_103,H_104) = k2_enumset1(B_101,C_103,D_102,H_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_8])).

tff(c_241,plain,(
    ! [B_101,D_102,C_103,H_104] : k2_enumset1(B_101,D_102,C_103,H_104) = k2_enumset1(B_101,C_103,D_102,H_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_8])).

tff(c_16,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_16])).

tff(c_263,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_241,c_17])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.21  
% 2.01/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.21  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.11/1.21  
% 2.11/1.21  %Foreground sorts:
% 2.11/1.21  
% 2.11/1.21  
% 2.11/1.21  %Background operators:
% 2.11/1.21  
% 2.11/1.21  
% 2.11/1.21  %Foreground operators:
% 2.11/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.21  
% 2.11/1.23  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 2.11/1.23  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.11/1.23  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.11/1.23  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.11/1.23  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.11/1.23  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 2.11/1.23  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 2.11/1.23  tff(c_4, plain, (![A_3, B_4, D_6, C_5]: (k2_enumset1(A_3, B_4, D_6, C_5)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.23  tff(c_10, plain, (![A_19, C_21, D_22, B_20, E_23]: (k4_enumset1(A_19, A_19, B_20, C_21, D_22, E_23)=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.23  tff(c_8, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.23  tff(c_12, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k5_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29)=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.23  tff(c_14, plain, (![D_33, A_30, C_32, B_31, E_34, G_36, F_35]: (k6_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35, G_36)=k5_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.23  tff(c_96, plain, (![B_66, F_70, H_72, C_67, G_69, D_65, E_71, A_68]: (k2_xboole_0(k5_enumset1(A_68, B_66, C_67, D_65, E_71, F_70, G_69), k1_tarski(H_72))=k6_enumset1(A_68, B_66, C_67, D_65, E_71, F_70, G_69, H_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.23  tff(c_105, plain, (![A_24, H_72, B_25, F_29, D_27, C_26, E_28]: (k6_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29, H_72)=k2_xboole_0(k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29), k1_tarski(H_72)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_96])).
% 2.11/1.23  tff(c_109, plain, (![H_78, A_77, C_73, B_74, D_79, F_76, E_75]: (k2_xboole_0(k4_enumset1(A_77, B_74, C_73, D_79, E_75, F_76), k1_tarski(H_78))=k5_enumset1(A_77, B_74, C_73, D_79, E_75, F_76, H_78))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_105])).
% 2.11/1.23  tff(c_118, plain, (![A_19, H_78, C_21, D_22, B_20, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, H_78)=k2_xboole_0(k3_enumset1(A_19, B_20, C_21, D_22, E_23), k1_tarski(H_78)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_109])).
% 2.11/1.23  tff(c_122, plain, (![C_81, D_85, B_83, H_80, E_82, A_84]: (k2_xboole_0(k3_enumset1(A_84, B_83, C_81, D_85, E_82), k1_tarski(H_80))=k4_enumset1(A_84, B_83, C_81, D_85, E_82, H_80))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_118])).
% 2.11/1.23  tff(c_131, plain, (![B_16, A_15, D_18, H_80, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, H_80)=k2_xboole_0(k2_enumset1(A_15, B_16, C_17, D_18), k1_tarski(H_80)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_122])).
% 2.11/1.23  tff(c_135, plain, (![C_86, B_89, H_88, D_87, A_90]: (k2_xboole_0(k2_enumset1(A_90, B_89, C_86, D_87), k1_tarski(H_88))=k3_enumset1(A_90, B_89, C_86, D_87, H_88))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_131])).
% 2.11/1.23  tff(c_150, plain, (![H_93, D_91, A_92, B_95, C_94]: (k2_xboole_0(k2_enumset1(A_92, B_95, D_91, C_94), k1_tarski(H_93))=k3_enumset1(A_92, B_95, C_94, D_91, H_93))), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 2.11/1.23  tff(c_134, plain, (![B_16, A_15, D_18, H_80, C_17]: (k2_xboole_0(k2_enumset1(A_15, B_16, C_17, D_18), k1_tarski(H_80))=k3_enumset1(A_15, B_16, C_17, D_18, H_80))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_131])).
% 2.11/1.23  tff(c_173, plain, (![B_98, D_96, H_100, A_99, C_97]: (k3_enumset1(A_99, B_98, D_96, C_97, H_100)=k3_enumset1(A_99, B_98, C_97, D_96, H_100))), inference(superposition, [status(thm), theory('equality')], [c_150, c_134])).
% 2.11/1.23  tff(c_226, plain, (![B_101, D_102, C_103, H_104]: (k3_enumset1(B_101, B_101, D_102, C_103, H_104)=k2_enumset1(B_101, C_103, D_102, H_104))), inference(superposition, [status(thm), theory('equality')], [c_173, c_8])).
% 2.11/1.23  tff(c_241, plain, (![B_101, D_102, C_103, H_104]: (k2_enumset1(B_101, D_102, C_103, H_104)=k2_enumset1(B_101, C_103, D_102, H_104))), inference(superposition, [status(thm), theory('equality')], [c_226, c_8])).
% 2.11/1.23  tff(c_16, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.11/1.23  tff(c_17, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_16])).
% 2.11/1.23  tff(c_263, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_241, c_17])).
% 2.11/1.23  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_263])).
% 2.11/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  Inference rules
% 2.11/1.23  ----------------------
% 2.11/1.23  #Ref     : 0
% 2.11/1.23  #Sup     : 60
% 2.11/1.23  #Fact    : 0
% 2.11/1.23  #Define  : 0
% 2.11/1.23  #Split   : 0
% 2.11/1.23  #Chain   : 0
% 2.11/1.23  #Close   : 0
% 2.11/1.23  
% 2.11/1.23  Ordering : KBO
% 2.11/1.23  
% 2.11/1.23  Simplification rules
% 2.11/1.23  ----------------------
% 2.11/1.23  #Subsume      : 0
% 2.11/1.23  #Demod        : 16
% 2.11/1.23  #Tautology    : 44
% 2.11/1.23  #SimpNegUnit  : 0
% 2.11/1.23  #BackRed      : 1
% 2.11/1.23  
% 2.11/1.23  #Partial instantiations: 0
% 2.13/1.23  #Strategies tried      : 1
% 2.13/1.23  
% 2.13/1.23  Timing (in seconds)
% 2.13/1.23  ----------------------
% 2.13/1.23  Preprocessing        : 0.30
% 2.13/1.23  Parsing              : 0.16
% 2.13/1.23  CNF conversion       : 0.02
% 2.13/1.23  Main loop            : 0.18
% 2.13/1.23  Inferencing          : 0.08
% 2.13/1.23  Reduction            : 0.07
% 2.13/1.23  Demodulation         : 0.05
% 2.13/1.23  BG Simplification    : 0.01
% 2.13/1.23  Subsumption          : 0.02
% 2.13/1.23  Abstraction          : 0.01
% 2.13/1.23  MUC search           : 0.00
% 2.13/1.23  Cooper               : 0.00
% 2.13/1.23  Total                : 0.50
% 2.13/1.23  Index Insertion      : 0.00
% 2.13/1.23  Index Deletion       : 0.00
% 2.13/1.23  Index Matching       : 0.00
% 2.13/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
