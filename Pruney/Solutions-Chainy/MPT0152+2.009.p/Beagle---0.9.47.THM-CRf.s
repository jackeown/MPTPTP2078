%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:02 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 183 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 164 expanded)
%              Number of equality atoms :   57 ( 163 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_14,plain,(
    ! [A_25,G_31,F_30,E_29,H_32,C_27,D_28,B_26] : k2_xboole_0(k1_tarski(A_25),k5_enumset1(B_26,C_27,D_28,E_29,F_30,G_31,H_32)) = k6_enumset1(A_25,B_26,C_27,D_28,E_29,F_30,G_31,H_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [E_22,G_24,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k2_tarski(A_18,B_19),k3_enumset1(C_20,D_21,E_22,F_23,G_24)) = k5_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k2_xboole_0(A_35,B_36),C_37) = k2_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k1_tarski(B_46),C_47)) = k2_xboole_0(k2_tarski(A_45,B_46),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_91,plain,(
    ! [A_45,A_6,B_7,C_8] : k2_xboole_0(k2_tarski(A_45,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k1_tarski(A_45),k1_enumset1(A_6,B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_98,plain,(
    ! [A_45,A_6,B_7,C_8] : k2_xboole_0(k2_tarski(A_45,A_6),k2_tarski(B_7,C_8)) = k2_enumset1(A_45,A_6,B_7,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_46,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k2_tarski(B_39,C_40)) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [A_60,B_61,C_62,C_63] : k2_xboole_0(k1_tarski(A_60),k2_xboole_0(k2_tarski(B_61,C_62),C_63)) = k2_xboole_0(k1_enumset1(A_60,B_61,C_62),C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_154,plain,(
    ! [B_7,C_8,A_60,A_45,A_6] : k2_xboole_0(k1_enumset1(A_60,A_45,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k1_tarski(A_60),k2_enumset1(A_45,A_6,B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_139])).

tff(c_161,plain,(
    ! [B_7,C_8,A_60,A_45,A_6] : k2_xboole_0(k1_enumset1(A_60,A_45,A_6),k2_tarski(B_7,C_8)) = k3_enumset1(A_60,A_45,A_6,B_7,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_154])).

tff(c_88,plain,(
    ! [C_11,A_45,B_10,D_12,A_9] : k2_xboole_0(k2_tarski(A_45,A_9),k1_enumset1(B_10,C_11,D_12)) = k2_xboole_0(k1_tarski(A_45),k2_enumset1(A_9,B_10,C_11,D_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_276,plain,(
    ! [A_98,C_96,B_95,D_97,A_94] : k2_xboole_0(k2_tarski(A_94,A_98),k1_enumset1(B_95,C_96,D_97)) = k3_enumset1(A_94,A_98,B_95,C_96,D_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_475,plain,(
    ! [C_148,B_144,C_147,A_145,A_143,D_146] : k2_xboole_0(k2_tarski(A_143,A_145),k2_xboole_0(k1_enumset1(B_144,C_147,D_146),C_148)) = k2_xboole_0(k3_enumset1(A_143,A_145,B_144,C_147,D_146),C_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_2])).

tff(c_499,plain,(
    ! [B_7,C_8,A_60,A_145,A_143,A_45,A_6] : k2_xboole_0(k3_enumset1(A_143,A_145,A_60,A_45,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k2_tarski(A_143,A_145),k3_enumset1(A_60,A_45,A_6,B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_475])).

tff(c_508,plain,(
    ! [B_7,C_8,A_60,A_145,A_143,A_45,A_6] : k2_xboole_0(k3_enumset1(A_143,A_145,A_60,A_45,A_6),k2_tarski(B_7,C_8)) = k5_enumset1(A_143,A_145,A_60,A_45,A_6,B_7,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_499])).

tff(c_94,plain,(
    ! [A_45,A_4,B_5] : k2_xboole_0(k2_tarski(A_45,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_45),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_115,plain,(
    ! [A_53,A_54,B_55] : k2_xboole_0(k2_tarski(A_53,A_54),k1_tarski(B_55)) = k1_enumset1(A_53,A_54,B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_94])).

tff(c_121,plain,(
    ! [A_53,A_54,B_55,C_3] : k2_xboole_0(k2_tarski(A_53,A_54),k2_xboole_0(k1_tarski(B_55),C_3)) = k2_xboole_0(k1_enumset1(A_53,A_54,B_55),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2])).

tff(c_100,plain,(
    ! [B_49,E_50,D_48,C_52,A_51] : k2_xboole_0(k1_tarski(A_51),k2_enumset1(B_49,C_52,D_48,E_50)) = k3_enumset1(A_51,B_49,C_52,D_48,E_50) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_4,B_5,C_37] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_37)) = k2_xboole_0(k2_tarski(A_4,B_5),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_106,plain,(
    ! [B_49,E_50,D_48,A_4,C_52,A_51] : k2_xboole_0(k2_tarski(A_4,A_51),k2_enumset1(B_49,C_52,D_48,E_50)) = k2_xboole_0(k1_tarski(A_4),k3_enumset1(A_51,B_49,C_52,D_48,E_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_41])).

tff(c_127,plain,(
    ! [A_56,A_57,B_58,C_59] : k2_xboole_0(k2_tarski(A_56,A_57),k2_tarski(B_58,C_59)) = k2_enumset1(A_56,A_57,B_58,C_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_311,plain,(
    ! [B_107,C_108,A_110,A_109,C_111] : k2_xboole_0(k2_tarski(A_109,A_110),k2_xboole_0(k2_tarski(B_107,C_111),C_108)) = k2_xboole_0(k2_enumset1(A_109,A_110,B_107,C_111),C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_2])).

tff(c_341,plain,(
    ! [B_7,C_8,A_110,A_109,A_45,A_6] : k2_xboole_0(k2_enumset1(A_109,A_110,A_45,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k2_tarski(A_109,A_110),k2_enumset1(A_45,A_6,B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_311])).

tff(c_578,plain,(
    ! [B_7,C_8,A_110,A_109,A_45,A_6] : k2_xboole_0(k2_enumset1(A_109,A_110,A_45,A_6),k2_tarski(B_7,C_8)) = k2_xboole_0(k1_tarski(A_109),k3_enumset1(A_110,A_45,A_6,B_7,C_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_341])).

tff(c_392,plain,(
    ! [C_121,E_119,B_118,A_117,C_122,D_120] : k2_xboole_0(k1_tarski(A_117),k2_xboole_0(k2_enumset1(B_118,C_121,D_120,E_119),C_122)) = k2_xboole_0(k3_enumset1(A_117,B_118,C_121,D_120,E_119),C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2])).

tff(c_760,plain,(
    ! [A_225,D_220,E_219,B_222,C_221,C_224,A_223] : k2_xboole_0(k2_tarski(A_225,A_223),k2_xboole_0(k2_enumset1(B_222,C_224,D_220,E_219),C_221)) = k2_xboole_0(k1_tarski(A_225),k2_xboole_0(k3_enumset1(A_223,B_222,C_224,D_220,E_219),C_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_41])).

tff(c_790,plain,(
    ! [B_7,C_8,A_225,A_110,A_109,A_45,A_223,A_6] : k2_xboole_0(k2_tarski(A_225,A_223),k2_xboole_0(k1_tarski(A_109),k3_enumset1(A_110,A_45,A_6,B_7,C_8))) = k2_xboole_0(k1_tarski(A_225),k2_xboole_0(k3_enumset1(A_223,A_109,A_110,A_45,A_6),k2_tarski(B_7,C_8))) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_760])).

tff(c_802,plain,(
    ! [B_7,C_8,A_225,A_110,A_109,A_45,A_223,A_6] : k2_xboole_0(k1_enumset1(A_225,A_223,A_109),k3_enumset1(A_110,A_45,A_6,B_7,C_8)) = k6_enumset1(A_225,A_223,A_109,A_110,A_45,A_6,B_7,C_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_508,c_121,c_790])).

tff(c_99,plain,(
    ! [A_45,A_4,B_5] : k2_xboole_0(k2_tarski(A_45,A_4),k1_tarski(B_5)) = k1_enumset1(A_45,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_94])).

tff(c_157,plain,(
    ! [A_60,A_45,A_4,B_5] : k2_xboole_0(k1_enumset1(A_60,A_45,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_60),k1_enumset1(A_45,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_139])).

tff(c_162,plain,(
    ! [A_60,A_45,A_4,B_5] : k2_xboole_0(k1_enumset1(A_60,A_45,A_4),k1_tarski(B_5)) = k2_enumset1(A_60,A_45,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_157])).

tff(c_58,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_xboole_0(k1_tarski(A_41),k1_enumset1(B_42,C_43,D_44)) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_222,plain,(
    ! [C_78,A_77,C_80,B_81,D_79] : k2_xboole_0(k1_tarski(A_77),k2_xboole_0(k1_enumset1(B_81,C_78,D_79),C_80)) = k2_xboole_0(k2_enumset1(A_77,B_81,C_78,D_79),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2])).

tff(c_243,plain,(
    ! [B_5,A_60,A_4,A_77,A_45] : k2_xboole_0(k2_enumset1(A_77,A_60,A_45,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_77),k2_enumset1(A_60,A_45,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_222])).

tff(c_247,plain,(
    ! [B_5,A_60,A_4,A_77,A_45] : k2_xboole_0(k2_enumset1(A_77,A_60,A_45,A_4),k1_tarski(B_5)) = k3_enumset1(A_77,A_60,A_45,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_243])).

tff(c_260,plain,(
    ! [A_87,G_93,D_91,B_92,F_90,E_89,C_88] : k2_xboole_0(k2_tarski(A_87,B_92),k3_enumset1(C_88,D_91,E_89,F_90,G_93)) = k5_enumset1(A_87,B_92,C_88,D_91,E_89,F_90,G_93) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_269,plain,(
    ! [A_87,G_93,D_91,C_3,B_92,F_90,E_89,C_88] : k2_xboole_0(k2_tarski(A_87,B_92),k2_xboole_0(k3_enumset1(C_88,D_91,E_89,F_90,G_93),C_3)) = k2_xboole_0(k5_enumset1(A_87,B_92,C_88,D_91,E_89,F_90,G_93),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_2])).

tff(c_52,plain,(
    ! [A_38,B_39,C_40,C_3] : k2_xboole_0(k1_tarski(A_38),k2_xboole_0(k2_tarski(B_39,C_40),C_3)) = k2_xboole_0(k1_enumset1(A_38,B_39,C_40),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_772,plain,(
    ! [A_225,D_220,E_219,B_222,C_221,C_224,A_223,A_38] : k2_xboole_0(k1_tarski(A_38),k2_xboole_0(k1_tarski(A_225),k2_xboole_0(k3_enumset1(A_223,B_222,C_224,D_220,E_219),C_221))) = k2_xboole_0(k1_enumset1(A_38,A_225,A_223),k2_xboole_0(k2_enumset1(B_222,C_224,D_220,E_219),C_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_760,c_52])).

tff(c_825,plain,(
    ! [C_238,A_235,C_234,B_239,A_240,E_237,D_241,A_236] : k2_xboole_0(k1_enumset1(A_235,A_236,A_240),k2_xboole_0(k2_enumset1(B_239,C_238,D_241,E_237),C_234)) = k2_xboole_0(k5_enumset1(A_235,A_236,A_240,B_239,C_238,D_241,E_237),C_234) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_41,c_772])).

tff(c_855,plain,(
    ! [B_5,A_235,A_60,A_4,A_77,A_45,A_240,A_236] : k2_xboole_0(k5_enumset1(A_235,A_236,A_240,A_77,A_60,A_45,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_enumset1(A_235,A_236,A_240),k3_enumset1(A_77,A_60,A_45,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_825])).

tff(c_861,plain,(
    ! [B_5,A_235,A_60,A_4,A_77,A_45,A_240,A_236] : k2_xboole_0(k5_enumset1(A_235,A_236,A_240,A_77,A_60,A_45,A_4),k1_tarski(B_5)) = k6_enumset1(A_235,A_236,A_240,A_77,A_60,A_45,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_802,c_855])).

tff(c_16,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_861,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.48  
% 3.29/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.48  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.29/1.48  
% 3.29/1.48  %Foreground sorts:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Background operators:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Foreground operators:
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.48  
% 3.29/1.50  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 3.29/1.50  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 3.29/1.50  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 3.29/1.50  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.29/1.50  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.29/1.50  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.29/1.50  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.29/1.50  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 3.29/1.50  tff(c_14, plain, (![A_25, G_31, F_30, E_29, H_32, C_27, D_28, B_26]: (k2_xboole_0(k1_tarski(A_25), k5_enumset1(B_26, C_27, D_28, E_29, F_30, G_31, H_32))=k6_enumset1(A_25, B_26, C_27, D_28, E_29, F_30, G_31, H_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.50  tff(c_12, plain, (![E_22, G_24, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k2_tarski(A_18, B_19), k3_enumset1(C_20, D_21, E_22, F_23, G_24))=k5_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.50  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.50  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.50  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.50  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.50  tff(c_26, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k2_xboole_0(A_35, B_36), C_37)=k2_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.50  tff(c_70, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k1_tarski(B_46), C_47))=k2_xboole_0(k2_tarski(A_45, B_46), C_47))), inference(superposition, [status(thm), theory('equality')], [c_4, c_26])).
% 3.29/1.50  tff(c_91, plain, (![A_45, A_6, B_7, C_8]: (k2_xboole_0(k2_tarski(A_45, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k1_tarski(A_45), k1_enumset1(A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_70])).
% 3.29/1.50  tff(c_98, plain, (![A_45, A_6, B_7, C_8]: (k2_xboole_0(k2_tarski(A_45, A_6), k2_tarski(B_7, C_8))=k2_enumset1(A_45, A_6, B_7, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_91])).
% 3.29/1.50  tff(c_46, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(B_39, C_40))=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.50  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.50  tff(c_139, plain, (![A_60, B_61, C_62, C_63]: (k2_xboole_0(k1_tarski(A_60), k2_xboole_0(k2_tarski(B_61, C_62), C_63))=k2_xboole_0(k1_enumset1(A_60, B_61, C_62), C_63))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 3.29/1.50  tff(c_154, plain, (![B_7, C_8, A_60, A_45, A_6]: (k2_xboole_0(k1_enumset1(A_60, A_45, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k1_tarski(A_60), k2_enumset1(A_45, A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_139])).
% 3.29/1.50  tff(c_161, plain, (![B_7, C_8, A_60, A_45, A_6]: (k2_xboole_0(k1_enumset1(A_60, A_45, A_6), k2_tarski(B_7, C_8))=k3_enumset1(A_60, A_45, A_6, B_7, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_154])).
% 3.29/1.50  tff(c_88, plain, (![C_11, A_45, B_10, D_12, A_9]: (k2_xboole_0(k2_tarski(A_45, A_9), k1_enumset1(B_10, C_11, D_12))=k2_xboole_0(k1_tarski(A_45), k2_enumset1(A_9, B_10, C_11, D_12)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_70])).
% 3.29/1.50  tff(c_276, plain, (![A_98, C_96, B_95, D_97, A_94]: (k2_xboole_0(k2_tarski(A_94, A_98), k1_enumset1(B_95, C_96, D_97))=k3_enumset1(A_94, A_98, B_95, C_96, D_97))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_88])).
% 3.29/1.50  tff(c_475, plain, (![C_148, B_144, C_147, A_145, A_143, D_146]: (k2_xboole_0(k2_tarski(A_143, A_145), k2_xboole_0(k1_enumset1(B_144, C_147, D_146), C_148))=k2_xboole_0(k3_enumset1(A_143, A_145, B_144, C_147, D_146), C_148))), inference(superposition, [status(thm), theory('equality')], [c_276, c_2])).
% 3.29/1.50  tff(c_499, plain, (![B_7, C_8, A_60, A_145, A_143, A_45, A_6]: (k2_xboole_0(k3_enumset1(A_143, A_145, A_60, A_45, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k2_tarski(A_143, A_145), k3_enumset1(A_60, A_45, A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_475])).
% 3.29/1.50  tff(c_508, plain, (![B_7, C_8, A_60, A_145, A_143, A_45, A_6]: (k2_xboole_0(k3_enumset1(A_143, A_145, A_60, A_45, A_6), k2_tarski(B_7, C_8))=k5_enumset1(A_143, A_145, A_60, A_45, A_6, B_7, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_499])).
% 3.29/1.50  tff(c_94, plain, (![A_45, A_4, B_5]: (k2_xboole_0(k2_tarski(A_45, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_45), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_70])).
% 3.29/1.50  tff(c_115, plain, (![A_53, A_54, B_55]: (k2_xboole_0(k2_tarski(A_53, A_54), k1_tarski(B_55))=k1_enumset1(A_53, A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_94])).
% 3.29/1.50  tff(c_121, plain, (![A_53, A_54, B_55, C_3]: (k2_xboole_0(k2_tarski(A_53, A_54), k2_xboole_0(k1_tarski(B_55), C_3))=k2_xboole_0(k1_enumset1(A_53, A_54, B_55), C_3))), inference(superposition, [status(thm), theory('equality')], [c_115, c_2])).
% 3.29/1.50  tff(c_100, plain, (![B_49, E_50, D_48, C_52, A_51]: (k2_xboole_0(k1_tarski(A_51), k2_enumset1(B_49, C_52, D_48, E_50))=k3_enumset1(A_51, B_49, C_52, D_48, E_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.50  tff(c_41, plain, (![A_4, B_5, C_37]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_37))=k2_xboole_0(k2_tarski(A_4, B_5), C_37))), inference(superposition, [status(thm), theory('equality')], [c_4, c_26])).
% 3.29/1.50  tff(c_106, plain, (![B_49, E_50, D_48, A_4, C_52, A_51]: (k2_xboole_0(k2_tarski(A_4, A_51), k2_enumset1(B_49, C_52, D_48, E_50))=k2_xboole_0(k1_tarski(A_4), k3_enumset1(A_51, B_49, C_52, D_48, E_50)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_41])).
% 3.29/1.50  tff(c_127, plain, (![A_56, A_57, B_58, C_59]: (k2_xboole_0(k2_tarski(A_56, A_57), k2_tarski(B_58, C_59))=k2_enumset1(A_56, A_57, B_58, C_59))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_91])).
% 3.29/1.50  tff(c_311, plain, (![B_107, C_108, A_110, A_109, C_111]: (k2_xboole_0(k2_tarski(A_109, A_110), k2_xboole_0(k2_tarski(B_107, C_111), C_108))=k2_xboole_0(k2_enumset1(A_109, A_110, B_107, C_111), C_108))), inference(superposition, [status(thm), theory('equality')], [c_127, c_2])).
% 3.29/1.50  tff(c_341, plain, (![B_7, C_8, A_110, A_109, A_45, A_6]: (k2_xboole_0(k2_enumset1(A_109, A_110, A_45, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k2_tarski(A_109, A_110), k2_enumset1(A_45, A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_311])).
% 3.29/1.50  tff(c_578, plain, (![B_7, C_8, A_110, A_109, A_45, A_6]: (k2_xboole_0(k2_enumset1(A_109, A_110, A_45, A_6), k2_tarski(B_7, C_8))=k2_xboole_0(k1_tarski(A_109), k3_enumset1(A_110, A_45, A_6, B_7, C_8)))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_341])).
% 3.29/1.50  tff(c_392, plain, (![C_121, E_119, B_118, A_117, C_122, D_120]: (k2_xboole_0(k1_tarski(A_117), k2_xboole_0(k2_enumset1(B_118, C_121, D_120, E_119), C_122))=k2_xboole_0(k3_enumset1(A_117, B_118, C_121, D_120, E_119), C_122))), inference(superposition, [status(thm), theory('equality')], [c_100, c_2])).
% 3.29/1.50  tff(c_760, plain, (![A_225, D_220, E_219, B_222, C_221, C_224, A_223]: (k2_xboole_0(k2_tarski(A_225, A_223), k2_xboole_0(k2_enumset1(B_222, C_224, D_220, E_219), C_221))=k2_xboole_0(k1_tarski(A_225), k2_xboole_0(k3_enumset1(A_223, B_222, C_224, D_220, E_219), C_221)))), inference(superposition, [status(thm), theory('equality')], [c_392, c_41])).
% 3.29/1.50  tff(c_790, plain, (![B_7, C_8, A_225, A_110, A_109, A_45, A_223, A_6]: (k2_xboole_0(k2_tarski(A_225, A_223), k2_xboole_0(k1_tarski(A_109), k3_enumset1(A_110, A_45, A_6, B_7, C_8)))=k2_xboole_0(k1_tarski(A_225), k2_xboole_0(k3_enumset1(A_223, A_109, A_110, A_45, A_6), k2_tarski(B_7, C_8))))), inference(superposition, [status(thm), theory('equality')], [c_578, c_760])).
% 3.29/1.50  tff(c_802, plain, (![B_7, C_8, A_225, A_110, A_109, A_45, A_223, A_6]: (k2_xboole_0(k1_enumset1(A_225, A_223, A_109), k3_enumset1(A_110, A_45, A_6, B_7, C_8))=k6_enumset1(A_225, A_223, A_109, A_110, A_45, A_6, B_7, C_8))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_508, c_121, c_790])).
% 3.29/1.50  tff(c_99, plain, (![A_45, A_4, B_5]: (k2_xboole_0(k2_tarski(A_45, A_4), k1_tarski(B_5))=k1_enumset1(A_45, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_94])).
% 3.29/1.50  tff(c_157, plain, (![A_60, A_45, A_4, B_5]: (k2_xboole_0(k1_enumset1(A_60, A_45, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_60), k1_enumset1(A_45, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_139])).
% 3.29/1.50  tff(c_162, plain, (![A_60, A_45, A_4, B_5]: (k2_xboole_0(k1_enumset1(A_60, A_45, A_4), k1_tarski(B_5))=k2_enumset1(A_60, A_45, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_157])).
% 3.29/1.50  tff(c_58, plain, (![A_41, B_42, C_43, D_44]: (k2_xboole_0(k1_tarski(A_41), k1_enumset1(B_42, C_43, D_44))=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.50  tff(c_222, plain, (![C_78, A_77, C_80, B_81, D_79]: (k2_xboole_0(k1_tarski(A_77), k2_xboole_0(k1_enumset1(B_81, C_78, D_79), C_80))=k2_xboole_0(k2_enumset1(A_77, B_81, C_78, D_79), C_80))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2])).
% 3.29/1.50  tff(c_243, plain, (![B_5, A_60, A_4, A_77, A_45]: (k2_xboole_0(k2_enumset1(A_77, A_60, A_45, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_77), k2_enumset1(A_60, A_45, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_222])).
% 3.29/1.50  tff(c_247, plain, (![B_5, A_60, A_4, A_77, A_45]: (k2_xboole_0(k2_enumset1(A_77, A_60, A_45, A_4), k1_tarski(B_5))=k3_enumset1(A_77, A_60, A_45, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_243])).
% 3.29/1.50  tff(c_260, plain, (![A_87, G_93, D_91, B_92, F_90, E_89, C_88]: (k2_xboole_0(k2_tarski(A_87, B_92), k3_enumset1(C_88, D_91, E_89, F_90, G_93))=k5_enumset1(A_87, B_92, C_88, D_91, E_89, F_90, G_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.50  tff(c_269, plain, (![A_87, G_93, D_91, C_3, B_92, F_90, E_89, C_88]: (k2_xboole_0(k2_tarski(A_87, B_92), k2_xboole_0(k3_enumset1(C_88, D_91, E_89, F_90, G_93), C_3))=k2_xboole_0(k5_enumset1(A_87, B_92, C_88, D_91, E_89, F_90, G_93), C_3))), inference(superposition, [status(thm), theory('equality')], [c_260, c_2])).
% 3.29/1.50  tff(c_52, plain, (![A_38, B_39, C_40, C_3]: (k2_xboole_0(k1_tarski(A_38), k2_xboole_0(k2_tarski(B_39, C_40), C_3))=k2_xboole_0(k1_enumset1(A_38, B_39, C_40), C_3))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 3.29/1.50  tff(c_772, plain, (![A_225, D_220, E_219, B_222, C_221, C_224, A_223, A_38]: (k2_xboole_0(k1_tarski(A_38), k2_xboole_0(k1_tarski(A_225), k2_xboole_0(k3_enumset1(A_223, B_222, C_224, D_220, E_219), C_221)))=k2_xboole_0(k1_enumset1(A_38, A_225, A_223), k2_xboole_0(k2_enumset1(B_222, C_224, D_220, E_219), C_221)))), inference(superposition, [status(thm), theory('equality')], [c_760, c_52])).
% 3.29/1.50  tff(c_825, plain, (![C_238, A_235, C_234, B_239, A_240, E_237, D_241, A_236]: (k2_xboole_0(k1_enumset1(A_235, A_236, A_240), k2_xboole_0(k2_enumset1(B_239, C_238, D_241, E_237), C_234))=k2_xboole_0(k5_enumset1(A_235, A_236, A_240, B_239, C_238, D_241, E_237), C_234))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_41, c_772])).
% 3.29/1.50  tff(c_855, plain, (![B_5, A_235, A_60, A_4, A_77, A_45, A_240, A_236]: (k2_xboole_0(k5_enumset1(A_235, A_236, A_240, A_77, A_60, A_45, A_4), k1_tarski(B_5))=k2_xboole_0(k1_enumset1(A_235, A_236, A_240), k3_enumset1(A_77, A_60, A_45, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_247, c_825])).
% 3.29/1.50  tff(c_861, plain, (![B_5, A_235, A_60, A_4, A_77, A_45, A_240, A_236]: (k2_xboole_0(k5_enumset1(A_235, A_236, A_240, A_77, A_60, A_45, A_4), k1_tarski(B_5))=k6_enumset1(A_235, A_236, A_240, A_77, A_60, A_45, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_802, c_855])).
% 3.29/1.50  tff(c_16, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.29/1.50  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_861, c_16])).
% 3.29/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.50  
% 3.29/1.50  Inference rules
% 3.29/1.50  ----------------------
% 3.29/1.50  #Ref     : 0
% 3.29/1.50  #Sup     : 218
% 3.29/1.50  #Fact    : 0
% 3.29/1.50  #Define  : 0
% 3.29/1.50  #Split   : 0
% 3.29/1.50  #Chain   : 0
% 3.29/1.50  #Close   : 0
% 3.29/1.50  
% 3.29/1.50  Ordering : KBO
% 3.29/1.50  
% 3.29/1.50  Simplification rules
% 3.29/1.50  ----------------------
% 3.29/1.50  #Subsume      : 0
% 3.29/1.50  #Demod        : 146
% 3.29/1.50  #Tautology    : 119
% 3.29/1.50  #SimpNegUnit  : 0
% 3.29/1.50  #BackRed      : 1
% 3.29/1.50  
% 3.29/1.50  #Partial instantiations: 0
% 3.29/1.50  #Strategies tried      : 1
% 3.29/1.50  
% 3.29/1.50  Timing (in seconds)
% 3.29/1.50  ----------------------
% 3.29/1.50  Preprocessing        : 0.28
% 3.29/1.50  Parsing              : 0.15
% 3.29/1.50  CNF conversion       : 0.02
% 3.29/1.50  Main loop            : 0.45
% 3.29/1.50  Inferencing          : 0.20
% 3.29/1.50  Reduction            : 0.15
% 3.29/1.50  Demodulation         : 0.13
% 3.29/1.50  BG Simplification    : 0.03
% 3.29/1.50  Subsumption          : 0.05
% 3.29/1.50  Abstraction          : 0.04
% 3.29/1.50  MUC search           : 0.00
% 3.29/1.50  Cooper               : 0.00
% 3.29/1.50  Total                : 0.77
% 3.29/1.50  Index Insertion      : 0.00
% 3.29/1.50  Index Deletion       : 0.00
% 3.29/1.51  Index Matching       : 0.00
% 3.29/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
