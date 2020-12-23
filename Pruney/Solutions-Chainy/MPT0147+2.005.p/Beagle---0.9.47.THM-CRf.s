%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:56 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 137 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 ( 118 expanded)
%              Number of equality atoms :   46 ( 117 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_16,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] : k2_xboole_0(k3_enumset1(A_35,B_36,C_37,D_38,E_39),k1_tarski(F_40)) = k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k2_xboole_0(k2_enumset1(A_30,B_31,C_32,D_33),k1_tarski(E_34)) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_57,B_59,D_56,C_58,E_60] : k2_xboole_0(k1_tarski(A_57),k2_enumset1(B_59,C_58,D_56,E_60)) = k3_enumset1(A_57,B_59,C_58,D_56,E_60) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_159,plain,(
    ! [C_89,C_92,B_88,E_91,A_93,D_90] : k2_xboole_0(k1_tarski(A_93),k2_xboole_0(k2_enumset1(B_88,C_89,D_90,E_91),C_92)) = k2_xboole_0(k3_enumset1(A_93,B_88,C_89,D_90,E_91),C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2])).

tff(c_174,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,A_93] : k2_xboole_0(k3_enumset1(A_93,A_30,B_31,C_32,D_33),k1_tarski(E_34)) = k2_xboole_0(k1_tarski(A_93),k3_enumset1(A_30,B_31,C_32,D_33,E_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_159])).

tff(c_179,plain,(
    ! [A_96,D_99,B_95,C_94,E_98,A_97] : k2_xboole_0(k1_tarski(A_96),k3_enumset1(A_97,B_95,C_94,D_99,E_98)) = k4_enumset1(A_96,A_97,B_95,C_94,D_99,E_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_174])).

tff(c_329,plain,(
    ! [A_143,C_144,E_148,D_147,A_142,B_145,C_146] : k2_xboole_0(k1_tarski(A_143),k2_xboole_0(k3_enumset1(A_142,B_145,C_144,D_147,E_148),C_146)) = k2_xboole_0(k4_enumset1(A_143,A_142,B_145,C_144,D_147,E_148),C_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_2])).

tff(c_353,plain,(
    ! [A_35,F_40,B_36,A_143,C_37,D_38,E_39] : k2_xboole_0(k4_enumset1(A_143,A_35,B_36,C_37,D_38,E_39),k1_tarski(F_40)) = k2_xboole_0(k1_tarski(A_143),k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_329])).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] : k2_xboole_0(k1_enumset1(A_4,B_5,C_6),k1_enumset1(D_7,E_8,F_9)) = k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k1_tarski(A_21),k1_enumset1(B_22,C_23,D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k2_tarski(A_18,B_19),k1_tarski(C_20)) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k2_xboole_0(A_44,B_45),C_46) = k2_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_67,B_68,C_69,C_70] : k2_xboole_0(k2_tarski(A_67,B_68),k2_xboole_0(k1_tarski(C_69),C_70)) = k2_xboole_0(k1_enumset1(A_67,B_68,C_69),C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_28])).

tff(c_111,plain,(
    ! [A_21,B_22,D_24,C_23,B_68,A_67] : k2_xboole_0(k1_enumset1(A_67,B_68,A_21),k1_enumset1(B_22,C_23,D_24)) = k2_xboole_0(k2_tarski(A_67,B_68),k2_enumset1(A_21,B_22,C_23,D_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_147,plain,(
    ! [C_85,B_87,D_84,B_82,A_83,A_86] : k2_xboole_0(k2_tarski(A_86,B_82),k2_enumset1(A_83,B_87,C_85,D_84)) = k4_enumset1(A_86,B_82,A_83,B_87,C_85,D_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_111])).

tff(c_357,plain,(
    ! [B_155,C_152,A_150,A_153,B_151,C_149,D_154] : k2_xboole_0(k2_tarski(A_150,B_155),k2_xboole_0(k2_enumset1(A_153,B_151,C_149,D_154),C_152)) = k2_xboole_0(k4_enumset1(A_150,B_155,A_153,B_151,C_149,D_154),C_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_2])).

tff(c_378,plain,(
    ! [B_155,D_33,A_30,C_32,A_150,B_31,E_34] : k2_xboole_0(k4_enumset1(A_150,B_155,A_30,B_31,C_32,D_33),k1_tarski(E_34)) = k2_xboole_0(k2_tarski(A_150,B_155),k3_enumset1(A_30,B_31,C_32,D_33,E_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_357])).

tff(c_396,plain,(
    ! [B_155,D_33,A_30,C_32,A_150,B_31,E_34] : k2_xboole_0(k2_tarski(A_150,B_155),k3_enumset1(A_30,B_31,C_32,D_33,E_34)) = k2_xboole_0(k1_tarski(A_150),k4_enumset1(B_155,A_30,B_31,C_32,D_33,E_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_378])).

tff(c_6,plain,(
    ! [H_17,B_11,A_10,C_12,G_16,F_15,E_14,D_13] : k2_xboole_0(k2_enumset1(A_10,B_11,C_12,D_13),k2_enumset1(E_14,F_15,G_16,H_17)) = k6_enumset1(A_10,B_11,C_12,D_13,E_14,F_15,G_16,H_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : k2_xboole_0(k1_tarski(A_25),k2_enumset1(B_26,C_27,D_28,E_29)) = k3_enumset1(A_25,B_26,C_27,D_28,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_293,plain,(
    ! [B_133,C_132,A_130,E_134,A_131,D_129,B_128] : k2_xboole_0(k1_enumset1(A_131,B_128,A_130),k2_enumset1(B_133,C_132,D_129,E_134)) = k2_xboole_0(k2_tarski(A_131,B_128),k3_enumset1(A_130,B_133,C_132,D_129,E_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_48,plain,(
    ! [A_47,B_48,C_49,D_50] : k2_xboole_0(k1_tarski(A_47),k1_enumset1(B_48,C_49,D_50)) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_47,C_3,D_50,C_49,B_48] : k2_xboole_0(k1_tarski(A_47),k2_xboole_0(k1_enumset1(B_48,C_49,D_50),C_3)) = k2_xboole_0(k2_enumset1(A_47,B_48,C_49,D_50),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_302,plain,(
    ! [B_133,A_47,C_132,A_130,E_134,A_131,D_129,B_128] : k2_xboole_0(k1_tarski(A_47),k2_xboole_0(k2_tarski(A_131,B_128),k3_enumset1(A_130,B_133,C_132,D_129,E_134))) = k2_xboole_0(k2_enumset1(A_47,A_131,B_128,A_130),k2_enumset1(B_133,C_132,D_129,E_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_54])).

tff(c_310,plain,(
    ! [B_133,A_47,C_132,A_130,E_134,A_131,D_129,B_128] : k2_xboole_0(k1_tarski(A_47),k2_xboole_0(k2_tarski(A_131,B_128),k3_enumset1(A_130,B_133,C_132,D_129,E_134))) = k6_enumset1(A_47,A_131,B_128,A_130,B_133,C_132,D_129,E_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_302])).

tff(c_519,plain,(
    ! [B_133,A_47,C_132,A_130,E_134,A_131,D_129,B_128] : k2_xboole_0(k1_tarski(A_47),k2_xboole_0(k1_tarski(A_131),k4_enumset1(B_128,A_130,B_133,C_132,D_129,E_134))) = k6_enumset1(A_47,A_131,B_128,A_130,B_133,C_132,D_129,E_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_310])).

tff(c_116,plain,(
    ! [C_73,E_74,F_72,D_75,A_71,B_76] : k2_xboole_0(k3_enumset1(A_71,B_76,C_73,D_75,E_74),k1_tarski(F_72)) = k4_enumset1(A_71,B_76,C_73,D_75,E_74,F_72) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [C_73,C_3,E_74,F_72,D_75,A_71,B_76] : k2_xboole_0(k3_enumset1(A_71,B_76,C_73,D_75,E_74),k2_xboole_0(k1_tarski(F_72),C_3)) = k2_xboole_0(k4_enumset1(A_71,B_76,C_73,D_75,E_74,F_72),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2])).

tff(c_350,plain,(
    ! [C_73,C_3,A_143,E_74,F_72,D_75,A_71,B_76] : k2_xboole_0(k4_enumset1(A_143,A_71,B_76,C_73,D_75,E_74),k2_xboole_0(k1_tarski(F_72),C_3)) = k2_xboole_0(k1_tarski(A_143),k2_xboole_0(k4_enumset1(A_71,B_76,C_73,D_75,E_74,F_72),C_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_329])).

tff(c_60,plain,(
    ! [D_55,B_52,A_53,C_51,E_54] : k2_xboole_0(k2_enumset1(A_53,B_52,C_51,D_55),k1_tarski(E_54)) = k3_enumset1(A_53,B_52,C_51,D_55,E_54) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [D_55,B_52,A_53,C_51,E_54,C_3] : k2_xboole_0(k2_enumset1(A_53,B_52,C_51,D_55),k2_xboole_0(k1_tarski(E_54),C_3)) = k2_xboole_0(k3_enumset1(A_53,B_52,C_51,D_55,E_54),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_375,plain,(
    ! [B_155,D_55,B_52,A_53,C_51,E_54,C_3,A_150] : k2_xboole_0(k4_enumset1(A_150,B_155,A_53,B_52,C_51,D_55),k2_xboole_0(k1_tarski(E_54),C_3)) = k2_xboole_0(k2_tarski(A_150,B_155),k2_xboole_0(k3_enumset1(A_53,B_52,C_51,D_55,E_54),C_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_357])).

tff(c_827,plain,(
    ! [A_315,B_317,C_318,C_321,A_322,D_320,B_319,E_316] : k2_xboole_0(k2_tarski(A_322,B_319),k2_xboole_0(k3_enumset1(A_315,B_317,C_318,D_320,E_316),C_321)) = k2_xboole_0(k1_tarski(A_322),k2_xboole_0(k4_enumset1(B_319,A_315,B_317,C_318,D_320,E_316),C_321)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_375])).

tff(c_851,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39,A_322,B_319] : k2_xboole_0(k1_tarski(A_322),k2_xboole_0(k4_enumset1(B_319,A_35,B_36,C_37,D_38,E_39),k1_tarski(F_40))) = k2_xboole_0(k2_tarski(A_322,B_319),k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_827])).

tff(c_858,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39,A_322,B_319] : k2_xboole_0(k2_tarski(A_322,B_319),k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40)) = k6_enumset1(A_322,B_319,A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_353,c_851])).

tff(c_18,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.61  
% 3.78/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.61  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.78/1.61  
% 3.78/1.61  %Foreground sorts:
% 3.78/1.61  
% 3.78/1.61  
% 3.78/1.61  %Background operators:
% 3.78/1.61  
% 3.78/1.61  
% 3.78/1.61  %Foreground operators:
% 3.78/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.78/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.78/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.78/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.78/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.78/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.78/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.78/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.78/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.78/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.78/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.78/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.78/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.78/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.78/1.61  
% 3.78/1.63  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 3.78/1.63  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 3.78/1.63  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 3.78/1.63  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.78/1.63  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 3.78/1.63  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.78/1.63  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.78/1.63  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 3.78/1.63  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 3.78/1.63  tff(c_16, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k2_xboole_0(k3_enumset1(A_35, B_36, C_37, D_38, E_39), k1_tarski(F_40))=k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.78/1.63  tff(c_14, plain, (![D_33, A_30, C_32, B_31, E_34]: (k2_xboole_0(k2_enumset1(A_30, B_31, C_32, D_33), k1_tarski(E_34))=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.78/1.63  tff(c_72, plain, (![A_57, B_59, D_56, C_58, E_60]: (k2_xboole_0(k1_tarski(A_57), k2_enumset1(B_59, C_58, D_56, E_60))=k3_enumset1(A_57, B_59, C_58, D_56, E_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.78/1.63  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.78/1.63  tff(c_159, plain, (![C_89, C_92, B_88, E_91, A_93, D_90]: (k2_xboole_0(k1_tarski(A_93), k2_xboole_0(k2_enumset1(B_88, C_89, D_90, E_91), C_92))=k2_xboole_0(k3_enumset1(A_93, B_88, C_89, D_90, E_91), C_92))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2])).
% 3.78/1.63  tff(c_174, plain, (![D_33, A_30, C_32, B_31, E_34, A_93]: (k2_xboole_0(k3_enumset1(A_93, A_30, B_31, C_32, D_33), k1_tarski(E_34))=k2_xboole_0(k1_tarski(A_93), k3_enumset1(A_30, B_31, C_32, D_33, E_34)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_159])).
% 3.78/1.63  tff(c_179, plain, (![A_96, D_99, B_95, C_94, E_98, A_97]: (k2_xboole_0(k1_tarski(A_96), k3_enumset1(A_97, B_95, C_94, D_99, E_98))=k4_enumset1(A_96, A_97, B_95, C_94, D_99, E_98))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_174])).
% 3.78/1.63  tff(c_329, plain, (![A_143, C_144, E_148, D_147, A_142, B_145, C_146]: (k2_xboole_0(k1_tarski(A_143), k2_xboole_0(k3_enumset1(A_142, B_145, C_144, D_147, E_148), C_146))=k2_xboole_0(k4_enumset1(A_143, A_142, B_145, C_144, D_147, E_148), C_146))), inference(superposition, [status(thm), theory('equality')], [c_179, c_2])).
% 3.78/1.63  tff(c_353, plain, (![A_35, F_40, B_36, A_143, C_37, D_38, E_39]: (k2_xboole_0(k4_enumset1(A_143, A_35, B_36, C_37, D_38, E_39), k1_tarski(F_40))=k2_xboole_0(k1_tarski(A_143), k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_329])).
% 3.78/1.63  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6, F_9]: (k2_xboole_0(k1_enumset1(A_4, B_5, C_6), k1_enumset1(D_7, E_8, F_9))=k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.78/1.63  tff(c_10, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k1_tarski(A_21), k1_enumset1(B_22, C_23, D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.78/1.63  tff(c_8, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_tarski(C_20))=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.78/1.63  tff(c_28, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k2_xboole_0(A_44, B_45), C_46)=k2_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.78/1.63  tff(c_96, plain, (![A_67, B_68, C_69, C_70]: (k2_xboole_0(k2_tarski(A_67, B_68), k2_xboole_0(k1_tarski(C_69), C_70))=k2_xboole_0(k1_enumset1(A_67, B_68, C_69), C_70))), inference(superposition, [status(thm), theory('equality')], [c_8, c_28])).
% 3.78/1.63  tff(c_111, plain, (![A_21, B_22, D_24, C_23, B_68, A_67]: (k2_xboole_0(k1_enumset1(A_67, B_68, A_21), k1_enumset1(B_22, C_23, D_24))=k2_xboole_0(k2_tarski(A_67, B_68), k2_enumset1(A_21, B_22, C_23, D_24)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_96])).
% 3.78/1.63  tff(c_147, plain, (![C_85, B_87, D_84, B_82, A_83, A_86]: (k2_xboole_0(k2_tarski(A_86, B_82), k2_enumset1(A_83, B_87, C_85, D_84))=k4_enumset1(A_86, B_82, A_83, B_87, C_85, D_84))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_111])).
% 3.78/1.63  tff(c_357, plain, (![B_155, C_152, A_150, A_153, B_151, C_149, D_154]: (k2_xboole_0(k2_tarski(A_150, B_155), k2_xboole_0(k2_enumset1(A_153, B_151, C_149, D_154), C_152))=k2_xboole_0(k4_enumset1(A_150, B_155, A_153, B_151, C_149, D_154), C_152))), inference(superposition, [status(thm), theory('equality')], [c_147, c_2])).
% 3.78/1.63  tff(c_378, plain, (![B_155, D_33, A_30, C_32, A_150, B_31, E_34]: (k2_xboole_0(k4_enumset1(A_150, B_155, A_30, B_31, C_32, D_33), k1_tarski(E_34))=k2_xboole_0(k2_tarski(A_150, B_155), k3_enumset1(A_30, B_31, C_32, D_33, E_34)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_357])).
% 3.78/1.63  tff(c_396, plain, (![B_155, D_33, A_30, C_32, A_150, B_31, E_34]: (k2_xboole_0(k2_tarski(A_150, B_155), k3_enumset1(A_30, B_31, C_32, D_33, E_34))=k2_xboole_0(k1_tarski(A_150), k4_enumset1(B_155, A_30, B_31, C_32, D_33, E_34)))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_378])).
% 3.78/1.63  tff(c_6, plain, (![H_17, B_11, A_10, C_12, G_16, F_15, E_14, D_13]: (k2_xboole_0(k2_enumset1(A_10, B_11, C_12, D_13), k2_enumset1(E_14, F_15, G_16, H_17))=k6_enumset1(A_10, B_11, C_12, D_13, E_14, F_15, G_16, H_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.78/1.63  tff(c_12, plain, (![A_25, E_29, C_27, D_28, B_26]: (k2_xboole_0(k1_tarski(A_25), k2_enumset1(B_26, C_27, D_28, E_29))=k3_enumset1(A_25, B_26, C_27, D_28, E_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.78/1.63  tff(c_293, plain, (![B_133, C_132, A_130, E_134, A_131, D_129, B_128]: (k2_xboole_0(k1_enumset1(A_131, B_128, A_130), k2_enumset1(B_133, C_132, D_129, E_134))=k2_xboole_0(k2_tarski(A_131, B_128), k3_enumset1(A_130, B_133, C_132, D_129, E_134)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_96])).
% 3.78/1.63  tff(c_48, plain, (![A_47, B_48, C_49, D_50]: (k2_xboole_0(k1_tarski(A_47), k1_enumset1(B_48, C_49, D_50))=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.78/1.63  tff(c_54, plain, (![A_47, C_3, D_50, C_49, B_48]: (k2_xboole_0(k1_tarski(A_47), k2_xboole_0(k1_enumset1(B_48, C_49, D_50), C_3))=k2_xboole_0(k2_enumset1(A_47, B_48, C_49, D_50), C_3))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2])).
% 3.78/1.63  tff(c_302, plain, (![B_133, A_47, C_132, A_130, E_134, A_131, D_129, B_128]: (k2_xboole_0(k1_tarski(A_47), k2_xboole_0(k2_tarski(A_131, B_128), k3_enumset1(A_130, B_133, C_132, D_129, E_134)))=k2_xboole_0(k2_enumset1(A_47, A_131, B_128, A_130), k2_enumset1(B_133, C_132, D_129, E_134)))), inference(superposition, [status(thm), theory('equality')], [c_293, c_54])).
% 3.78/1.63  tff(c_310, plain, (![B_133, A_47, C_132, A_130, E_134, A_131, D_129, B_128]: (k2_xboole_0(k1_tarski(A_47), k2_xboole_0(k2_tarski(A_131, B_128), k3_enumset1(A_130, B_133, C_132, D_129, E_134)))=k6_enumset1(A_47, A_131, B_128, A_130, B_133, C_132, D_129, E_134))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_302])).
% 3.78/1.63  tff(c_519, plain, (![B_133, A_47, C_132, A_130, E_134, A_131, D_129, B_128]: (k2_xboole_0(k1_tarski(A_47), k2_xboole_0(k1_tarski(A_131), k4_enumset1(B_128, A_130, B_133, C_132, D_129, E_134)))=k6_enumset1(A_47, A_131, B_128, A_130, B_133, C_132, D_129, E_134))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_310])).
% 3.78/1.63  tff(c_116, plain, (![C_73, E_74, F_72, D_75, A_71, B_76]: (k2_xboole_0(k3_enumset1(A_71, B_76, C_73, D_75, E_74), k1_tarski(F_72))=k4_enumset1(A_71, B_76, C_73, D_75, E_74, F_72))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.78/1.63  tff(c_122, plain, (![C_73, C_3, E_74, F_72, D_75, A_71, B_76]: (k2_xboole_0(k3_enumset1(A_71, B_76, C_73, D_75, E_74), k2_xboole_0(k1_tarski(F_72), C_3))=k2_xboole_0(k4_enumset1(A_71, B_76, C_73, D_75, E_74, F_72), C_3))), inference(superposition, [status(thm), theory('equality')], [c_116, c_2])).
% 3.78/1.63  tff(c_350, plain, (![C_73, C_3, A_143, E_74, F_72, D_75, A_71, B_76]: (k2_xboole_0(k4_enumset1(A_143, A_71, B_76, C_73, D_75, E_74), k2_xboole_0(k1_tarski(F_72), C_3))=k2_xboole_0(k1_tarski(A_143), k2_xboole_0(k4_enumset1(A_71, B_76, C_73, D_75, E_74, F_72), C_3)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_329])).
% 3.78/1.63  tff(c_60, plain, (![D_55, B_52, A_53, C_51, E_54]: (k2_xboole_0(k2_enumset1(A_53, B_52, C_51, D_55), k1_tarski(E_54))=k3_enumset1(A_53, B_52, C_51, D_55, E_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.78/1.63  tff(c_66, plain, (![D_55, B_52, A_53, C_51, E_54, C_3]: (k2_xboole_0(k2_enumset1(A_53, B_52, C_51, D_55), k2_xboole_0(k1_tarski(E_54), C_3))=k2_xboole_0(k3_enumset1(A_53, B_52, C_51, D_55, E_54), C_3))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2])).
% 3.78/1.63  tff(c_375, plain, (![B_155, D_55, B_52, A_53, C_51, E_54, C_3, A_150]: (k2_xboole_0(k4_enumset1(A_150, B_155, A_53, B_52, C_51, D_55), k2_xboole_0(k1_tarski(E_54), C_3))=k2_xboole_0(k2_tarski(A_150, B_155), k2_xboole_0(k3_enumset1(A_53, B_52, C_51, D_55, E_54), C_3)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_357])).
% 3.78/1.63  tff(c_827, plain, (![A_315, B_317, C_318, C_321, A_322, D_320, B_319, E_316]: (k2_xboole_0(k2_tarski(A_322, B_319), k2_xboole_0(k3_enumset1(A_315, B_317, C_318, D_320, E_316), C_321))=k2_xboole_0(k1_tarski(A_322), k2_xboole_0(k4_enumset1(B_319, A_315, B_317, C_318, D_320, E_316), C_321)))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_375])).
% 3.78/1.63  tff(c_851, plain, (![A_35, F_40, B_36, C_37, D_38, E_39, A_322, B_319]: (k2_xboole_0(k1_tarski(A_322), k2_xboole_0(k4_enumset1(B_319, A_35, B_36, C_37, D_38, E_39), k1_tarski(F_40)))=k2_xboole_0(k2_tarski(A_322, B_319), k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_827])).
% 3.78/1.63  tff(c_858, plain, (![A_35, F_40, B_36, C_37, D_38, E_39, A_322, B_319]: (k2_xboole_0(k2_tarski(A_322, B_319), k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))=k6_enumset1(A_322, B_319, A_35, B_36, C_37, D_38, E_39, F_40))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_353, c_851])).
% 3.78/1.63  tff(c_18, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.78/1.63  tff(c_875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_858, c_18])).
% 3.78/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.63  
% 3.78/1.63  Inference rules
% 3.78/1.63  ----------------------
% 3.78/1.63  #Ref     : 0
% 3.78/1.63  #Sup     : 218
% 3.78/1.63  #Fact    : 0
% 3.78/1.63  #Define  : 0
% 3.78/1.63  #Split   : 0
% 3.78/1.63  #Chain   : 0
% 3.78/1.63  #Close   : 0
% 3.78/1.63  
% 3.78/1.63  Ordering : KBO
% 3.78/1.63  
% 3.78/1.63  Simplification rules
% 3.78/1.63  ----------------------
% 3.78/1.63  #Subsume      : 0
% 3.78/1.63  #Demod        : 121
% 3.78/1.63  #Tautology    : 107
% 3.78/1.63  #SimpNegUnit  : 0
% 3.78/1.63  #BackRed      : 7
% 3.78/1.63  
% 3.78/1.63  #Partial instantiations: 0
% 3.78/1.63  #Strategies tried      : 1
% 3.78/1.63  
% 3.78/1.63  Timing (in seconds)
% 3.78/1.63  ----------------------
% 3.78/1.63  Preprocessing        : 0.30
% 3.78/1.63  Parsing              : 0.17
% 3.78/1.63  CNF conversion       : 0.02
% 3.78/1.63  Main loop            : 0.57
% 3.78/1.63  Inferencing          : 0.26
% 3.78/1.63  Reduction            : 0.20
% 3.78/1.63  Demodulation         : 0.16
% 3.78/1.63  BG Simplification    : 0.04
% 3.78/1.63  Subsumption          : 0.06
% 3.78/1.63  Abstraction          : 0.05
% 3.78/1.64  MUC search           : 0.00
% 3.78/1.64  Cooper               : 0.00
% 3.78/1.64  Total                : 0.91
% 3.78/1.64  Index Insertion      : 0.00
% 3.78/1.64  Index Deletion       : 0.00
% 3.78/1.64  Index Matching       : 0.00
% 3.78/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
