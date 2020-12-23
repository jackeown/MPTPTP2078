%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:46 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 143 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   48 ( 124 expanded)
%              Number of equality atoms :   47 ( 123 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(c_16,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k1_enumset1(D_25,E_26,F_27)) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_tarski(A_14,B_15),k1_tarski(C_16)) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [A_40,B_41,C_42,D_43] : k2_xboole_0(k2_tarski(A_40,B_41),k2_tarski(C_42,D_43)) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_254,plain,(
    ! [C_85,A_82,C_84,D_83,B_86] : k2_xboole_0(k2_tarski(A_82,B_86),k2_xboole_0(k2_tarski(C_84,D_83),C_85)) = k2_xboole_0(k2_enumset1(A_82,B_86,C_84,D_83),C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_281,plain,(
    ! [A_82,C_16,A_14,B_86,B_15] : k2_xboole_0(k2_enumset1(A_82,B_86,A_14,B_15),k1_tarski(C_16)) = k2_xboole_0(k2_tarski(A_82,B_86),k1_enumset1(A_14,B_15,C_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_254])).

tff(c_14,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k2_xboole_0(k1_tarski(A_17),k2_enumset1(B_18,C_19,D_20,E_21)) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_xboole_0(k2_tarski(A_8,B_9),k2_tarski(C_10,D_11)) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k2_xboole_0(A_34,B_35),C_36) = k2_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k1_tarski(A_44),k2_xboole_0(k1_tarski(B_45),C_46)) = k2_xboole_0(k2_tarski(A_44,B_45),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_108,plain,(
    ! [A_44,A_12,B_13] : k2_xboole_0(k2_tarski(A_44,A_12),k1_tarski(B_13)) = k2_xboole_0(k1_tarski(A_44),k2_tarski(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_113,plain,(
    ! [A_47,A_48,B_49] : k2_xboole_0(k1_tarski(A_47),k2_tarski(A_48,B_49)) = k1_enumset1(A_47,A_48,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_108])).

tff(c_200,plain,(
    ! [A_67,A_68,B_69,C_70] : k2_xboole_0(k1_tarski(A_67),k2_xboole_0(k2_tarski(A_68,B_69),C_70)) = k2_xboole_0(k1_enumset1(A_67,A_68,B_69),C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_4])).

tff(c_221,plain,(
    ! [D_11,A_8,C_10,A_67,B_9] : k2_xboole_0(k1_enumset1(A_67,A_8,B_9),k2_tarski(C_10,D_11)) = k2_xboole_0(k1_tarski(A_67),k2_enumset1(A_8,B_9,C_10,D_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_200])).

tff(c_228,plain,(
    ! [D_11,A_8,C_10,A_67,B_9] : k2_xboole_0(k1_enumset1(A_67,A_8,B_9),k2_tarski(C_10,D_11)) = k3_enumset1(A_67,A_8,B_9,C_10,D_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_221])).

tff(c_66,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k2_tarski(A_37,B_38),k1_tarski(C_39)) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [A_59,B_60,C_61,C_62] : k2_xboole_0(k2_tarski(A_59,B_60),k2_xboole_0(k1_tarski(C_61),C_62)) = k2_xboole_0(k1_enumset1(A_59,B_60,C_61),C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_183,plain,(
    ! [A_59,B_60,A_12,B_13] : k2_xboole_0(k1_enumset1(A_59,B_60,A_12),k1_tarski(B_13)) = k2_xboole_0(k2_tarski(A_59,B_60),k2_tarski(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_159])).

tff(c_188,plain,(
    ! [A_63,B_64,A_65,B_66] : k2_xboole_0(k1_enumset1(A_63,B_64,A_65),k1_tarski(B_66)) = k2_enumset1(A_63,B_64,A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_183])).

tff(c_299,plain,(
    ! [A_95,C_96,B_92,B_93,A_94] : k2_xboole_0(k1_enumset1(A_95,B_92,A_94),k2_xboole_0(k1_tarski(B_93),C_96)) = k2_xboole_0(k2_enumset1(A_95,B_92,A_94,B_93),C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_4])).

tff(c_326,plain,(
    ! [A_95,B_92,A_12,B_13,A_94] : k2_xboole_0(k2_enumset1(A_95,B_92,A_94,A_12),k1_tarski(B_13)) = k2_xboole_0(k1_enumset1(A_95,B_92,A_94),k2_tarski(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_299])).

tff(c_333,plain,(
    ! [B_98,A_99,A_101,B_100,A_97] : k2_xboole_0(k2_tarski(A_101,B_100),k1_enumset1(A_97,A_99,B_98)) = k3_enumset1(A_101,B_100,A_97,A_99,B_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_228,c_326])).

tff(c_122,plain,(
    ! [A_47,A_48,B_49,C_5] : k2_xboole_0(k1_tarski(A_47),k2_xboole_0(k2_tarski(A_48,B_49),C_5)) = k2_xboole_0(k1_enumset1(A_47,A_48,B_49),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_4])).

tff(c_342,plain,(
    ! [B_98,A_47,A_99,A_101,B_100,A_97] : k2_xboole_0(k1_enumset1(A_47,A_101,B_100),k1_enumset1(A_97,A_99,B_98)) = k2_xboole_0(k1_tarski(A_47),k3_enumset1(A_101,B_100,A_97,A_99,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_122])).

tff(c_350,plain,(
    ! [B_98,A_47,A_99,A_101,B_100,A_97] : k2_xboole_0(k1_tarski(A_47),k3_enumset1(A_101,B_100,A_97,A_99,B_98)) = k4_enumset1(A_47,A_101,B_100,A_97,A_99,B_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_342])).

tff(c_144,plain,(
    ! [B_56,E_58,A_55,D_57,C_54] : k2_xboole_0(k1_tarski(A_55),k2_enumset1(B_56,C_54,D_57,E_58)) = k3_enumset1(A_55,B_56,C_54,D_57,E_58) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    ! [A_12,B_13,C_36] : k2_xboole_0(k1_tarski(A_12),k2_xboole_0(k1_tarski(B_13),C_36)) = k2_xboole_0(k2_tarski(A_12,B_13),C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_150,plain,(
    ! [B_56,E_58,A_55,A_12,D_57,C_54] : k2_xboole_0(k2_tarski(A_12,A_55),k2_enumset1(B_56,C_54,D_57,E_58)) = k2_xboole_0(k1_tarski(A_12),k3_enumset1(A_55,B_56,C_54,D_57,E_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_61])).

tff(c_465,plain,(
    ! [B_56,E_58,A_55,A_12,D_57,C_54] : k2_xboole_0(k2_tarski(A_12,A_55),k2_enumset1(B_56,C_54,D_57,E_58)) = k4_enumset1(A_12,A_55,B_56,C_54,D_57,E_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_150])).

tff(c_187,plain,(
    ! [A_59,B_60,A_12,B_13] : k2_xboole_0(k1_enumset1(A_59,B_60,A_12),k1_tarski(B_13)) = k2_enumset1(A_59,B_60,A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_183])).

tff(c_153,plain,(
    ! [B_56,E_58,A_55,C_5,D_57,C_54] : k2_xboole_0(k1_tarski(A_55),k2_xboole_0(k2_enumset1(B_56,C_54,D_57,E_58),C_5)) = k2_xboole_0(k3_enumset1(A_55,B_56,C_54,D_57,E_58),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_4])).

tff(c_119,plain,(
    ! [A_12,A_47,A_48,B_49] : k2_xboole_0(k2_tarski(A_12,A_47),k2_tarski(A_48,B_49)) = k2_xboole_0(k1_tarski(A_12),k1_enumset1(A_47,A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_61])).

tff(c_129,plain,(
    ! [A_50,A_51,A_52,B_53] : k2_xboole_0(k1_tarski(A_50),k1_enumset1(A_51,A_52,B_53)) = k2_enumset1(A_50,A_51,A_52,B_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_119])).

tff(c_392,plain,(
    ! [A_113,A_115,B_116,C_117,A_114] : k2_xboole_0(k1_tarski(A_114),k2_xboole_0(k1_enumset1(A_113,A_115,B_116),C_117)) = k2_xboole_0(k2_enumset1(A_114,A_113,A_115,B_116),C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_4])).

tff(c_404,plain,(
    ! [A_113,A_115,A_12,B_116,C_117,A_114] : k2_xboole_0(k2_tarski(A_12,A_114),k2_xboole_0(k1_enumset1(A_113,A_115,B_116),C_117)) = k2_xboole_0(k1_tarski(A_12),k2_xboole_0(k2_enumset1(A_114,A_113,A_115,B_116),C_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_61])).

tff(c_523,plain,(
    ! [A_145,A_143,C_144,B_147,A_148,A_146] : k2_xboole_0(k2_tarski(A_143,A_146),k2_xboole_0(k1_enumset1(A_145,A_148,B_147),C_144)) = k2_xboole_0(k3_enumset1(A_143,A_146,A_145,A_148,B_147),C_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_404])).

tff(c_553,plain,(
    ! [A_143,A_59,A_12,B_13,A_146,B_60] : k2_xboole_0(k3_enumset1(A_143,A_146,A_59,B_60,A_12),k1_tarski(B_13)) = k2_xboole_0(k2_tarski(A_143,A_146),k2_enumset1(A_59,B_60,A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_523])).

tff(c_558,plain,(
    ! [A_143,A_59,A_12,B_13,A_146,B_60] : k2_xboole_0(k3_enumset1(A_143,A_146,A_59,B_60,A_12),k1_tarski(B_13)) = k4_enumset1(A_143,A_146,A_59,B_60,A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_553])).

tff(c_18,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_tarski('#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:30:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.51  
% 2.68/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.51  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.68/1.51  
% 2.68/1.51  %Foreground sorts:
% 2.68/1.51  
% 2.68/1.51  
% 2.68/1.51  %Background operators:
% 2.68/1.51  
% 2.68/1.51  
% 2.68/1.51  %Foreground operators:
% 2.68/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.68/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.68/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.51  
% 2.86/1.53  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 2.86/1.53  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.86/1.53  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.86/1.53  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.86/1.53  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.86/1.53  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.86/1.53  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.86/1.53  tff(c_16, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k1_enumset1(D_25, E_26, F_27))=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.53  tff(c_12, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_tarski(C_16))=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.53  tff(c_78, plain, (![A_40, B_41, C_42, D_43]: (k2_xboole_0(k2_tarski(A_40, B_41), k2_tarski(C_42, D_43))=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.53  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.53  tff(c_254, plain, (![C_85, A_82, C_84, D_83, B_86]: (k2_xboole_0(k2_tarski(A_82, B_86), k2_xboole_0(k2_tarski(C_84, D_83), C_85))=k2_xboole_0(k2_enumset1(A_82, B_86, C_84, D_83), C_85))), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 2.86/1.53  tff(c_281, plain, (![A_82, C_16, A_14, B_86, B_15]: (k2_xboole_0(k2_enumset1(A_82, B_86, A_14, B_15), k1_tarski(C_16))=k2_xboole_0(k2_tarski(A_82, B_86), k1_enumset1(A_14, B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_254])).
% 2.86/1.53  tff(c_14, plain, (![E_21, D_20, C_19, B_18, A_17]: (k2_xboole_0(k1_tarski(A_17), k2_enumset1(B_18, C_19, D_20, E_21))=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.53  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k2_xboole_0(k2_tarski(A_8, B_9), k2_tarski(C_10, D_11))=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.53  tff(c_10, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.53  tff(c_46, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k2_xboole_0(A_34, B_35), C_36)=k2_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.53  tff(c_90, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k1_tarski(A_44), k2_xboole_0(k1_tarski(B_45), C_46))=k2_xboole_0(k2_tarski(A_44, B_45), C_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 2.86/1.53  tff(c_108, plain, (![A_44, A_12, B_13]: (k2_xboole_0(k2_tarski(A_44, A_12), k1_tarski(B_13))=k2_xboole_0(k1_tarski(A_44), k2_tarski(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 2.86/1.53  tff(c_113, plain, (![A_47, A_48, B_49]: (k2_xboole_0(k1_tarski(A_47), k2_tarski(A_48, B_49))=k1_enumset1(A_47, A_48, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_108])).
% 2.86/1.53  tff(c_200, plain, (![A_67, A_68, B_69, C_70]: (k2_xboole_0(k1_tarski(A_67), k2_xboole_0(k2_tarski(A_68, B_69), C_70))=k2_xboole_0(k1_enumset1(A_67, A_68, B_69), C_70))), inference(superposition, [status(thm), theory('equality')], [c_113, c_4])).
% 2.86/1.53  tff(c_221, plain, (![D_11, A_8, C_10, A_67, B_9]: (k2_xboole_0(k1_enumset1(A_67, A_8, B_9), k2_tarski(C_10, D_11))=k2_xboole_0(k1_tarski(A_67), k2_enumset1(A_8, B_9, C_10, D_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_200])).
% 2.86/1.53  tff(c_228, plain, (![D_11, A_8, C_10, A_67, B_9]: (k2_xboole_0(k1_enumset1(A_67, A_8, B_9), k2_tarski(C_10, D_11))=k3_enumset1(A_67, A_8, B_9, C_10, D_11))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_221])).
% 2.86/1.53  tff(c_66, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k2_tarski(A_37, B_38), k1_tarski(C_39))=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.53  tff(c_159, plain, (![A_59, B_60, C_61, C_62]: (k2_xboole_0(k2_tarski(A_59, B_60), k2_xboole_0(k1_tarski(C_61), C_62))=k2_xboole_0(k1_enumset1(A_59, B_60, C_61), C_62))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 2.86/1.53  tff(c_183, plain, (![A_59, B_60, A_12, B_13]: (k2_xboole_0(k1_enumset1(A_59, B_60, A_12), k1_tarski(B_13))=k2_xboole_0(k2_tarski(A_59, B_60), k2_tarski(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_159])).
% 2.86/1.53  tff(c_188, plain, (![A_63, B_64, A_65, B_66]: (k2_xboole_0(k1_enumset1(A_63, B_64, A_65), k1_tarski(B_66))=k2_enumset1(A_63, B_64, A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_183])).
% 2.86/1.53  tff(c_299, plain, (![A_95, C_96, B_92, B_93, A_94]: (k2_xboole_0(k1_enumset1(A_95, B_92, A_94), k2_xboole_0(k1_tarski(B_93), C_96))=k2_xboole_0(k2_enumset1(A_95, B_92, A_94, B_93), C_96))), inference(superposition, [status(thm), theory('equality')], [c_188, c_4])).
% 2.86/1.53  tff(c_326, plain, (![A_95, B_92, A_12, B_13, A_94]: (k2_xboole_0(k2_enumset1(A_95, B_92, A_94, A_12), k1_tarski(B_13))=k2_xboole_0(k1_enumset1(A_95, B_92, A_94), k2_tarski(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_299])).
% 2.86/1.53  tff(c_333, plain, (![B_98, A_99, A_101, B_100, A_97]: (k2_xboole_0(k2_tarski(A_101, B_100), k1_enumset1(A_97, A_99, B_98))=k3_enumset1(A_101, B_100, A_97, A_99, B_98))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_228, c_326])).
% 2.86/1.53  tff(c_122, plain, (![A_47, A_48, B_49, C_5]: (k2_xboole_0(k1_tarski(A_47), k2_xboole_0(k2_tarski(A_48, B_49), C_5))=k2_xboole_0(k1_enumset1(A_47, A_48, B_49), C_5))), inference(superposition, [status(thm), theory('equality')], [c_113, c_4])).
% 2.86/1.53  tff(c_342, plain, (![B_98, A_47, A_99, A_101, B_100, A_97]: (k2_xboole_0(k1_enumset1(A_47, A_101, B_100), k1_enumset1(A_97, A_99, B_98))=k2_xboole_0(k1_tarski(A_47), k3_enumset1(A_101, B_100, A_97, A_99, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_333, c_122])).
% 2.86/1.53  tff(c_350, plain, (![B_98, A_47, A_99, A_101, B_100, A_97]: (k2_xboole_0(k1_tarski(A_47), k3_enumset1(A_101, B_100, A_97, A_99, B_98))=k4_enumset1(A_47, A_101, B_100, A_97, A_99, B_98))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_342])).
% 2.86/1.53  tff(c_144, plain, (![B_56, E_58, A_55, D_57, C_54]: (k2_xboole_0(k1_tarski(A_55), k2_enumset1(B_56, C_54, D_57, E_58))=k3_enumset1(A_55, B_56, C_54, D_57, E_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.53  tff(c_61, plain, (![A_12, B_13, C_36]: (k2_xboole_0(k1_tarski(A_12), k2_xboole_0(k1_tarski(B_13), C_36))=k2_xboole_0(k2_tarski(A_12, B_13), C_36))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 2.86/1.53  tff(c_150, plain, (![B_56, E_58, A_55, A_12, D_57, C_54]: (k2_xboole_0(k2_tarski(A_12, A_55), k2_enumset1(B_56, C_54, D_57, E_58))=k2_xboole_0(k1_tarski(A_12), k3_enumset1(A_55, B_56, C_54, D_57, E_58)))), inference(superposition, [status(thm), theory('equality')], [c_144, c_61])).
% 2.86/1.53  tff(c_465, plain, (![B_56, E_58, A_55, A_12, D_57, C_54]: (k2_xboole_0(k2_tarski(A_12, A_55), k2_enumset1(B_56, C_54, D_57, E_58))=k4_enumset1(A_12, A_55, B_56, C_54, D_57, E_58))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_150])).
% 2.86/1.53  tff(c_187, plain, (![A_59, B_60, A_12, B_13]: (k2_xboole_0(k1_enumset1(A_59, B_60, A_12), k1_tarski(B_13))=k2_enumset1(A_59, B_60, A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_183])).
% 2.86/1.53  tff(c_153, plain, (![B_56, E_58, A_55, C_5, D_57, C_54]: (k2_xboole_0(k1_tarski(A_55), k2_xboole_0(k2_enumset1(B_56, C_54, D_57, E_58), C_5))=k2_xboole_0(k3_enumset1(A_55, B_56, C_54, D_57, E_58), C_5))), inference(superposition, [status(thm), theory('equality')], [c_144, c_4])).
% 2.86/1.53  tff(c_119, plain, (![A_12, A_47, A_48, B_49]: (k2_xboole_0(k2_tarski(A_12, A_47), k2_tarski(A_48, B_49))=k2_xboole_0(k1_tarski(A_12), k1_enumset1(A_47, A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_61])).
% 2.86/1.53  tff(c_129, plain, (![A_50, A_51, A_52, B_53]: (k2_xboole_0(k1_tarski(A_50), k1_enumset1(A_51, A_52, B_53))=k2_enumset1(A_50, A_51, A_52, B_53))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_119])).
% 2.86/1.53  tff(c_392, plain, (![A_113, A_115, B_116, C_117, A_114]: (k2_xboole_0(k1_tarski(A_114), k2_xboole_0(k1_enumset1(A_113, A_115, B_116), C_117))=k2_xboole_0(k2_enumset1(A_114, A_113, A_115, B_116), C_117))), inference(superposition, [status(thm), theory('equality')], [c_129, c_4])).
% 2.86/1.53  tff(c_404, plain, (![A_113, A_115, A_12, B_116, C_117, A_114]: (k2_xboole_0(k2_tarski(A_12, A_114), k2_xboole_0(k1_enumset1(A_113, A_115, B_116), C_117))=k2_xboole_0(k1_tarski(A_12), k2_xboole_0(k2_enumset1(A_114, A_113, A_115, B_116), C_117)))), inference(superposition, [status(thm), theory('equality')], [c_392, c_61])).
% 2.86/1.53  tff(c_523, plain, (![A_145, A_143, C_144, B_147, A_148, A_146]: (k2_xboole_0(k2_tarski(A_143, A_146), k2_xboole_0(k1_enumset1(A_145, A_148, B_147), C_144))=k2_xboole_0(k3_enumset1(A_143, A_146, A_145, A_148, B_147), C_144))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_404])).
% 2.86/1.53  tff(c_553, plain, (![A_143, A_59, A_12, B_13, A_146, B_60]: (k2_xboole_0(k3_enumset1(A_143, A_146, A_59, B_60, A_12), k1_tarski(B_13))=k2_xboole_0(k2_tarski(A_143, A_146), k2_enumset1(A_59, B_60, A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_523])).
% 2.86/1.53  tff(c_558, plain, (![A_143, A_59, A_12, B_13, A_146, B_60]: (k2_xboole_0(k3_enumset1(A_143, A_146, A_59, B_60, A_12), k1_tarski(B_13))=k4_enumset1(A_143, A_146, A_59, B_60, A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_553])).
% 2.86/1.53  tff(c_18, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_tarski('#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.53  tff(c_561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_558, c_18])).
% 2.86/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.53  
% 2.86/1.53  Inference rules
% 2.86/1.53  ----------------------
% 2.86/1.53  #Ref     : 0
% 2.86/1.53  #Sup     : 141
% 2.86/1.53  #Fact    : 0
% 2.86/1.53  #Define  : 0
% 2.86/1.53  #Split   : 0
% 2.86/1.53  #Chain   : 0
% 2.86/1.53  #Close   : 0
% 2.86/1.53  
% 2.86/1.53  Ordering : KBO
% 2.86/1.53  
% 2.86/1.53  Simplification rules
% 2.86/1.53  ----------------------
% 2.86/1.53  #Subsume      : 0
% 2.86/1.53  #Demod        : 71
% 2.86/1.53  #Tautology    : 76
% 2.86/1.53  #SimpNegUnit  : 0
% 2.86/1.53  #BackRed      : 2
% 2.86/1.53  
% 2.86/1.53  #Partial instantiations: 0
% 2.86/1.53  #Strategies tried      : 1
% 2.86/1.53  
% 2.86/1.53  Timing (in seconds)
% 2.86/1.53  ----------------------
% 2.86/1.53  Preprocessing        : 0.29
% 2.86/1.53  Parsing              : 0.16
% 2.86/1.53  CNF conversion       : 0.02
% 2.86/1.53  Main loop            : 0.41
% 2.86/1.53  Inferencing          : 0.19
% 2.86/1.53  Reduction            : 0.13
% 2.86/1.53  Demodulation         : 0.11
% 2.86/1.53  BG Simplification    : 0.03
% 2.86/1.53  Subsumption          : 0.05
% 2.86/1.53  Abstraction          : 0.03
% 2.86/1.53  MUC search           : 0.00
% 2.86/1.53  Cooper               : 0.00
% 2.86/1.53  Total                : 0.73
% 2.86/1.53  Index Insertion      : 0.00
% 2.86/1.53  Index Deletion       : 0.00
% 2.86/1.53  Index Matching       : 0.00
% 2.86/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
