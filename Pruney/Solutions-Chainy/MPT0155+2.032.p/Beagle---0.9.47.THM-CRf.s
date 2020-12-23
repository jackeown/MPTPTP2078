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
% DateTime   : Thu Dec  3 09:46:13 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 371 expanded)
%              Number of leaves         :   23 ( 135 expanded)
%              Depth                    :   22
%              Number of atoms          :   56 ( 356 expanded)
%              Number of equality atoms :   55 ( 355 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k1_tarski(A_10),k2_enumset1(B_11,C_12,D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k1_tarski(A_3),k2_tarski(B_4,C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_38,B_39,C_40,D_41] : k2_xboole_0(k1_tarski(A_38),k1_enumset1(B_39,C_40,D_41)) = k2_enumset1(A_38,B_39,C_40,D_41) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_38,A_28,B_29] : k2_xboole_0(k1_tarski(A_38),k2_tarski(A_28,B_29)) = k2_enumset1(A_38,A_28,A_28,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_158,plain,(
    ! [A_51,A_52,B_53] : k2_enumset1(A_51,A_52,A_52,B_53) = k1_enumset1(A_51,A_52,B_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_67])).

tff(c_164,plain,(
    ! [A_10,A_51,A_52,B_53] : k3_enumset1(A_10,A_51,A_52,A_52,B_53) = k2_xboole_0(k1_tarski(A_10),k1_enumset1(A_51,A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_8])).

tff(c_253,plain,(
    ! [A_63,A_64,A_65,B_66] : k3_enumset1(A_63,A_64,A_65,A_65,B_66) = k2_enumset1(A_63,A_64,A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] : k2_xboole_0(k1_tarski(A_15),k3_enumset1(B_16,C_17,D_18,E_19,F_20)) = k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_259,plain,(
    ! [B_66,A_15,A_65,A_63,A_64] : k4_enumset1(A_15,A_63,A_64,A_65,A_65,B_66) = k2_xboole_0(k1_tarski(A_15),k2_enumset1(A_63,A_64,A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_10])).

tff(c_264,plain,(
    ! [B_66,A_15,A_65,A_63,A_64] : k4_enumset1(A_15,A_63,A_64,A_65,A_65,B_66) = k3_enumset1(A_15,A_63,A_64,A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_259])).

tff(c_14,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k1_tarski(A_35),k2_tarski(B_36,C_37)) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_42,A_43] : k2_xboole_0(k1_tarski(A_42),k1_tarski(A_43)) = k1_enumset1(A_42,A_43,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_84,plain,(
    ! [A_43] : k2_xboole_0(k1_tarski(A_43),k1_tarski(A_43)) = k2_tarski(A_43,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_16])).

tff(c_101,plain,(
    ! [A_44] : k2_xboole_0(k1_tarski(A_44),k1_tarski(A_44)) = k1_tarski(A_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_84])).

tff(c_55,plain,(
    ! [A_35,A_27] : k2_xboole_0(k1_tarski(A_35),k1_tarski(A_27)) = k1_enumset1(A_35,A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_117,plain,(
    ! [A_45] : k1_enumset1(A_45,A_45,A_45) = k1_tarski(A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_55])).

tff(c_171,plain,(
    ! [A_54,A_55] : k2_xboole_0(k1_tarski(A_54),k1_tarski(A_55)) = k2_enumset1(A_54,A_55,A_55,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_6])).

tff(c_97,plain,(
    ! [A_43] : k2_xboole_0(k1_tarski(A_43),k1_tarski(A_43)) = k1_tarski(A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_84])).

tff(c_213,plain,(
    ! [A_56] : k2_enumset1(A_56,A_56,A_56,A_56) = k1_tarski(A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_97])).

tff(c_266,plain,(
    ! [A_67,A_68] : k3_enumset1(A_67,A_68,A_68,A_68,A_68) = k2_xboole_0(k1_tarski(A_67),k1_tarski(A_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_8])).

tff(c_329,plain,(
    ! [A_75] : k3_enumset1(A_75,A_75,A_75,A_75,A_75) = k1_tarski(A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_97])).

tff(c_12,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] : k2_xboole_0(k3_enumset1(A_21,B_22,C_23,D_24,E_25),k1_tarski(F_26)) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,F_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_478,plain,(
    ! [A_84,F_85] : k4_enumset1(A_84,A_84,A_84,A_84,A_84,F_85) = k2_xboole_0(k1_tarski(A_84),k1_tarski(F_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_12])).

tff(c_740,plain,(
    ! [A_96,F_97] : k4_enumset1(A_96,A_96,A_96,A_96,A_96,F_97) = k1_enumset1(A_96,F_97,F_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_55])).

tff(c_991,plain,(
    ! [A_107,F_108] : k3_enumset1(A_107,A_107,A_107,A_107,F_108) = k1_enumset1(A_107,F_108,F_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_264])).

tff(c_169,plain,(
    ! [A_10,A_51,A_52,B_53] : k3_enumset1(A_10,A_51,A_52,A_52,B_53) = k2_enumset1(A_10,A_51,A_52,B_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_1068,plain,(
    ! [A_109,F_110] : k2_enumset1(A_109,A_109,A_109,F_110) = k1_enumset1(A_109,F_110,F_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_169])).

tff(c_70,plain,(
    ! [A_38,A_28,B_29] : k2_enumset1(A_38,A_28,A_28,B_29) = k1_enumset1(A_38,A_28,B_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_67])).

tff(c_1095,plain,(
    ! [A_109,F_110] : k1_enumset1(A_109,F_110,F_110) = k1_enumset1(A_109,A_109,F_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_70])).

tff(c_1142,plain,(
    ! [A_109,F_110] : k1_enumset1(A_109,F_110,F_110) = k2_tarski(A_109,F_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1095])).

tff(c_314,plain,(
    ! [D_70,B_73,E_74,F_72,C_71,A_69] : k2_xboole_0(k3_enumset1(A_69,B_73,C_71,D_70,E_74),k1_tarski(F_72)) = k4_enumset1(A_69,B_73,C_71,D_70,E_74,F_72) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1189,plain,(
    ! [B_115,A_113,A_117,F_116,A_114] : k4_enumset1(A_117,A_113,A_114,A_114,B_115,F_116) = k2_xboole_0(k2_enumset1(A_117,A_113,A_114,B_115),k1_tarski(F_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_314])).

tff(c_1785,plain,(
    ! [A_144,A_145,B_146,F_147] : k4_enumset1(A_144,A_145,A_145,A_145,B_146,F_147) = k2_xboole_0(k1_enumset1(A_144,A_145,B_146),k1_tarski(F_147)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1189])).

tff(c_1840,plain,(
    ! [A_15,A_65,B_66] : k3_enumset1(A_15,A_65,A_65,A_65,B_66) = k2_xboole_0(k1_enumset1(A_15,A_65,A_65),k1_tarski(B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_1785])).

tff(c_1864,plain,(
    ! [A_15,A_65,B_66] : k2_xboole_0(k2_tarski(A_15,A_65),k1_tarski(B_66)) = k1_enumset1(A_15,A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_70,c_169,c_1840])).

tff(c_1156,plain,(
    ! [A_35,A_27] : k2_xboole_0(k1_tarski(A_35),k1_tarski(A_27)) = k2_tarski(A_35,A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_55])).

tff(c_819,plain,(
    ! [A_98,A_99,A_100] : k3_enumset1(A_98,A_99,A_100,A_100,A_100) = k2_xboole_0(k1_tarski(A_98),k2_xboole_0(k1_tarski(A_99),k1_tarski(A_100))) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_8])).

tff(c_839,plain,(
    ! [A_98,A_99,A_100,F_26] : k4_enumset1(A_98,A_99,A_100,A_100,A_100,F_26) = k2_xboole_0(k2_xboole_0(k1_tarski(A_98),k2_xboole_0(k1_tarski(A_99),k1_tarski(A_100))),k1_tarski(F_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_12])).

tff(c_2467,plain,(
    ! [A_172,A_173,A_174,F_175] : k4_enumset1(A_172,A_173,A_174,A_174,A_174,F_175) = k2_xboole_0(k1_enumset1(A_172,A_173,A_174),k1_tarski(F_175)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1156,c_839])).

tff(c_2582,plain,(
    ! [A_28,B_29,F_175] : k4_enumset1(A_28,A_28,B_29,B_29,B_29,F_175) = k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(F_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2467])).

tff(c_2744,plain,(
    ! [A_179,B_180,F_181] : k4_enumset1(A_179,A_179,B_180,B_180,B_180,F_181) = k1_enumset1(A_179,B_180,F_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1864,c_2582])).

tff(c_2943,plain,(
    ! [A_184,A_185,B_186] : k3_enumset1(A_184,A_184,A_185,A_185,B_186) = k1_enumset1(A_184,A_185,B_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_2744])).

tff(c_2976,plain,(
    ! [A_184,A_185,B_186] : k2_enumset1(A_184,A_184,A_185,B_186) = k1_enumset1(A_184,A_185,B_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_169])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n018.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 11:39:56 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.51  
% 3.48/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.51  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.48/1.51  
% 3.48/1.51  %Foreground sorts:
% 3.48/1.51  
% 3.48/1.51  
% 3.48/1.51  %Background operators:
% 3.48/1.51  
% 3.48/1.51  
% 3.48/1.51  %Foreground operators:
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.48/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.48/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.51  
% 3.76/1.52  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 3.76/1.52  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.76/1.52  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.76/1.52  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.76/1.52  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 3.76/1.52  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.76/1.52  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 3.76/1.52  tff(f_44, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.76/1.52  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k2_xboole_0(k1_tarski(A_10), k2_enumset1(B_11, C_12, D_13, E_14))=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.76/1.52  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.52  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(B_4, C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.76/1.52  tff(c_16, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.76/1.52  tff(c_58, plain, (![A_38, B_39, C_40, D_41]: (k2_xboole_0(k1_tarski(A_38), k1_enumset1(B_39, C_40, D_41))=k2_enumset1(A_38, B_39, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.52  tff(c_67, plain, (![A_38, A_28, B_29]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(A_28, B_29))=k2_enumset1(A_38, A_28, A_28, B_29))), inference(superposition, [status(thm), theory('equality')], [c_16, c_58])).
% 3.76/1.52  tff(c_158, plain, (![A_51, A_52, B_53]: (k2_enumset1(A_51, A_52, A_52, B_53)=k1_enumset1(A_51, A_52, B_53))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_67])).
% 3.76/1.52  tff(c_164, plain, (![A_10, A_51, A_52, B_53]: (k3_enumset1(A_10, A_51, A_52, A_52, B_53)=k2_xboole_0(k1_tarski(A_10), k1_enumset1(A_51, A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_8])).
% 3.76/1.52  tff(c_253, plain, (![A_63, A_64, A_65, B_66]: (k3_enumset1(A_63, A_64, A_65, A_65, B_66)=k2_enumset1(A_63, A_64, A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 3.76/1.52  tff(c_10, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k2_xboole_0(k1_tarski(A_15), k3_enumset1(B_16, C_17, D_18, E_19, F_20))=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.76/1.52  tff(c_259, plain, (![B_66, A_15, A_65, A_63, A_64]: (k4_enumset1(A_15, A_63, A_64, A_65, A_65, B_66)=k2_xboole_0(k1_tarski(A_15), k2_enumset1(A_63, A_64, A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_253, c_10])).
% 3.76/1.52  tff(c_264, plain, (![B_66, A_15, A_65, A_63, A_64]: (k4_enumset1(A_15, A_63, A_64, A_65, A_65, B_66)=k3_enumset1(A_15, A_63, A_64, A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_259])).
% 3.76/1.52  tff(c_14, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.76/1.52  tff(c_46, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k1_tarski(A_35), k2_tarski(B_36, C_37))=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.76/1.52  tff(c_71, plain, (![A_42, A_43]: (k2_xboole_0(k1_tarski(A_42), k1_tarski(A_43))=k1_enumset1(A_42, A_43, A_43))), inference(superposition, [status(thm), theory('equality')], [c_14, c_46])).
% 3.76/1.52  tff(c_84, plain, (![A_43]: (k2_xboole_0(k1_tarski(A_43), k1_tarski(A_43))=k2_tarski(A_43, A_43))), inference(superposition, [status(thm), theory('equality')], [c_71, c_16])).
% 3.76/1.52  tff(c_101, plain, (![A_44]: (k2_xboole_0(k1_tarski(A_44), k1_tarski(A_44))=k1_tarski(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_84])).
% 3.76/1.52  tff(c_55, plain, (![A_35, A_27]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(A_27))=k1_enumset1(A_35, A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_14, c_46])).
% 3.76/1.52  tff(c_117, plain, (![A_45]: (k1_enumset1(A_45, A_45, A_45)=k1_tarski(A_45))), inference(superposition, [status(thm), theory('equality')], [c_101, c_55])).
% 3.76/1.52  tff(c_171, plain, (![A_54, A_55]: (k2_xboole_0(k1_tarski(A_54), k1_tarski(A_55))=k2_enumset1(A_54, A_55, A_55, A_55))), inference(superposition, [status(thm), theory('equality')], [c_117, c_6])).
% 3.76/1.52  tff(c_97, plain, (![A_43]: (k2_xboole_0(k1_tarski(A_43), k1_tarski(A_43))=k1_tarski(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_84])).
% 3.76/1.52  tff(c_213, plain, (![A_56]: (k2_enumset1(A_56, A_56, A_56, A_56)=k1_tarski(A_56))), inference(superposition, [status(thm), theory('equality')], [c_171, c_97])).
% 3.76/1.52  tff(c_266, plain, (![A_67, A_68]: (k3_enumset1(A_67, A_68, A_68, A_68, A_68)=k2_xboole_0(k1_tarski(A_67), k1_tarski(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_8])).
% 3.76/1.52  tff(c_329, plain, (![A_75]: (k3_enumset1(A_75, A_75, A_75, A_75, A_75)=k1_tarski(A_75))), inference(superposition, [status(thm), theory('equality')], [c_266, c_97])).
% 3.76/1.52  tff(c_12, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k2_xboole_0(k3_enumset1(A_21, B_22, C_23, D_24, E_25), k1_tarski(F_26))=k4_enumset1(A_21, B_22, C_23, D_24, E_25, F_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.76/1.52  tff(c_478, plain, (![A_84, F_85]: (k4_enumset1(A_84, A_84, A_84, A_84, A_84, F_85)=k2_xboole_0(k1_tarski(A_84), k1_tarski(F_85)))), inference(superposition, [status(thm), theory('equality')], [c_329, c_12])).
% 3.76/1.52  tff(c_740, plain, (![A_96, F_97]: (k4_enumset1(A_96, A_96, A_96, A_96, A_96, F_97)=k1_enumset1(A_96, F_97, F_97))), inference(superposition, [status(thm), theory('equality')], [c_478, c_55])).
% 3.76/1.52  tff(c_991, plain, (![A_107, F_108]: (k3_enumset1(A_107, A_107, A_107, A_107, F_108)=k1_enumset1(A_107, F_108, F_108))), inference(superposition, [status(thm), theory('equality')], [c_740, c_264])).
% 3.76/1.52  tff(c_169, plain, (![A_10, A_51, A_52, B_53]: (k3_enumset1(A_10, A_51, A_52, A_52, B_53)=k2_enumset1(A_10, A_51, A_52, B_53))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 3.76/1.52  tff(c_1068, plain, (![A_109, F_110]: (k2_enumset1(A_109, A_109, A_109, F_110)=k1_enumset1(A_109, F_110, F_110))), inference(superposition, [status(thm), theory('equality')], [c_991, c_169])).
% 3.76/1.52  tff(c_70, plain, (![A_38, A_28, B_29]: (k2_enumset1(A_38, A_28, A_28, B_29)=k1_enumset1(A_38, A_28, B_29))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_67])).
% 3.76/1.52  tff(c_1095, plain, (![A_109, F_110]: (k1_enumset1(A_109, F_110, F_110)=k1_enumset1(A_109, A_109, F_110))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_70])).
% 3.76/1.52  tff(c_1142, plain, (![A_109, F_110]: (k1_enumset1(A_109, F_110, F_110)=k2_tarski(A_109, F_110))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1095])).
% 3.76/1.52  tff(c_314, plain, (![D_70, B_73, E_74, F_72, C_71, A_69]: (k2_xboole_0(k3_enumset1(A_69, B_73, C_71, D_70, E_74), k1_tarski(F_72))=k4_enumset1(A_69, B_73, C_71, D_70, E_74, F_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.76/1.52  tff(c_1189, plain, (![B_115, A_113, A_117, F_116, A_114]: (k4_enumset1(A_117, A_113, A_114, A_114, B_115, F_116)=k2_xboole_0(k2_enumset1(A_117, A_113, A_114, B_115), k1_tarski(F_116)))), inference(superposition, [status(thm), theory('equality')], [c_169, c_314])).
% 3.76/1.52  tff(c_1785, plain, (![A_144, A_145, B_146, F_147]: (k4_enumset1(A_144, A_145, A_145, A_145, B_146, F_147)=k2_xboole_0(k1_enumset1(A_144, A_145, B_146), k1_tarski(F_147)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1189])).
% 3.76/1.52  tff(c_1840, plain, (![A_15, A_65, B_66]: (k3_enumset1(A_15, A_65, A_65, A_65, B_66)=k2_xboole_0(k1_enumset1(A_15, A_65, A_65), k1_tarski(B_66)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_1785])).
% 3.76/1.52  tff(c_1864, plain, (![A_15, A_65, B_66]: (k2_xboole_0(k2_tarski(A_15, A_65), k1_tarski(B_66))=k1_enumset1(A_15, A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_70, c_169, c_1840])).
% 3.76/1.52  tff(c_1156, plain, (![A_35, A_27]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(A_27))=k2_tarski(A_35, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_55])).
% 3.76/1.52  tff(c_819, plain, (![A_98, A_99, A_100]: (k3_enumset1(A_98, A_99, A_100, A_100, A_100)=k2_xboole_0(k1_tarski(A_98), k2_xboole_0(k1_tarski(A_99), k1_tarski(A_100))))), inference(superposition, [status(thm), theory('equality')], [c_171, c_8])).
% 3.76/1.52  tff(c_839, plain, (![A_98, A_99, A_100, F_26]: (k4_enumset1(A_98, A_99, A_100, A_100, A_100, F_26)=k2_xboole_0(k2_xboole_0(k1_tarski(A_98), k2_xboole_0(k1_tarski(A_99), k1_tarski(A_100))), k1_tarski(F_26)))), inference(superposition, [status(thm), theory('equality')], [c_819, c_12])).
% 3.76/1.52  tff(c_2467, plain, (![A_172, A_173, A_174, F_175]: (k4_enumset1(A_172, A_173, A_174, A_174, A_174, F_175)=k2_xboole_0(k1_enumset1(A_172, A_173, A_174), k1_tarski(F_175)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1156, c_839])).
% 3.76/1.52  tff(c_2582, plain, (![A_28, B_29, F_175]: (k4_enumset1(A_28, A_28, B_29, B_29, B_29, F_175)=k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(F_175)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2467])).
% 3.76/1.52  tff(c_2744, plain, (![A_179, B_180, F_181]: (k4_enumset1(A_179, A_179, B_180, B_180, B_180, F_181)=k1_enumset1(A_179, B_180, F_181))), inference(demodulation, [status(thm), theory('equality')], [c_1864, c_2582])).
% 3.76/1.52  tff(c_2943, plain, (![A_184, A_185, B_186]: (k3_enumset1(A_184, A_184, A_185, A_185, B_186)=k1_enumset1(A_184, A_185, B_186))), inference(superposition, [status(thm), theory('equality')], [c_264, c_2744])).
% 3.76/1.52  tff(c_2976, plain, (![A_184, A_185, B_186]: (k2_enumset1(A_184, A_184, A_185, B_186)=k1_enumset1(A_184, A_185, B_186))), inference(superposition, [status(thm), theory('equality')], [c_2943, c_169])).
% 3.76/1.52  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.76/1.52  tff(c_3027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2976, c_18])).
% 3.76/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.52  
% 3.76/1.52  Inference rules
% 3.76/1.52  ----------------------
% 3.76/1.52  #Ref     : 0
% 3.76/1.52  #Sup     : 675
% 3.76/1.52  #Fact    : 0
% 3.76/1.52  #Define  : 0
% 3.76/1.52  #Split   : 0
% 3.76/1.52  #Chain   : 0
% 3.76/1.52  #Close   : 0
% 3.76/1.52  
% 3.76/1.52  Ordering : KBO
% 3.76/1.52  
% 3.76/1.52  Simplification rules
% 3.76/1.52  ----------------------
% 3.76/1.52  #Subsume      : 31
% 3.76/1.52  #Demod        : 928
% 3.76/1.52  #Tautology    : 572
% 3.76/1.52  #SimpNegUnit  : 0
% 3.76/1.52  #BackRed      : 15
% 3.76/1.52  
% 3.76/1.52  #Partial instantiations: 0
% 3.76/1.52  #Strategies tried      : 1
% 3.76/1.52  
% 3.76/1.52  Timing (in seconds)
% 3.76/1.52  ----------------------
% 3.76/1.53  Preprocessing        : 0.28
% 3.76/1.53  Parsing              : 0.15
% 3.76/1.53  CNF conversion       : 0.02
% 3.76/1.53  Main loop            : 0.59
% 3.76/1.53  Inferencing          : 0.23
% 3.76/1.53  Reduction            : 0.26
% 3.76/1.53  Demodulation         : 0.21
% 3.76/1.53  BG Simplification    : 0.03
% 3.76/1.53  Subsumption          : 0.05
% 3.76/1.53  Abstraction          : 0.04
% 3.76/1.53  MUC search           : 0.00
% 3.76/1.53  Cooper               : 0.00
% 3.76/1.53  Total                : 0.91
% 3.76/1.53  Index Insertion      : 0.00
% 3.76/1.53  Index Deletion       : 0.00
% 3.76/1.53  Index Matching       : 0.00
% 3.76/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
