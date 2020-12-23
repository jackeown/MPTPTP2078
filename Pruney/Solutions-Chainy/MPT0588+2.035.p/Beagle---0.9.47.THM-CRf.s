%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:07 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 145 expanded)
%              Number of leaves         :   37 (  63 expanded)
%              Depth                    :   22
%              Number of atoms          :   81 ( 143 expanded)
%              Number of equality atoms :   55 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(k7_relat_1(A_49,B_50))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [C_53,A_51,B_52] :
      ( k7_relat_1(k7_relat_1(C_53,A_51),B_52) = k7_relat_1(C_53,k3_xboole_0(A_51,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [B_55,A_54] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_55,A_54)),k1_relat_1(B_55))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_239,plain,(
    ! [B_83,A_84] :
      ( k7_relat_1(B_83,A_84) = B_83
      | ~ r1_tarski(k1_relat_1(B_83),A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_904,plain,(
    ! [B_146,A_147] :
      ( k7_relat_1(k7_relat_1(B_146,A_147),k1_relat_1(B_146)) = k7_relat_1(B_146,A_147)
      | ~ v1_relat_1(k7_relat_1(B_146,A_147))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_30,c_239])).

tff(c_935,plain,(
    ! [C_53,A_51] :
      ( k7_relat_1(C_53,k3_xboole_0(A_51,k1_relat_1(C_53))) = k7_relat_1(C_53,A_51)
      | ~ v1_relat_1(k7_relat_1(C_53,A_51))
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_904])).

tff(c_10,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    ! [D_74,C_75,B_76,A_77] : k2_enumset1(D_74,C_75,B_76,A_77) = k2_enumset1(A_77,B_76,C_75,D_74) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [D_78,C_79,B_80] : k2_enumset1(D_78,C_79,B_80,B_80) = k1_enumset1(B_80,C_79,D_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_184,plain,(
    ! [C_79,B_80] : k1_enumset1(C_79,B_80,B_80) = k1_enumset1(B_80,C_79,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_256,plain,(
    ! [A_89,B_90,C_91,D_92] : k2_xboole_0(k1_enumset1(A_89,B_90,C_91),k1_tarski(D_92)) = k2_enumset1(A_89,B_90,C_91,D_92) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_338,plain,(
    ! [C_102,B_103,D_104] : k2_xboole_0(k1_enumset1(C_102,B_103,B_103),k1_tarski(D_104)) = k2_enumset1(B_103,C_102,C_102,D_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_256])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k1_tarski(D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_399,plain,(
    ! [C_105,B_106,D_107] : k2_enumset1(C_105,B_106,B_106,D_107) = k2_enumset1(B_106,C_105,C_105,D_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_4])).

tff(c_140,plain,(
    ! [D_74,C_75,B_76] : k2_enumset1(D_74,C_75,B_76,B_76) = k1_enumset1(B_76,C_75,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_421,plain,(
    ! [D_107,B_106] : k2_enumset1(D_107,B_106,B_106,D_107) = k1_enumset1(D_107,D_107,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_140])).

tff(c_496,plain,(
    ! [D_108,B_109] : k2_enumset1(D_108,B_109,B_109,D_108) = k2_tarski(D_108,B_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_421])).

tff(c_347,plain,(
    ! [C_102,B_103,D_104] : k2_enumset1(C_102,B_103,B_103,D_104) = k2_enumset1(B_103,C_102,C_102,D_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_4])).

tff(c_502,plain,(
    ! [B_109,D_108] : k2_enumset1(B_109,D_108,D_108,D_108) = k2_tarski(D_108,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_347])).

tff(c_8,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_516,plain,(
    ! [B_109] : k1_enumset1(B_109,B_109,B_109) = k2_tarski(B_109,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_12])).

tff(c_542,plain,(
    ! [B_109] : k1_enumset1(B_109,B_109,B_109) = k1_tarski(B_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_516])).

tff(c_18,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] : k5_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,F_37) = k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [D_41,B_39,A_38,F_43,G_44,E_42,C_40] : k6_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43,G_44) = k5_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_enumset1(A_23,A_23,B_24,C_25,D_26) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_752,plain,(
    ! [E_137,D_136,H_138,G_139,F_133,B_134,A_140,C_135] : k2_xboole_0(k3_enumset1(A_140,B_134,C_135,D_136,E_137),k1_enumset1(F_133,G_139,H_138)) = k6_enumset1(A_140,B_134,C_135,D_136,E_137,F_133,G_139,H_138) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_764,plain,(
    ! [A_23,B_24,D_26,C_25,H_138,G_139,F_133] : k6_enumset1(A_23,A_23,B_24,C_25,D_26,F_133,G_139,H_138) = k2_xboole_0(k2_enumset1(A_23,B_24,C_25,D_26),k1_enumset1(F_133,G_139,H_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_752])).

tff(c_1323,plain,(
    ! [A_163,F_158,B_159,G_161,D_160,H_162,C_157] : k2_xboole_0(k2_enumset1(A_163,B_159,C_157,D_160),k1_enumset1(F_158,G_161,H_162)) = k5_enumset1(A_163,B_159,C_157,D_160,F_158,G_161,H_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_764])).

tff(c_1380,plain,(
    ! [F_158,C_22,A_20,G_161,B_21,H_162] : k5_enumset1(A_20,A_20,B_21,C_22,F_158,G_161,H_162) = k2_xboole_0(k1_enumset1(A_20,B_21,C_22),k1_enumset1(F_158,G_161,H_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1323])).

tff(c_2116,plain,(
    ! [F_190,A_194,C_189,B_193,G_191,H_192] : k2_xboole_0(k1_enumset1(A_194,B_193,C_189),k1_enumset1(F_190,G_191,H_192)) = k4_enumset1(A_194,B_193,C_189,F_190,G_191,H_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1380])).

tff(c_2132,plain,(
    ! [A_194,B_193,C_189,B_109] : k4_enumset1(A_194,B_193,C_189,B_109,B_109,B_109) = k2_xboole_0(k1_enumset1(A_194,B_193,C_189),k1_tarski(B_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_2116])).

tff(c_2161,plain,(
    ! [A_195,B_196,C_197,B_198] : k4_enumset1(A_195,B_196,C_197,B_198,B_198,B_198) = k2_enumset1(A_195,B_196,C_197,B_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2132])).

tff(c_16,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] : k4_enumset1(A_27,A_27,B_28,C_29,D_30,E_31) = k3_enumset1(A_27,B_28,C_29,D_30,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2168,plain,(
    ! [B_196,C_197,B_198] : k3_enumset1(B_196,C_197,B_198,B_198,B_198) = k2_enumset1(B_196,B_196,C_197,B_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_2161,c_16])).

tff(c_2232,plain,(
    ! [B_204,C_205,B_206] : k3_enumset1(B_204,C_205,B_206,B_206,B_206) = k1_enumset1(B_204,C_205,B_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2168])).

tff(c_2245,plain,(
    ! [C_205,B_206] : k2_enumset1(C_205,B_206,B_206,B_206) = k1_enumset1(C_205,C_205,B_206) ),
    inference(superposition,[status(thm),theory(equality)],[c_2232,c_14])).

tff(c_2258,plain,(
    ! [C_207,B_208] : k2_tarski(C_207,B_208) = k2_tarski(B_208,C_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_10,c_2245])).

tff(c_24,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2321,plain,(
    ! [C_209,B_210] : k1_setfam_1(k2_tarski(C_209,B_210)) = k3_xboole_0(B_210,C_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_24])).

tff(c_2327,plain,(
    ! [C_209,B_210] : k3_xboole_0(C_209,B_210) = k3_xboole_0(B_210,C_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_2321,c_24])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2347,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2327,c_34])).

tff(c_2521,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_2347])).

tff(c_2524,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2521])).

tff(c_2527,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2524])).

tff(c_2531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.78  
% 4.36/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.78  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.36/1.78  
% 4.36/1.78  %Foreground sorts:
% 4.36/1.78  
% 4.36/1.78  
% 4.36/1.78  %Background operators:
% 4.36/1.78  
% 4.36/1.78  
% 4.36/1.78  %Foreground operators:
% 4.36/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.36/1.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.36/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.36/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.36/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.36/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.36/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.36/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.36/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.36/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.36/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.36/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.36/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.36/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.36/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.36/1.78  
% 4.36/1.81  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 4.36/1.81  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.36/1.81  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 4.36/1.81  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 4.36/1.81  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.36/1.81  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.36/1.81  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 4.36/1.81  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.36/1.81  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.36/1.81  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.36/1.81  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.36/1.81  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 4.36/1.81  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.36/1.81  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 4.36/1.81  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.36/1.81  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.36/1.81  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.36/1.81  tff(c_26, plain, (![A_49, B_50]: (v1_relat_1(k7_relat_1(A_49, B_50)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.36/1.81  tff(c_28, plain, (![C_53, A_51, B_52]: (k7_relat_1(k7_relat_1(C_53, A_51), B_52)=k7_relat_1(C_53, k3_xboole_0(A_51, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.36/1.81  tff(c_30, plain, (![B_55, A_54]: (r1_tarski(k1_relat_1(k7_relat_1(B_55, A_54)), k1_relat_1(B_55)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.36/1.81  tff(c_239, plain, (![B_83, A_84]: (k7_relat_1(B_83, A_84)=B_83 | ~r1_tarski(k1_relat_1(B_83), A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.36/1.81  tff(c_904, plain, (![B_146, A_147]: (k7_relat_1(k7_relat_1(B_146, A_147), k1_relat_1(B_146))=k7_relat_1(B_146, A_147) | ~v1_relat_1(k7_relat_1(B_146, A_147)) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_30, c_239])).
% 4.36/1.81  tff(c_935, plain, (![C_53, A_51]: (k7_relat_1(C_53, k3_xboole_0(A_51, k1_relat_1(C_53)))=k7_relat_1(C_53, A_51) | ~v1_relat_1(k7_relat_1(C_53, A_51)) | ~v1_relat_1(C_53) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_28, c_904])).
% 4.36/1.81  tff(c_10, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.36/1.81  tff(c_124, plain, (![D_74, C_75, B_76, A_77]: (k2_enumset1(D_74, C_75, B_76, A_77)=k2_enumset1(A_77, B_76, C_75, D_74))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.36/1.81  tff(c_12, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.36/1.81  tff(c_171, plain, (![D_78, C_79, B_80]: (k2_enumset1(D_78, C_79, B_80, B_80)=k1_enumset1(B_80, C_79, D_78))), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 4.36/1.81  tff(c_184, plain, (![C_79, B_80]: (k1_enumset1(C_79, B_80, B_80)=k1_enumset1(B_80, C_79, C_79))), inference(superposition, [status(thm), theory('equality')], [c_171, c_12])).
% 4.36/1.81  tff(c_256, plain, (![A_89, B_90, C_91, D_92]: (k2_xboole_0(k1_enumset1(A_89, B_90, C_91), k1_tarski(D_92))=k2_enumset1(A_89, B_90, C_91, D_92))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.36/1.81  tff(c_338, plain, (![C_102, B_103, D_104]: (k2_xboole_0(k1_enumset1(C_102, B_103, B_103), k1_tarski(D_104))=k2_enumset1(B_103, C_102, C_102, D_104))), inference(superposition, [status(thm), theory('equality')], [c_184, c_256])).
% 4.36/1.81  tff(c_4, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k1_enumset1(A_5, B_6, C_7), k1_tarski(D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.36/1.81  tff(c_399, plain, (![C_105, B_106, D_107]: (k2_enumset1(C_105, B_106, B_106, D_107)=k2_enumset1(B_106, C_105, C_105, D_107))), inference(superposition, [status(thm), theory('equality')], [c_338, c_4])).
% 4.36/1.81  tff(c_140, plain, (![D_74, C_75, B_76]: (k2_enumset1(D_74, C_75, B_76, B_76)=k1_enumset1(B_76, C_75, D_74))), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 4.36/1.81  tff(c_421, plain, (![D_107, B_106]: (k2_enumset1(D_107, B_106, B_106, D_107)=k1_enumset1(D_107, D_107, B_106))), inference(superposition, [status(thm), theory('equality')], [c_399, c_140])).
% 4.36/1.81  tff(c_496, plain, (![D_108, B_109]: (k2_enumset1(D_108, B_109, B_109, D_108)=k2_tarski(D_108, B_109))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_421])).
% 4.36/1.81  tff(c_347, plain, (![C_102, B_103, D_104]: (k2_enumset1(C_102, B_103, B_103, D_104)=k2_enumset1(B_103, C_102, C_102, D_104))), inference(superposition, [status(thm), theory('equality')], [c_338, c_4])).
% 4.36/1.81  tff(c_502, plain, (![B_109, D_108]: (k2_enumset1(B_109, D_108, D_108, D_108)=k2_tarski(D_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_496, c_347])).
% 4.36/1.81  tff(c_8, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.36/1.81  tff(c_516, plain, (![B_109]: (k1_enumset1(B_109, B_109, B_109)=k2_tarski(B_109, B_109))), inference(superposition, [status(thm), theory('equality')], [c_496, c_12])).
% 4.36/1.81  tff(c_542, plain, (![B_109]: (k1_enumset1(B_109, B_109, B_109)=k1_tarski(B_109))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_516])).
% 4.36/1.81  tff(c_18, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k5_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, F_37)=k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.36/1.81  tff(c_20, plain, (![D_41, B_39, A_38, F_43, G_44, E_42, C_40]: (k6_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43, G_44)=k5_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.81  tff(c_14, plain, (![A_23, B_24, C_25, D_26]: (k3_enumset1(A_23, A_23, B_24, C_25, D_26)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.36/1.81  tff(c_752, plain, (![E_137, D_136, H_138, G_139, F_133, B_134, A_140, C_135]: (k2_xboole_0(k3_enumset1(A_140, B_134, C_135, D_136, E_137), k1_enumset1(F_133, G_139, H_138))=k6_enumset1(A_140, B_134, C_135, D_136, E_137, F_133, G_139, H_138))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.36/1.81  tff(c_764, plain, (![A_23, B_24, D_26, C_25, H_138, G_139, F_133]: (k6_enumset1(A_23, A_23, B_24, C_25, D_26, F_133, G_139, H_138)=k2_xboole_0(k2_enumset1(A_23, B_24, C_25, D_26), k1_enumset1(F_133, G_139, H_138)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_752])).
% 4.36/1.81  tff(c_1323, plain, (![A_163, F_158, B_159, G_161, D_160, H_162, C_157]: (k2_xboole_0(k2_enumset1(A_163, B_159, C_157, D_160), k1_enumset1(F_158, G_161, H_162))=k5_enumset1(A_163, B_159, C_157, D_160, F_158, G_161, H_162))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_764])).
% 4.36/1.81  tff(c_1380, plain, (![F_158, C_22, A_20, G_161, B_21, H_162]: (k5_enumset1(A_20, A_20, B_21, C_22, F_158, G_161, H_162)=k2_xboole_0(k1_enumset1(A_20, B_21, C_22), k1_enumset1(F_158, G_161, H_162)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1323])).
% 4.36/1.81  tff(c_2116, plain, (![F_190, A_194, C_189, B_193, G_191, H_192]: (k2_xboole_0(k1_enumset1(A_194, B_193, C_189), k1_enumset1(F_190, G_191, H_192))=k4_enumset1(A_194, B_193, C_189, F_190, G_191, H_192))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1380])).
% 4.36/1.81  tff(c_2132, plain, (![A_194, B_193, C_189, B_109]: (k4_enumset1(A_194, B_193, C_189, B_109, B_109, B_109)=k2_xboole_0(k1_enumset1(A_194, B_193, C_189), k1_tarski(B_109)))), inference(superposition, [status(thm), theory('equality')], [c_542, c_2116])).
% 4.36/1.81  tff(c_2161, plain, (![A_195, B_196, C_197, B_198]: (k4_enumset1(A_195, B_196, C_197, B_198, B_198, B_198)=k2_enumset1(A_195, B_196, C_197, B_198))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2132])).
% 4.36/1.81  tff(c_16, plain, (![C_29, D_30, B_28, A_27, E_31]: (k4_enumset1(A_27, A_27, B_28, C_29, D_30, E_31)=k3_enumset1(A_27, B_28, C_29, D_30, E_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.36/1.81  tff(c_2168, plain, (![B_196, C_197, B_198]: (k3_enumset1(B_196, C_197, B_198, B_198, B_198)=k2_enumset1(B_196, B_196, C_197, B_198))), inference(superposition, [status(thm), theory('equality')], [c_2161, c_16])).
% 4.36/1.81  tff(c_2232, plain, (![B_204, C_205, B_206]: (k3_enumset1(B_204, C_205, B_206, B_206, B_206)=k1_enumset1(B_204, C_205, B_206))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2168])).
% 4.36/1.81  tff(c_2245, plain, (![C_205, B_206]: (k2_enumset1(C_205, B_206, B_206, B_206)=k1_enumset1(C_205, C_205, B_206))), inference(superposition, [status(thm), theory('equality')], [c_2232, c_14])).
% 4.36/1.81  tff(c_2258, plain, (![C_207, B_208]: (k2_tarski(C_207, B_208)=k2_tarski(B_208, C_207))), inference(demodulation, [status(thm), theory('equality')], [c_502, c_10, c_2245])).
% 4.36/1.81  tff(c_24, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.36/1.81  tff(c_2321, plain, (![C_209, B_210]: (k1_setfam_1(k2_tarski(C_209, B_210))=k3_xboole_0(B_210, C_209))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_24])).
% 4.36/1.81  tff(c_2327, plain, (![C_209, B_210]: (k3_xboole_0(C_209, B_210)=k3_xboole_0(B_210, C_209))), inference(superposition, [status(thm), theory('equality')], [c_2321, c_24])).
% 4.36/1.81  tff(c_34, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.36/1.81  tff(c_2347, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2327, c_34])).
% 4.36/1.81  tff(c_2521, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_935, c_2347])).
% 4.36/1.81  tff(c_2524, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2521])).
% 4.36/1.81  tff(c_2527, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_2524])).
% 4.36/1.81  tff(c_2531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2527])).
% 4.36/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.81  
% 4.36/1.81  Inference rules
% 4.36/1.81  ----------------------
% 4.36/1.81  #Ref     : 0
% 4.36/1.81  #Sup     : 634
% 4.36/1.81  #Fact    : 0
% 4.36/1.81  #Define  : 0
% 4.36/1.81  #Split   : 0
% 4.36/1.81  #Chain   : 0
% 4.36/1.81  #Close   : 0
% 4.36/1.81  
% 4.36/1.81  Ordering : KBO
% 4.36/1.81  
% 4.36/1.81  Simplification rules
% 4.36/1.81  ----------------------
% 4.36/1.81  #Subsume      : 143
% 4.36/1.81  #Demod        : 319
% 4.36/1.81  #Tautology    : 335
% 4.36/1.81  #SimpNegUnit  : 0
% 4.56/1.81  #BackRed      : 1
% 4.56/1.81  
% 4.56/1.81  #Partial instantiations: 0
% 4.56/1.81  #Strategies tried      : 1
% 4.56/1.81  
% 4.56/1.81  Timing (in seconds)
% 4.56/1.81  ----------------------
% 4.56/1.81  Preprocessing        : 0.31
% 4.56/1.81  Parsing              : 0.16
% 4.56/1.81  CNF conversion       : 0.02
% 4.56/1.81  Main loop            : 0.68
% 4.56/1.81  Inferencing          : 0.24
% 4.56/1.81  Reduction            : 0.29
% 4.56/1.81  Demodulation         : 0.26
% 4.56/1.81  BG Simplification    : 0.04
% 4.56/1.81  Subsumption          : 0.08
% 4.56/1.81  Abstraction          : 0.04
% 4.56/1.81  MUC search           : 0.00
% 4.56/1.81  Cooper               : 0.00
% 4.56/1.81  Total                : 1.03
% 4.56/1.81  Index Insertion      : 0.00
% 4.56/1.81  Index Deletion       : 0.00
% 4.56/1.81  Index Matching       : 0.00
% 4.56/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
