%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:07 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 177 expanded)
%              Number of leaves         :   37 (  75 expanded)
%              Depth                    :   20
%              Number of atoms          :   81 ( 175 expanded)
%              Number of equality atoms :   55 ( 146 expanded)
%              Maximal formula depth    :   10 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_52,B_53] :
      ( v1_relat_1(k7_relat_1(A_52,B_53))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [B_58,A_57] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_58,A_57)),k1_relat_1(B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_239,plain,(
    ! [B_86,A_87] :
      ( k7_relat_1(B_86,A_87) = B_86
      | ~ r1_tarski(k1_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_295,plain,(
    ! [B_106,A_107] :
      ( k7_relat_1(k7_relat_1(B_106,A_107),k1_relat_1(B_106)) = k7_relat_1(B_106,A_107)
      | ~ v1_relat_1(k7_relat_1(B_106,A_107))
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_30,c_239])).

tff(c_28,plain,(
    ! [C_56,A_54,B_55] :
      ( k7_relat_1(k7_relat_1(C_56,A_54),B_55) = k7_relat_1(C_56,k3_xboole_0(A_54,B_55))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_307,plain,(
    ! [B_106,A_107] :
      ( k7_relat_1(B_106,k3_xboole_0(A_107,k1_relat_1(B_106))) = k7_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(k7_relat_1(B_106,A_107))
      | ~ v1_relat_1(B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_28])).

tff(c_124,plain,(
    ! [D_77,C_78,B_79,A_80] : k2_enumset1(D_77,C_78,B_79,A_80) = k2_enumset1(A_80,B_79,C_78,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [D_77,C_78,B_79] : k2_enumset1(D_77,C_78,B_79,B_79) = k1_enumset1(B_79,C_78,D_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_10,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,E_39,F_40) = k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_338,plain,(
    ! [E_121,B_118,G_117,D_115,F_116,A_120,C_119] : k2_xboole_0(k4_enumset1(A_120,B_118,C_119,D_115,E_121,F_116),k1_tarski(G_117)) = k5_enumset1(A_120,B_118,C_119,D_115,E_121,F_116,G_117) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_347,plain,(
    ! [G_117,D_33,A_30,C_32,B_31,E_34] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,G_117) = k2_xboole_0(k3_enumset1(A_30,B_31,C_32,D_33,E_34),k1_tarski(G_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_338])).

tff(c_351,plain,(
    ! [A_124,D_127,G_126,C_122,E_125,B_123] : k2_xboole_0(k3_enumset1(A_124,B_123,C_122,D_127,E_125),k1_tarski(G_126)) = k4_enumset1(A_124,B_123,C_122,D_127,E_125,G_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_347])).

tff(c_360,plain,(
    ! [B_27,D_29,G_126,A_26,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,G_126) = k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k1_tarski(G_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_351])).

tff(c_364,plain,(
    ! [C_132,B_129,A_131,D_128,G_130] : k2_xboole_0(k2_enumset1(A_131,B_129,C_132,D_128),k1_tarski(G_130)) = k3_enumset1(A_131,B_129,C_132,D_128,G_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_360])).

tff(c_382,plain,(
    ! [A_23,B_24,C_25,G_130] : k3_enumset1(A_23,A_23,B_24,C_25,G_130) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(G_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_364])).

tff(c_385,plain,(
    ! [A_23,B_24,C_25,G_130] : k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k1_tarski(G_130)) = k2_enumset1(A_23,B_24,C_25,G_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_382])).

tff(c_8,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [D_4,C_3,B_2,A_1] : k2_enumset1(D_4,C_3,B_2,A_1) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,G_47,E_45] : k6_enumset1(A_41,A_41,B_42,C_43,D_44,E_45,F_46,G_47) = k5_enumset1(A_41,B_42,C_43,D_44,E_45,F_46,G_47) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_405,plain,(
    ! [H_139,G_137,C_144,D_142,B_138,F_143,E_141,A_140] : k2_xboole_0(k4_enumset1(A_140,B_138,C_144,D_142,E_141,F_143),k2_tarski(G_137,H_139)) = k6_enumset1(A_140,B_138,C_144,D_142,E_141,F_143,G_137,H_139) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_414,plain,(
    ! [H_139,G_137,D_33,A_30,C_32,B_31,E_34] : k6_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,G_137,H_139) = k2_xboole_0(k3_enumset1(A_30,B_31,C_32,D_33,E_34),k2_tarski(G_137,H_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_405])).

tff(c_1099,plain,(
    ! [B_180,A_181,D_183,H_179,G_177,C_178,E_182] : k2_xboole_0(k3_enumset1(A_181,B_180,C_178,D_183,E_182),k2_tarski(G_177,H_179)) = k5_enumset1(A_181,B_180,C_178,D_183,E_182,G_177,H_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_414])).

tff(c_1108,plain,(
    ! [B_27,D_29,H_179,G_177,A_26,C_28] : k5_enumset1(A_26,A_26,B_27,C_28,D_29,G_177,H_179) = k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k2_tarski(G_177,H_179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1099])).

tff(c_2420,plain,(
    ! [H_236,D_231,A_233,B_232,C_235,G_234] : k2_xboole_0(k2_enumset1(A_233,B_232,C_235,D_231),k2_tarski(G_234,H_236)) = k4_enumset1(A_233,B_232,C_235,D_231,G_234,H_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1108])).

tff(c_3287,plain,(
    ! [A_268,G_263,D_265,B_266,C_267,H_264] : k2_xboole_0(k2_enumset1(D_265,C_267,B_266,A_268),k2_tarski(G_263,H_264)) = k4_enumset1(A_268,B_266,C_267,D_265,G_263,H_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2420])).

tff(c_3397,plain,(
    ! [G_274,C_271,H_272,A_275,B_273] : k4_enumset1(C_271,B_273,A_275,A_275,G_274,H_272) = k2_xboole_0(k1_enumset1(A_275,B_273,C_271),k2_tarski(G_274,H_272)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3287])).

tff(c_3438,plain,(
    ! [C_271,B_273,A_275,A_20] : k4_enumset1(C_271,B_273,A_275,A_275,A_20,A_20) = k2_xboole_0(k1_enumset1(A_275,B_273,C_271),k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3397])).

tff(c_3446,plain,(
    ! [C_276,B_277,A_278,A_279] : k4_enumset1(C_276,B_277,A_278,A_278,A_279,A_279) = k2_enumset1(A_278,B_277,C_276,A_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_3438])).

tff(c_3480,plain,(
    ! [B_280,A_281,A_282] : k3_enumset1(B_280,A_281,A_281,A_282,A_282) = k2_enumset1(A_281,B_280,B_280,A_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_3446,c_16])).

tff(c_3582,plain,(
    ! [A_281,A_282] : k2_enumset1(A_281,A_281,A_282,A_282) = k2_enumset1(A_281,A_281,A_281,A_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_3480,c_14])).

tff(c_3698,plain,(
    ! [A_282,A_281] : k1_enumset1(A_282,A_281,A_281) = k2_tarski(A_281,A_282) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_10,c_12,c_3582])).

tff(c_171,plain,(
    ! [D_81,C_82,B_83] : k2_enumset1(D_81,C_82,B_83,B_83) = k1_enumset1(B_83,C_82,D_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_184,plain,(
    ! [C_82,B_83] : k1_enumset1(C_82,B_83,B_83) = k1_enumset1(B_83,C_82,C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_3838,plain,(
    ! [C_287,B_288] : k2_tarski(C_287,B_288) = k2_tarski(B_288,C_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3698,c_3698,c_184])).

tff(c_24,plain,(
    ! [A_50,B_51] : k1_setfam_1(k2_tarski(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4318,plain,(
    ! [C_296,B_297] : k1_setfam_1(k2_tarski(C_296,B_297)) = k3_xboole_0(B_297,C_296) ),
    inference(superposition,[status(thm),theory(equality)],[c_3838,c_24])).

tff(c_4324,plain,(
    ! [C_296,B_297] : k3_xboole_0(C_296,B_297) = k3_xboole_0(B_297,C_296) ),
    inference(superposition,[status(thm),theory(equality)],[c_4318,c_24])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4451,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4324,c_34])).

tff(c_4520,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_4451])).

tff(c_4523,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4520])).

tff(c_4526,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_4523])).

tff(c_4530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:19:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.05  
% 5.60/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.06  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.60/2.06  
% 5.60/2.06  %Foreground sorts:
% 5.60/2.06  
% 5.60/2.06  
% 5.60/2.06  %Background operators:
% 5.60/2.06  
% 5.60/2.06  
% 5.60/2.06  %Foreground operators:
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.60/2.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.60/2.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.60/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.60/2.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.60/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.60/2.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.60/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.60/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.60/2.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.60/2.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.60/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.60/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.60/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.60/2.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.60/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.60/2.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.60/2.06  
% 5.68/2.08  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 5.68/2.08  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.68/2.08  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 5.68/2.08  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 5.68/2.08  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 5.68/2.08  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 5.68/2.08  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.68/2.08  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.68/2.08  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 5.68/2.08  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 5.68/2.08  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 5.68/2.08  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 5.68/2.08  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.68/2.08  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 5.68/2.08  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 5.68/2.08  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.68/2.08  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.68/2.08  tff(c_26, plain, (![A_52, B_53]: (v1_relat_1(k7_relat_1(A_52, B_53)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.68/2.08  tff(c_30, plain, (![B_58, A_57]: (r1_tarski(k1_relat_1(k7_relat_1(B_58, A_57)), k1_relat_1(B_58)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.68/2.08  tff(c_239, plain, (![B_86, A_87]: (k7_relat_1(B_86, A_87)=B_86 | ~r1_tarski(k1_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.68/2.08  tff(c_295, plain, (![B_106, A_107]: (k7_relat_1(k7_relat_1(B_106, A_107), k1_relat_1(B_106))=k7_relat_1(B_106, A_107) | ~v1_relat_1(k7_relat_1(B_106, A_107)) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_30, c_239])).
% 5.68/2.08  tff(c_28, plain, (![C_56, A_54, B_55]: (k7_relat_1(k7_relat_1(C_56, A_54), B_55)=k7_relat_1(C_56, k3_xboole_0(A_54, B_55)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.68/2.08  tff(c_307, plain, (![B_106, A_107]: (k7_relat_1(B_106, k3_xboole_0(A_107, k1_relat_1(B_106)))=k7_relat_1(B_106, A_107) | ~v1_relat_1(B_106) | ~v1_relat_1(k7_relat_1(B_106, A_107)) | ~v1_relat_1(B_106))), inference(superposition, [status(thm), theory('equality')], [c_295, c_28])).
% 5.68/2.08  tff(c_124, plain, (![D_77, C_78, B_79, A_80]: (k2_enumset1(D_77, C_78, B_79, A_80)=k2_enumset1(A_80, B_79, C_78, D_77))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.68/2.08  tff(c_12, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.68/2.08  tff(c_140, plain, (![D_77, C_78, B_79]: (k2_enumset1(D_77, C_78, B_79, B_79)=k1_enumset1(B_79, C_78, D_77))), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 5.68/2.08  tff(c_10, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.68/2.08  tff(c_14, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.68/2.08  tff(c_16, plain, (![D_33, A_30, C_32, B_31, E_34]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34)=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.68/2.08  tff(c_18, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, E_39, F_40)=k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.68/2.08  tff(c_338, plain, (![E_121, B_118, G_117, D_115, F_116, A_120, C_119]: (k2_xboole_0(k4_enumset1(A_120, B_118, C_119, D_115, E_121, F_116), k1_tarski(G_117))=k5_enumset1(A_120, B_118, C_119, D_115, E_121, F_116, G_117))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.68/2.08  tff(c_347, plain, (![G_117, D_33, A_30, C_32, B_31, E_34]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, G_117)=k2_xboole_0(k3_enumset1(A_30, B_31, C_32, D_33, E_34), k1_tarski(G_117)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_338])).
% 5.68/2.08  tff(c_351, plain, (![A_124, D_127, G_126, C_122, E_125, B_123]: (k2_xboole_0(k3_enumset1(A_124, B_123, C_122, D_127, E_125), k1_tarski(G_126))=k4_enumset1(A_124, B_123, C_122, D_127, E_125, G_126))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_347])).
% 5.68/2.08  tff(c_360, plain, (![B_27, D_29, G_126, A_26, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, G_126)=k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k1_tarski(G_126)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_351])).
% 5.68/2.08  tff(c_364, plain, (![C_132, B_129, A_131, D_128, G_130]: (k2_xboole_0(k2_enumset1(A_131, B_129, C_132, D_128), k1_tarski(G_130))=k3_enumset1(A_131, B_129, C_132, D_128, G_130))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_360])).
% 5.68/2.08  tff(c_382, plain, (![A_23, B_24, C_25, G_130]: (k3_enumset1(A_23, A_23, B_24, C_25, G_130)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(G_130)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_364])).
% 5.68/2.08  tff(c_385, plain, (![A_23, B_24, C_25, G_130]: (k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k1_tarski(G_130))=k2_enumset1(A_23, B_24, C_25, G_130))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_382])).
% 5.68/2.08  tff(c_8, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.68/2.08  tff(c_2, plain, (![D_4, C_3, B_2, A_1]: (k2_enumset1(D_4, C_3, B_2, A_1)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.68/2.08  tff(c_20, plain, (![D_44, F_46, C_43, A_41, B_42, G_47, E_45]: (k6_enumset1(A_41, A_41, B_42, C_43, D_44, E_45, F_46, G_47)=k5_enumset1(A_41, B_42, C_43, D_44, E_45, F_46, G_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.68/2.08  tff(c_405, plain, (![H_139, G_137, C_144, D_142, B_138, F_143, E_141, A_140]: (k2_xboole_0(k4_enumset1(A_140, B_138, C_144, D_142, E_141, F_143), k2_tarski(G_137, H_139))=k6_enumset1(A_140, B_138, C_144, D_142, E_141, F_143, G_137, H_139))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.68/2.08  tff(c_414, plain, (![H_139, G_137, D_33, A_30, C_32, B_31, E_34]: (k6_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, G_137, H_139)=k2_xboole_0(k3_enumset1(A_30, B_31, C_32, D_33, E_34), k2_tarski(G_137, H_139)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_405])).
% 5.68/2.08  tff(c_1099, plain, (![B_180, A_181, D_183, H_179, G_177, C_178, E_182]: (k2_xboole_0(k3_enumset1(A_181, B_180, C_178, D_183, E_182), k2_tarski(G_177, H_179))=k5_enumset1(A_181, B_180, C_178, D_183, E_182, G_177, H_179))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_414])).
% 5.68/2.08  tff(c_1108, plain, (![B_27, D_29, H_179, G_177, A_26, C_28]: (k5_enumset1(A_26, A_26, B_27, C_28, D_29, G_177, H_179)=k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k2_tarski(G_177, H_179)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1099])).
% 5.68/2.08  tff(c_2420, plain, (![H_236, D_231, A_233, B_232, C_235, G_234]: (k2_xboole_0(k2_enumset1(A_233, B_232, C_235, D_231), k2_tarski(G_234, H_236))=k4_enumset1(A_233, B_232, C_235, D_231, G_234, H_236))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1108])).
% 5.68/2.08  tff(c_3287, plain, (![A_268, G_263, D_265, B_266, C_267, H_264]: (k2_xboole_0(k2_enumset1(D_265, C_267, B_266, A_268), k2_tarski(G_263, H_264))=k4_enumset1(A_268, B_266, C_267, D_265, G_263, H_264))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2420])).
% 5.68/2.08  tff(c_3397, plain, (![G_274, C_271, H_272, A_275, B_273]: (k4_enumset1(C_271, B_273, A_275, A_275, G_274, H_272)=k2_xboole_0(k1_enumset1(A_275, B_273, C_271), k2_tarski(G_274, H_272)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3287])).
% 5.68/2.08  tff(c_3438, plain, (![C_271, B_273, A_275, A_20]: (k4_enumset1(C_271, B_273, A_275, A_275, A_20, A_20)=k2_xboole_0(k1_enumset1(A_275, B_273, C_271), k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3397])).
% 5.68/2.08  tff(c_3446, plain, (![C_276, B_277, A_278, A_279]: (k4_enumset1(C_276, B_277, A_278, A_278, A_279, A_279)=k2_enumset1(A_278, B_277, C_276, A_279))), inference(demodulation, [status(thm), theory('equality')], [c_385, c_3438])).
% 5.68/2.08  tff(c_3480, plain, (![B_280, A_281, A_282]: (k3_enumset1(B_280, A_281, A_281, A_282, A_282)=k2_enumset1(A_281, B_280, B_280, A_282))), inference(superposition, [status(thm), theory('equality')], [c_3446, c_16])).
% 5.68/2.08  tff(c_3582, plain, (![A_281, A_282]: (k2_enumset1(A_281, A_281, A_282, A_282)=k2_enumset1(A_281, A_281, A_281, A_282))), inference(superposition, [status(thm), theory('equality')], [c_3480, c_14])).
% 5.68/2.08  tff(c_3698, plain, (![A_282, A_281]: (k1_enumset1(A_282, A_281, A_281)=k2_tarski(A_281, A_282))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_10, c_12, c_3582])).
% 5.68/2.08  tff(c_171, plain, (![D_81, C_82, B_83]: (k2_enumset1(D_81, C_82, B_83, B_83)=k1_enumset1(B_83, C_82, D_81))), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 5.68/2.08  tff(c_184, plain, (![C_82, B_83]: (k1_enumset1(C_82, B_83, B_83)=k1_enumset1(B_83, C_82, C_82))), inference(superposition, [status(thm), theory('equality')], [c_171, c_12])).
% 5.68/2.08  tff(c_3838, plain, (![C_287, B_288]: (k2_tarski(C_287, B_288)=k2_tarski(B_288, C_287))), inference(demodulation, [status(thm), theory('equality')], [c_3698, c_3698, c_184])).
% 5.68/2.08  tff(c_24, plain, (![A_50, B_51]: (k1_setfam_1(k2_tarski(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.68/2.08  tff(c_4318, plain, (![C_296, B_297]: (k1_setfam_1(k2_tarski(C_296, B_297))=k3_xboole_0(B_297, C_296))), inference(superposition, [status(thm), theory('equality')], [c_3838, c_24])).
% 5.68/2.08  tff(c_4324, plain, (![C_296, B_297]: (k3_xboole_0(C_296, B_297)=k3_xboole_0(B_297, C_296))), inference(superposition, [status(thm), theory('equality')], [c_4318, c_24])).
% 5.68/2.08  tff(c_34, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.68/2.08  tff(c_4451, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4324, c_34])).
% 5.68/2.08  tff(c_4520, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_307, c_4451])).
% 5.68/2.08  tff(c_4523, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4520])).
% 5.68/2.08  tff(c_4526, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_4523])).
% 5.68/2.08  tff(c_4530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_4526])).
% 5.68/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.08  
% 5.68/2.08  Inference rules
% 5.68/2.08  ----------------------
% 5.68/2.08  #Ref     : 0
% 5.68/2.08  #Sup     : 1161
% 5.68/2.08  #Fact    : 0
% 5.68/2.08  #Define  : 0
% 5.68/2.08  #Split   : 0
% 5.68/2.08  #Chain   : 0
% 5.68/2.08  #Close   : 0
% 5.68/2.08  
% 5.68/2.08  Ordering : KBO
% 5.68/2.08  
% 5.68/2.08  Simplification rules
% 5.68/2.08  ----------------------
% 5.68/2.08  #Subsume      : 229
% 5.68/2.08  #Demod        : 580
% 5.68/2.08  #Tautology    : 528
% 5.68/2.08  #SimpNegUnit  : 0
% 5.68/2.08  #BackRed      : 9
% 5.68/2.08  
% 5.68/2.08  #Partial instantiations: 0
% 5.68/2.08  #Strategies tried      : 1
% 5.68/2.08  
% 5.68/2.08  Timing (in seconds)
% 5.68/2.08  ----------------------
% 5.68/2.08  Preprocessing        : 0.32
% 5.68/2.08  Parsing              : 0.17
% 5.68/2.08  CNF conversion       : 0.02
% 5.68/2.08  Main loop            : 1.01
% 5.68/2.08  Inferencing          : 0.35
% 5.68/2.08  Reduction            : 0.44
% 5.68/2.08  Demodulation         : 0.37
% 5.68/2.08  BG Simplification    : 0.06
% 5.68/2.08  Subsumption          : 0.12
% 5.68/2.08  Abstraction          : 0.06
% 5.68/2.08  MUC search           : 0.00
% 5.68/2.08  Cooper               : 0.00
% 5.68/2.08  Total                : 1.37
% 5.68/2.08  Index Insertion      : 0.00
% 5.68/2.08  Index Deletion       : 0.00
% 5.68/2.08  Index Matching       : 0.00
% 5.68/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
