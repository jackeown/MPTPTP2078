%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:07 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 232 expanded)
%              Number of leaves         :   37 (  92 expanded)
%              Depth                    :   24
%              Number of atoms          :   85 ( 230 expanded)
%              Number of equality atoms :   59 ( 201 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_51,B_52] :
      ( v1_relat_1(k7_relat_1(A_51,B_52))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [B_57,A_56] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_57,A_56)),k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_239,plain,(
    ! [B_85,A_86] :
      ( k7_relat_1(B_85,A_86) = B_85
      | ~ r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_295,plain,(
    ! [B_105,A_106] :
      ( k7_relat_1(k7_relat_1(B_105,A_106),k1_relat_1(B_105)) = k7_relat_1(B_105,A_106)
      | ~ v1_relat_1(k7_relat_1(B_105,A_106))
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_30,c_239])).

tff(c_28,plain,(
    ! [C_55,A_53,B_54] :
      ( k7_relat_1(k7_relat_1(C_55,A_53),B_54) = k7_relat_1(C_55,k3_xboole_0(A_53,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_307,plain,(
    ! [B_105,A_106] :
      ( k7_relat_1(B_105,k3_xboole_0(A_106,k1_relat_1(B_105))) = k7_relat_1(B_105,A_106)
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(k7_relat_1(B_105,A_106))
      | ~ v1_relat_1(B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_28])).

tff(c_124,plain,(
    ! [D_76,C_77,B_78,A_79] : k2_enumset1(D_76,C_77,B_78,A_79) = k2_enumset1(A_79,B_78,C_77,D_76) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_22,B_23,C_24] : k2_enumset1(A_22,A_22,B_23,C_24) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [D_80,C_81,B_82] : k2_enumset1(D_80,C_81,B_82,B_82) = k1_enumset1(B_82,C_81,D_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_184,plain,(
    ! [C_81,B_82] : k1_enumset1(C_81,B_82,B_82) = k1_enumset1(B_82,C_81,C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_14,plain,(
    ! [A_25,B_26,C_27,D_28] : k3_enumset1(A_25,A_25,B_26,C_27,D_28) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [E_33,A_29,D_32,C_31,B_30] : k4_enumset1(A_29,A_29,B_30,C_31,D_32,E_33) = k3_enumset1(A_29,B_30,C_31,D_32,E_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_329,plain,(
    ! [C_110,F_108,A_111,D_107,B_109,E_112] : k2_xboole_0(k3_enumset1(A_111,B_109,C_110,D_107,E_112),k1_tarski(F_108)) = k4_enumset1(A_111,B_109,C_110,D_107,E_112,F_108) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_338,plain,(
    ! [F_108,A_25,C_27,D_28,B_26] : k4_enumset1(A_25,A_25,B_26,C_27,D_28,F_108) = k2_xboole_0(k2_enumset1(A_25,B_26,C_27,D_28),k1_tarski(F_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_329])).

tff(c_351,plain,(
    ! [F_124,A_121,C_122,D_120,B_123] : k2_xboole_0(k2_enumset1(A_121,B_123,C_122,D_120),k1_tarski(F_124)) = k3_enumset1(A_121,B_123,C_122,D_120,F_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_338])).

tff(c_369,plain,(
    ! [A_22,B_23,C_24,F_124] : k3_enumset1(A_22,A_22,B_23,C_24,F_124) = k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k1_tarski(F_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_351])).

tff(c_373,plain,(
    ! [A_125,B_126,C_127,F_128] : k2_xboole_0(k1_enumset1(A_125,B_126,C_127),k1_tarski(F_128)) = k2_enumset1(A_125,B_126,C_127,F_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_369])).

tff(c_456,plain,(
    ! [C_143,B_144,F_145] : k2_xboole_0(k1_enumset1(C_143,B_144,B_144),k1_tarski(F_145)) = k2_enumset1(B_144,C_143,C_143,F_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_373])).

tff(c_372,plain,(
    ! [A_22,B_23,C_24,F_124] : k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k1_tarski(F_124)) = k2_enumset1(A_22,B_23,C_24,F_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_369])).

tff(c_465,plain,(
    ! [C_143,B_144,F_145] : k2_enumset1(C_143,B_144,B_144,F_145) = k2_enumset1(B_144,C_143,C_143,F_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_372])).

tff(c_10,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_521,plain,(
    ! [C_146,B_147,F_148] : k2_enumset1(C_146,B_147,B_147,F_148) = k2_enumset1(B_147,C_146,C_146,F_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_372])).

tff(c_140,plain,(
    ! [D_76,C_77,B_78] : k2_enumset1(D_76,C_77,B_78,B_78) = k1_enumset1(B_78,C_77,D_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_549,plain,(
    ! [F_148,B_147] : k2_enumset1(F_148,B_147,B_147,F_148) = k1_enumset1(F_148,F_148,B_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_140])).

tff(c_642,plain,(
    ! [F_152,B_153] : k2_enumset1(F_152,B_153,B_153,F_152) = k2_tarski(F_152,B_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_549])).

tff(c_672,plain,(
    ! [C_143,F_145] : k2_enumset1(C_143,F_145,F_145,F_145) = k2_tarski(F_145,C_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_642])).

tff(c_8,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_661,plain,(
    ! [F_152] : k1_enumset1(F_152,F_152,F_152) = k2_tarski(F_152,F_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_140])).

tff(c_691,plain,(
    ! [F_152] : k1_enumset1(F_152,F_152,F_152) = k1_tarski(F_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_661])).

tff(c_18,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] : k5_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,F_39) = k4_enumset1(A_34,B_35,C_36,D_37,E_38,F_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [E_44,C_42,G_46,F_45,A_40,D_43,B_41] : k6_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,F_45,G_46) = k5_enumset1(A_40,B_41,C_42,D_43,E_44,F_45,G_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_405,plain,(
    ! [H_139,E_138,D_137,C_133,B_136,F_132,G_134,A_135] : k2_xboole_0(k3_enumset1(A_135,B_136,C_133,D_137,E_138),k1_enumset1(F_132,G_134,H_139)) = k6_enumset1(A_135,B_136,C_133,D_137,E_138,F_132,G_134,H_139) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_414,plain,(
    ! [H_139,A_25,F_132,G_134,C_27,D_28,B_26] : k6_enumset1(A_25,A_25,B_26,C_27,D_28,F_132,G_134,H_139) = k2_xboole_0(k2_enumset1(A_25,B_26,C_27,D_28),k1_enumset1(F_132,G_134,H_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_405])).

tff(c_885,plain,(
    ! [C_162,A_159,H_161,B_163,D_158,G_164,F_160] : k2_xboole_0(k2_enumset1(A_159,B_163,C_162,D_158),k1_enumset1(F_160,G_164,H_161)) = k5_enumset1(A_159,B_163,C_162,D_158,F_160,G_164,H_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_414])).

tff(c_930,plain,(
    ! [H_161,G_164,A_22,B_23,F_160,C_24] : k5_enumset1(A_22,A_22,B_23,C_24,F_160,G_164,H_161) = k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k1_enumset1(F_160,G_164,H_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_885])).

tff(c_2715,plain,(
    ! [A_235,H_238,C_236,B_239,F_240,G_237] : k2_xboole_0(k1_enumset1(A_235,B_239,C_236),k1_enumset1(F_240,G_237,H_238)) = k4_enumset1(A_235,B_239,C_236,F_240,G_237,H_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_930])).

tff(c_2731,plain,(
    ! [A_235,B_239,C_236,F_152] : k4_enumset1(A_235,B_239,C_236,F_152,F_152,F_152) = k2_xboole_0(k1_enumset1(A_235,B_239,C_236),k1_tarski(F_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_2715])).

tff(c_3329,plain,(
    ! [A_267,B_268,C_269,F_270] : k4_enumset1(A_267,B_268,C_269,F_270,F_270,F_270) = k2_enumset1(A_267,B_268,C_269,F_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_2731])).

tff(c_3342,plain,(
    ! [B_268,C_269,F_270] : k3_enumset1(B_268,C_269,F_270,F_270,F_270) = k2_enumset1(B_268,B_268,C_269,F_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_3329,c_16])).

tff(c_3362,plain,(
    ! [B_271,C_272,F_273] : k3_enumset1(B_271,C_272,F_273,F_273,F_273) = k1_enumset1(B_271,C_272,F_273) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3342])).

tff(c_3418,plain,(
    ! [C_272,F_273] : k2_enumset1(C_272,F_273,F_273,F_273) = k1_enumset1(C_272,C_272,F_273) ),
    inference(superposition,[status(thm),theory(equality)],[c_3362,c_14])).

tff(c_3477,plain,(
    ! [F_274,C_275] : k2_tarski(F_274,C_275) = k2_tarski(C_275,F_274) ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_10,c_3418])).

tff(c_24,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3880,plain,(
    ! [F_282,C_283] : k1_setfam_1(k2_tarski(F_282,C_283)) = k3_xboole_0(C_283,F_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_3477,c_24])).

tff(c_3886,plain,(
    ! [F_282,C_283] : k3_xboole_0(F_282,C_283) = k3_xboole_0(C_283,F_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_3880,c_24])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3906,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_34])).

tff(c_4164,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_3906])).

tff(c_4167,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4164])).

tff(c_4170,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_4167])).

tff(c_4174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.20  
% 5.94/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.20  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.94/2.20  
% 5.94/2.20  %Foreground sorts:
% 5.94/2.20  
% 5.94/2.20  
% 5.94/2.20  %Background operators:
% 5.94/2.20  
% 5.94/2.20  
% 5.94/2.20  %Foreground operators:
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.94/2.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.94/2.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.94/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.94/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.94/2.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.94/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.94/2.20  tff('#skF_1', type, '#skF_1': $i).
% 5.94/2.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.94/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.94/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.94/2.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.94/2.20  
% 6.07/2.22  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 6.07/2.22  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.07/2.22  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 6.07/2.22  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 6.07/2.22  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 6.07/2.22  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 6.07/2.22  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.07/2.22  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.07/2.22  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 6.07/2.22  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 6.07/2.22  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.07/2.22  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.07/2.22  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 6.07/2.22  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 6.07/2.22  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 6.07/2.22  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.07/2.22  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.07/2.22  tff(c_26, plain, (![A_51, B_52]: (v1_relat_1(k7_relat_1(A_51, B_52)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.07/2.22  tff(c_30, plain, (![B_57, A_56]: (r1_tarski(k1_relat_1(k7_relat_1(B_57, A_56)), k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.07/2.22  tff(c_239, plain, (![B_85, A_86]: (k7_relat_1(B_85, A_86)=B_85 | ~r1_tarski(k1_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.07/2.22  tff(c_295, plain, (![B_105, A_106]: (k7_relat_1(k7_relat_1(B_105, A_106), k1_relat_1(B_105))=k7_relat_1(B_105, A_106) | ~v1_relat_1(k7_relat_1(B_105, A_106)) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_30, c_239])).
% 6.07/2.22  tff(c_28, plain, (![C_55, A_53, B_54]: (k7_relat_1(k7_relat_1(C_55, A_53), B_54)=k7_relat_1(C_55, k3_xboole_0(A_53, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.07/2.22  tff(c_307, plain, (![B_105, A_106]: (k7_relat_1(B_105, k3_xboole_0(A_106, k1_relat_1(B_105)))=k7_relat_1(B_105, A_106) | ~v1_relat_1(B_105) | ~v1_relat_1(k7_relat_1(B_105, A_106)) | ~v1_relat_1(B_105))), inference(superposition, [status(thm), theory('equality')], [c_295, c_28])).
% 6.07/2.22  tff(c_124, plain, (![D_76, C_77, B_78, A_79]: (k2_enumset1(D_76, C_77, B_78, A_79)=k2_enumset1(A_79, B_78, C_77, D_76))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.07/2.22  tff(c_12, plain, (![A_22, B_23, C_24]: (k2_enumset1(A_22, A_22, B_23, C_24)=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.07/2.22  tff(c_171, plain, (![D_80, C_81, B_82]: (k2_enumset1(D_80, C_81, B_82, B_82)=k1_enumset1(B_82, C_81, D_80))), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 6.07/2.22  tff(c_184, plain, (![C_81, B_82]: (k1_enumset1(C_81, B_82, B_82)=k1_enumset1(B_82, C_81, C_81))), inference(superposition, [status(thm), theory('equality')], [c_171, c_12])).
% 6.07/2.22  tff(c_14, plain, (![A_25, B_26, C_27, D_28]: (k3_enumset1(A_25, A_25, B_26, C_27, D_28)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.07/2.22  tff(c_16, plain, (![E_33, A_29, D_32, C_31, B_30]: (k4_enumset1(A_29, A_29, B_30, C_31, D_32, E_33)=k3_enumset1(A_29, B_30, C_31, D_32, E_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.07/2.22  tff(c_329, plain, (![C_110, F_108, A_111, D_107, B_109, E_112]: (k2_xboole_0(k3_enumset1(A_111, B_109, C_110, D_107, E_112), k1_tarski(F_108))=k4_enumset1(A_111, B_109, C_110, D_107, E_112, F_108))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.07/2.22  tff(c_338, plain, (![F_108, A_25, C_27, D_28, B_26]: (k4_enumset1(A_25, A_25, B_26, C_27, D_28, F_108)=k2_xboole_0(k2_enumset1(A_25, B_26, C_27, D_28), k1_tarski(F_108)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_329])).
% 6.07/2.22  tff(c_351, plain, (![F_124, A_121, C_122, D_120, B_123]: (k2_xboole_0(k2_enumset1(A_121, B_123, C_122, D_120), k1_tarski(F_124))=k3_enumset1(A_121, B_123, C_122, D_120, F_124))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_338])).
% 6.07/2.22  tff(c_369, plain, (![A_22, B_23, C_24, F_124]: (k3_enumset1(A_22, A_22, B_23, C_24, F_124)=k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k1_tarski(F_124)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_351])).
% 6.07/2.22  tff(c_373, plain, (![A_125, B_126, C_127, F_128]: (k2_xboole_0(k1_enumset1(A_125, B_126, C_127), k1_tarski(F_128))=k2_enumset1(A_125, B_126, C_127, F_128))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_369])).
% 6.07/2.22  tff(c_456, plain, (![C_143, B_144, F_145]: (k2_xboole_0(k1_enumset1(C_143, B_144, B_144), k1_tarski(F_145))=k2_enumset1(B_144, C_143, C_143, F_145))), inference(superposition, [status(thm), theory('equality')], [c_184, c_373])).
% 6.07/2.22  tff(c_372, plain, (![A_22, B_23, C_24, F_124]: (k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k1_tarski(F_124))=k2_enumset1(A_22, B_23, C_24, F_124))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_369])).
% 6.07/2.22  tff(c_465, plain, (![C_143, B_144, F_145]: (k2_enumset1(C_143, B_144, B_144, F_145)=k2_enumset1(B_144, C_143, C_143, F_145))), inference(superposition, [status(thm), theory('equality')], [c_456, c_372])).
% 6.07/2.22  tff(c_10, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.07/2.22  tff(c_521, plain, (![C_146, B_147, F_148]: (k2_enumset1(C_146, B_147, B_147, F_148)=k2_enumset1(B_147, C_146, C_146, F_148))), inference(superposition, [status(thm), theory('equality')], [c_456, c_372])).
% 6.07/2.22  tff(c_140, plain, (![D_76, C_77, B_78]: (k2_enumset1(D_76, C_77, B_78, B_78)=k1_enumset1(B_78, C_77, D_76))), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 6.07/2.22  tff(c_549, plain, (![F_148, B_147]: (k2_enumset1(F_148, B_147, B_147, F_148)=k1_enumset1(F_148, F_148, B_147))), inference(superposition, [status(thm), theory('equality')], [c_521, c_140])).
% 6.07/2.22  tff(c_642, plain, (![F_152, B_153]: (k2_enumset1(F_152, B_153, B_153, F_152)=k2_tarski(F_152, B_153))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_549])).
% 6.07/2.22  tff(c_672, plain, (![C_143, F_145]: (k2_enumset1(C_143, F_145, F_145, F_145)=k2_tarski(F_145, C_143))), inference(superposition, [status(thm), theory('equality')], [c_465, c_642])).
% 6.07/2.22  tff(c_8, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.07/2.22  tff(c_661, plain, (![F_152]: (k1_enumset1(F_152, F_152, F_152)=k2_tarski(F_152, F_152))), inference(superposition, [status(thm), theory('equality')], [c_642, c_140])).
% 6.07/2.22  tff(c_691, plain, (![F_152]: (k1_enumset1(F_152, F_152, F_152)=k1_tarski(F_152))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_661])).
% 6.07/2.22  tff(c_18, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (k5_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, F_39)=k4_enumset1(A_34, B_35, C_36, D_37, E_38, F_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.07/2.22  tff(c_20, plain, (![E_44, C_42, G_46, F_45, A_40, D_43, B_41]: (k6_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, F_45, G_46)=k5_enumset1(A_40, B_41, C_42, D_43, E_44, F_45, G_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.07/2.22  tff(c_405, plain, (![H_139, E_138, D_137, C_133, B_136, F_132, G_134, A_135]: (k2_xboole_0(k3_enumset1(A_135, B_136, C_133, D_137, E_138), k1_enumset1(F_132, G_134, H_139))=k6_enumset1(A_135, B_136, C_133, D_137, E_138, F_132, G_134, H_139))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.07/2.22  tff(c_414, plain, (![H_139, A_25, F_132, G_134, C_27, D_28, B_26]: (k6_enumset1(A_25, A_25, B_26, C_27, D_28, F_132, G_134, H_139)=k2_xboole_0(k2_enumset1(A_25, B_26, C_27, D_28), k1_enumset1(F_132, G_134, H_139)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_405])).
% 6.07/2.22  tff(c_885, plain, (![C_162, A_159, H_161, B_163, D_158, G_164, F_160]: (k2_xboole_0(k2_enumset1(A_159, B_163, C_162, D_158), k1_enumset1(F_160, G_164, H_161))=k5_enumset1(A_159, B_163, C_162, D_158, F_160, G_164, H_161))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_414])).
% 6.07/2.22  tff(c_930, plain, (![H_161, G_164, A_22, B_23, F_160, C_24]: (k5_enumset1(A_22, A_22, B_23, C_24, F_160, G_164, H_161)=k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k1_enumset1(F_160, G_164, H_161)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_885])).
% 6.07/2.22  tff(c_2715, plain, (![A_235, H_238, C_236, B_239, F_240, G_237]: (k2_xboole_0(k1_enumset1(A_235, B_239, C_236), k1_enumset1(F_240, G_237, H_238))=k4_enumset1(A_235, B_239, C_236, F_240, G_237, H_238))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_930])).
% 6.07/2.22  tff(c_2731, plain, (![A_235, B_239, C_236, F_152]: (k4_enumset1(A_235, B_239, C_236, F_152, F_152, F_152)=k2_xboole_0(k1_enumset1(A_235, B_239, C_236), k1_tarski(F_152)))), inference(superposition, [status(thm), theory('equality')], [c_691, c_2715])).
% 6.07/2.22  tff(c_3329, plain, (![A_267, B_268, C_269, F_270]: (k4_enumset1(A_267, B_268, C_269, F_270, F_270, F_270)=k2_enumset1(A_267, B_268, C_269, F_270))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_2731])).
% 6.07/2.22  tff(c_3342, plain, (![B_268, C_269, F_270]: (k3_enumset1(B_268, C_269, F_270, F_270, F_270)=k2_enumset1(B_268, B_268, C_269, F_270))), inference(superposition, [status(thm), theory('equality')], [c_3329, c_16])).
% 6.07/2.22  tff(c_3362, plain, (![B_271, C_272, F_273]: (k3_enumset1(B_271, C_272, F_273, F_273, F_273)=k1_enumset1(B_271, C_272, F_273))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3342])).
% 6.07/2.22  tff(c_3418, plain, (![C_272, F_273]: (k2_enumset1(C_272, F_273, F_273, F_273)=k1_enumset1(C_272, C_272, F_273))), inference(superposition, [status(thm), theory('equality')], [c_3362, c_14])).
% 6.07/2.22  tff(c_3477, plain, (![F_274, C_275]: (k2_tarski(F_274, C_275)=k2_tarski(C_275, F_274))), inference(demodulation, [status(thm), theory('equality')], [c_672, c_10, c_3418])).
% 6.07/2.22  tff(c_24, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.07/2.22  tff(c_3880, plain, (![F_282, C_283]: (k1_setfam_1(k2_tarski(F_282, C_283))=k3_xboole_0(C_283, F_282))), inference(superposition, [status(thm), theory('equality')], [c_3477, c_24])).
% 6.07/2.22  tff(c_3886, plain, (![F_282, C_283]: (k3_xboole_0(F_282, C_283)=k3_xboole_0(C_283, F_282))), inference(superposition, [status(thm), theory('equality')], [c_3880, c_24])).
% 6.07/2.22  tff(c_34, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.07/2.22  tff(c_3906, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3886, c_34])).
% 6.07/2.22  tff(c_4164, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_307, c_3906])).
% 6.07/2.22  tff(c_4167, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4164])).
% 6.07/2.22  tff(c_4170, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_4167])).
% 6.07/2.22  tff(c_4174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_4170])).
% 6.07/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.22  
% 6.07/2.22  Inference rules
% 6.07/2.22  ----------------------
% 6.07/2.22  #Ref     : 0
% 6.07/2.22  #Sup     : 1079
% 6.07/2.22  #Fact    : 0
% 6.07/2.22  #Define  : 0
% 6.07/2.22  #Split   : 0
% 6.07/2.22  #Chain   : 0
% 6.07/2.22  #Close   : 0
% 6.07/2.22  
% 6.07/2.22  Ordering : KBO
% 6.07/2.22  
% 6.07/2.22  Simplification rules
% 6.07/2.22  ----------------------
% 6.07/2.22  #Subsume      : 206
% 6.07/2.22  #Demod        : 495
% 6.07/2.22  #Tautology    : 492
% 6.07/2.22  #SimpNegUnit  : 0
% 6.07/2.22  #BackRed      : 1
% 6.07/2.22  
% 6.07/2.22  #Partial instantiations: 0
% 6.07/2.22  #Strategies tried      : 1
% 6.07/2.22  
% 6.07/2.22  Timing (in seconds)
% 6.07/2.22  ----------------------
% 6.07/2.22  Preprocessing        : 0.35
% 6.07/2.22  Parsing              : 0.20
% 6.07/2.22  CNF conversion       : 0.02
% 6.07/2.22  Main loop            : 1.04
% 6.07/2.22  Inferencing          : 0.37
% 6.07/2.22  Reduction            : 0.45
% 6.07/2.22  Demodulation         : 0.39
% 6.07/2.22  BG Simplification    : 0.05
% 6.07/2.22  Subsumption          : 0.13
% 6.07/2.22  Abstraction          : 0.06
% 6.07/2.22  MUC search           : 0.00
% 6.07/2.22  Cooper               : 0.00
% 6.07/2.23  Total                : 1.44
% 6.07/2.23  Index Insertion      : 0.00
% 6.07/2.23  Index Deletion       : 0.00
% 6.07/2.23  Index Matching       : 0.00
% 6.07/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
