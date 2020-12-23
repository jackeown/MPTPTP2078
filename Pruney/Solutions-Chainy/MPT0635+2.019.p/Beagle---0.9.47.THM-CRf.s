%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:23 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 292 expanded)
%              Number of leaves         :   46 ( 118 expanded)
%              Depth                    :   23
%              Number of atoms          :  118 ( 378 expanded)
%              Number of equality atoms :   64 ( 233 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    ! [A_63] : v1_relat_1(k6_relat_1(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    ! [A_63] : v1_funct_1(k6_relat_1(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_60] : k1_relat_1(k6_relat_1(A_60)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_806,plain,(
    ! [B_196,C_197,A_198] :
      ( k1_funct_1(k5_relat_1(B_196,C_197),A_198) = k1_funct_1(C_197,k1_funct_1(B_196,A_198))
      | ~ r2_hidden(A_198,k1_relat_1(B_196))
      | ~ v1_funct_1(C_197)
      | ~ v1_relat_1(C_197)
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_810,plain,(
    ! [A_60,C_197,A_198] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_60),C_197),A_198) = k1_funct_1(C_197,k1_funct_1(k6_relat_1(A_60),A_198))
      | ~ r2_hidden(A_198,A_60)
      | ~ v1_funct_1(C_197)
      | ~ v1_relat_1(C_197)
      | ~ v1_funct_1(k6_relat_1(A_60))
      | ~ v1_relat_1(k6_relat_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_806])).

tff(c_1041,plain,(
    ! [A_211,C_212,A_213] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_211),C_212),A_213) = k1_funct_1(C_212,k1_funct_1(k6_relat_1(A_211),A_213))
      | ~ r2_hidden(A_213,A_211)
      | ~ v1_funct_1(C_212)
      | ~ v1_relat_1(C_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_810])).

tff(c_54,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1047,plain,
    ( k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_54])).

tff(c_1056,plain,
    ( k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1047])).

tff(c_1102,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1056])).

tff(c_12,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_230,plain,(
    ! [D_108,C_109,B_110,A_111] : k2_enumset1(D_108,C_109,B_110,A_111) = k2_enumset1(A_111,B_110,C_109,D_108) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,(
    ! [C_112,B_113,A_114] : k2_enumset1(C_112,B_113,A_114,A_114) = k1_enumset1(A_114,B_113,C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_230])).

tff(c_294,plain,(
    ! [B_113,A_114] : k1_enumset1(B_113,A_114,A_114) = k1_enumset1(A_114,B_113,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_14])).

tff(c_16,plain,(
    ! [A_28,B_29,C_30,D_31] : k3_enumset1(A_28,A_28,B_29,C_30,D_31) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_33,C_34,E_36,A_32,D_35] : k4_enumset1(A_32,A_32,B_33,C_34,D_35,E_36) = k3_enumset1(A_32,B_33,C_34,D_35,E_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_426,plain,(
    ! [A_152,C_155,D_156,E_153,F_151,B_154] : k2_xboole_0(k3_enumset1(A_152,B_154,C_155,D_156,E_153),k1_tarski(F_151)) = k4_enumset1(A_152,B_154,C_155,D_156,E_153,F_151) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_435,plain,(
    ! [C_30,D_31,B_29,F_151,A_28] : k4_enumset1(A_28,A_28,B_29,C_30,D_31,F_151) = k2_xboole_0(k2_enumset1(A_28,B_29,C_30,D_31),k1_tarski(F_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_426])).

tff(c_439,plain,(
    ! [F_158,C_159,D_161,A_157,B_160] : k2_xboole_0(k2_enumset1(A_157,B_160,C_159,D_161),k1_tarski(F_158)) = k3_enumset1(A_157,B_160,C_159,D_161,F_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_435])).

tff(c_457,plain,(
    ! [A_25,B_26,C_27,F_158] : k3_enumset1(A_25,A_25,B_26,C_27,F_158) = k2_xboole_0(k1_enumset1(A_25,B_26,C_27),k1_tarski(F_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_439])).

tff(c_461,plain,(
    ! [A_162,B_163,C_164,F_165] : k2_xboole_0(k1_enumset1(A_162,B_163,C_164),k1_tarski(F_165)) = k2_enumset1(A_162,B_163,C_164,F_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_457])).

tff(c_531,plain,(
    ! [B_179,A_180,F_181] : k2_xboole_0(k1_enumset1(B_179,A_180,A_180),k1_tarski(F_181)) = k2_enumset1(A_180,B_179,B_179,F_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_461])).

tff(c_460,plain,(
    ! [A_25,B_26,C_27,F_158] : k2_xboole_0(k1_enumset1(A_25,B_26,C_27),k1_tarski(F_158)) = k2_enumset1(A_25,B_26,C_27,F_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_457])).

tff(c_596,plain,(
    ! [B_182,A_183,F_184] : k2_enumset1(B_182,A_183,A_183,F_184) = k2_enumset1(A_183,B_182,B_182,F_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_460])).

tff(c_265,plain,(
    ! [C_27,B_26,A_25] : k2_enumset1(C_27,B_26,A_25,A_25) = k1_enumset1(A_25,B_26,C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_230])).

tff(c_624,plain,(
    ! [F_184,A_183] : k2_enumset1(F_184,A_183,A_183,F_184) = k1_enumset1(F_184,F_184,A_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_265])).

tff(c_721,plain,(
    ! [F_193,A_194] : k2_enumset1(F_193,A_194,A_194,F_193) = k2_tarski(F_193,A_194) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_624])).

tff(c_540,plain,(
    ! [B_179,A_180,F_181] : k2_enumset1(B_179,A_180,A_180,F_181) = k2_enumset1(A_180,B_179,B_179,F_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_460])).

tff(c_727,plain,(
    ! [A_194,F_193] : k2_enumset1(A_194,F_193,F_193,F_193) = k2_tarski(F_193,A_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_540])).

tff(c_10,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_740,plain,(
    ! [F_193] : k1_enumset1(F_193,F_193,F_193) = k2_tarski(F_193,F_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_265])).

tff(c_770,plain,(
    ! [F_193] : k1_enumset1(F_193,F_193,F_193) = k1_tarski(F_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_740])).

tff(c_20,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] : k5_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,F_42) = k4_enumset1(A_37,B_38,C_39,D_40,E_41,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [G_49,E_47,F_48,D_46,C_45,A_43,B_44] : k6_enumset1(A_43,A_43,B_44,C_45,D_46,E_47,F_48,G_49) = k5_enumset1(A_43,B_44,C_45,D_46,E_47,F_48,G_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_699,plain,(
    ! [D_188,C_190,B_191,G_189,E_186,A_192,F_187,H_185] : k2_xboole_0(k3_enumset1(A_192,B_191,C_190,D_188,E_186),k1_enumset1(F_187,G_189,H_185)) = k6_enumset1(A_192,B_191,C_190,D_188,E_186,F_187,G_189,H_185) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_714,plain,(
    ! [C_30,G_189,D_31,B_29,F_187,A_28,H_185] : k6_enumset1(A_28,A_28,B_29,C_30,D_31,F_187,G_189,H_185) = k2_xboole_0(k2_enumset1(A_28,B_29,C_30,D_31),k1_enumset1(F_187,G_189,H_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_699])).

tff(c_821,plain,(
    ! [A_200,D_204,B_203,G_202,F_205,C_201,H_199] : k2_xboole_0(k2_enumset1(A_200,B_203,C_201,D_204),k1_enumset1(F_205,G_202,H_199)) = k5_enumset1(A_200,B_203,C_201,D_204,F_205,G_202,H_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_714])).

tff(c_860,plain,(
    ! [A_25,G_202,F_205,C_27,H_199,B_26] : k5_enumset1(A_25,A_25,B_26,C_27,F_205,G_202,H_199) = k2_xboole_0(k1_enumset1(A_25,B_26,C_27),k1_enumset1(F_205,G_202,H_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_821])).

tff(c_2982,plain,(
    ! [C_290,F_293,A_288,H_292,G_289,B_291] : k2_xboole_0(k1_enumset1(A_288,B_291,C_290),k1_enumset1(F_293,G_289,H_292)) = k4_enumset1(A_288,B_291,C_290,F_293,G_289,H_292) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_860])).

tff(c_2998,plain,(
    ! [A_288,B_291,C_290,F_193] : k4_enumset1(A_288,B_291,C_290,F_193,F_193,F_193) = k2_xboole_0(k1_enumset1(A_288,B_291,C_290),k1_tarski(F_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_2982])).

tff(c_3409,plain,(
    ! [A_318,B_319,C_320,F_321] : k4_enumset1(A_318,B_319,C_320,F_321,F_321,F_321) = k2_enumset1(A_318,B_319,C_320,F_321) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_2998])).

tff(c_3447,plain,(
    ! [A_32,B_33,E_36] : k3_enumset1(A_32,B_33,E_36,E_36,E_36) = k2_enumset1(A_32,A_32,B_33,E_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3409])).

tff(c_3843,plain,(
    ! [A_330,B_331,E_332] : k3_enumset1(A_330,B_331,E_332,E_332,E_332) = k1_enumset1(A_330,B_331,E_332) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3447])).

tff(c_3899,plain,(
    ! [B_331,E_332] : k2_enumset1(B_331,E_332,E_332,E_332) = k1_enumset1(B_331,B_331,E_332) ),
    inference(superposition,[status(thm),theory(equality)],[c_3843,c_16])).

tff(c_3960,plain,(
    ! [E_333,B_334] : k2_tarski(E_333,B_334) = k2_tarski(B_334,E_333) ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_12,c_3899])).

tff(c_36,plain,(
    ! [A_57,B_58] : k1_setfam_1(k2_tarski(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4188,plain,(
    ! [B_344,E_345] : k1_setfam_1(k2_tarski(B_344,E_345)) = k3_xboole_0(E_345,B_344) ),
    inference(superposition,[status(thm),theory(equality)],[c_3960,c_36])).

tff(c_4194,plain,(
    ! [E_345,B_344] : k3_xboole_0(E_345,B_344) = k3_xboole_0(B_344,E_345) ),
    inference(superposition,[status(thm),theory(equality)],[c_4188,c_36])).

tff(c_56,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4215,plain,(
    r2_hidden('#skF_1',k3_xboole_0('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4194,c_56])).

tff(c_26,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_tarski(A_95,B_96)
      | ~ r1_tarski(A_95,k3_xboole_0(B_96,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [A_50,B_96,C_97] :
      ( r1_tarski(k1_tarski(A_50),B_96)
      | ~ r2_hidden(A_50,k3_xboole_0(B_96,C_97)) ) ),
    inference(resolution,[status(thm)],[c_26,c_181])).

tff(c_4271,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4215,c_189])).

tff(c_24,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | ~ r1_tarski(k1_tarski(A_50),B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4274,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4271,c_24])).

tff(c_4278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1102,c_4274])).

tff(c_4280,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1056])).

tff(c_52,plain,(
    ! [B_69,A_68] :
      ( k1_funct_1(k6_relat_1(B_69),A_68) = A_68
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4279,plain,(
    k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1056])).

tff(c_4309,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4279])).

tff(c_4313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4280,c_4309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/2.01  
% 4.95/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/2.01  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.95/2.01  
% 4.95/2.01  %Foreground sorts:
% 4.95/2.01  
% 4.95/2.01  
% 4.95/2.01  %Background operators:
% 4.95/2.01  
% 4.95/2.01  
% 4.95/2.01  %Foreground operators:
% 4.95/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.95/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/2.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.95/2.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.95/2.01  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.95/2.01  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.95/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.95/2.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.95/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.95/2.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.95/2.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.95/2.01  tff('#skF_2', type, '#skF_2': $i).
% 4.95/2.01  tff('#skF_3', type, '#skF_3': $i).
% 4.95/2.01  tff('#skF_1', type, '#skF_1': $i).
% 4.95/2.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.95/2.01  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.95/2.01  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.95/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/2.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.95/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.95/2.01  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.95/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.95/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.95/2.01  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.95/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.95/2.01  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.95/2.01  
% 5.37/2.03  tff(f_103, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 5.37/2.03  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.37/2.03  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.37/2.03  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 5.37/2.03  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.37/2.03  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.37/2.03  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 5.37/2.03  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 5.37/2.03  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 5.37/2.03  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 5.37/2.03  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.37/2.03  tff(f_47, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 5.37/2.03  tff(f_49, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 5.37/2.03  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 5.37/2.03  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.37/2.03  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.37/2.03  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 5.37/2.03  tff(f_94, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 5.37/2.03  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.37/2.03  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.37/2.03  tff(c_46, plain, (![A_63]: (v1_relat_1(k6_relat_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.37/2.03  tff(c_48, plain, (![A_63]: (v1_funct_1(k6_relat_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.37/2.03  tff(c_40, plain, (![A_60]: (k1_relat_1(k6_relat_1(A_60))=A_60)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.37/2.03  tff(c_806, plain, (![B_196, C_197, A_198]: (k1_funct_1(k5_relat_1(B_196, C_197), A_198)=k1_funct_1(C_197, k1_funct_1(B_196, A_198)) | ~r2_hidden(A_198, k1_relat_1(B_196)) | ~v1_funct_1(C_197) | ~v1_relat_1(C_197) | ~v1_funct_1(B_196) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.37/2.03  tff(c_810, plain, (![A_60, C_197, A_198]: (k1_funct_1(k5_relat_1(k6_relat_1(A_60), C_197), A_198)=k1_funct_1(C_197, k1_funct_1(k6_relat_1(A_60), A_198)) | ~r2_hidden(A_198, A_60) | ~v1_funct_1(C_197) | ~v1_relat_1(C_197) | ~v1_funct_1(k6_relat_1(A_60)) | ~v1_relat_1(k6_relat_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_806])).
% 5.37/2.03  tff(c_1041, plain, (![A_211, C_212, A_213]: (k1_funct_1(k5_relat_1(k6_relat_1(A_211), C_212), A_213)=k1_funct_1(C_212, k1_funct_1(k6_relat_1(A_211), A_213)) | ~r2_hidden(A_213, A_211) | ~v1_funct_1(C_212) | ~v1_relat_1(C_212))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_810])).
% 5.37/2.03  tff(c_54, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.37/2.03  tff(c_1047, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1041, c_54])).
% 5.37/2.03  tff(c_1056, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1047])).
% 5.37/2.03  tff(c_1102, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_1056])).
% 5.37/2.03  tff(c_12, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.37/2.03  tff(c_14, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.37/2.03  tff(c_230, plain, (![D_108, C_109, B_110, A_111]: (k2_enumset1(D_108, C_109, B_110, A_111)=k2_enumset1(A_111, B_110, C_109, D_108))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.37/2.03  tff(c_281, plain, (![C_112, B_113, A_114]: (k2_enumset1(C_112, B_113, A_114, A_114)=k1_enumset1(A_114, B_113, C_112))), inference(superposition, [status(thm), theory('equality')], [c_14, c_230])).
% 5.37/2.03  tff(c_294, plain, (![B_113, A_114]: (k1_enumset1(B_113, A_114, A_114)=k1_enumset1(A_114, B_113, B_113))), inference(superposition, [status(thm), theory('equality')], [c_281, c_14])).
% 5.37/2.03  tff(c_16, plain, (![A_28, B_29, C_30, D_31]: (k3_enumset1(A_28, A_28, B_29, C_30, D_31)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.37/2.03  tff(c_18, plain, (![B_33, C_34, E_36, A_32, D_35]: (k4_enumset1(A_32, A_32, B_33, C_34, D_35, E_36)=k3_enumset1(A_32, B_33, C_34, D_35, E_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.37/2.03  tff(c_426, plain, (![A_152, C_155, D_156, E_153, F_151, B_154]: (k2_xboole_0(k3_enumset1(A_152, B_154, C_155, D_156, E_153), k1_tarski(F_151))=k4_enumset1(A_152, B_154, C_155, D_156, E_153, F_151))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.37/2.03  tff(c_435, plain, (![C_30, D_31, B_29, F_151, A_28]: (k4_enumset1(A_28, A_28, B_29, C_30, D_31, F_151)=k2_xboole_0(k2_enumset1(A_28, B_29, C_30, D_31), k1_tarski(F_151)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_426])).
% 5.37/2.03  tff(c_439, plain, (![F_158, C_159, D_161, A_157, B_160]: (k2_xboole_0(k2_enumset1(A_157, B_160, C_159, D_161), k1_tarski(F_158))=k3_enumset1(A_157, B_160, C_159, D_161, F_158))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_435])).
% 5.37/2.03  tff(c_457, plain, (![A_25, B_26, C_27, F_158]: (k3_enumset1(A_25, A_25, B_26, C_27, F_158)=k2_xboole_0(k1_enumset1(A_25, B_26, C_27), k1_tarski(F_158)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_439])).
% 5.37/2.03  tff(c_461, plain, (![A_162, B_163, C_164, F_165]: (k2_xboole_0(k1_enumset1(A_162, B_163, C_164), k1_tarski(F_165))=k2_enumset1(A_162, B_163, C_164, F_165))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_457])).
% 5.37/2.03  tff(c_531, plain, (![B_179, A_180, F_181]: (k2_xboole_0(k1_enumset1(B_179, A_180, A_180), k1_tarski(F_181))=k2_enumset1(A_180, B_179, B_179, F_181))), inference(superposition, [status(thm), theory('equality')], [c_294, c_461])).
% 5.37/2.03  tff(c_460, plain, (![A_25, B_26, C_27, F_158]: (k2_xboole_0(k1_enumset1(A_25, B_26, C_27), k1_tarski(F_158))=k2_enumset1(A_25, B_26, C_27, F_158))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_457])).
% 5.37/2.03  tff(c_596, plain, (![B_182, A_183, F_184]: (k2_enumset1(B_182, A_183, A_183, F_184)=k2_enumset1(A_183, B_182, B_182, F_184))), inference(superposition, [status(thm), theory('equality')], [c_531, c_460])).
% 5.37/2.03  tff(c_265, plain, (![C_27, B_26, A_25]: (k2_enumset1(C_27, B_26, A_25, A_25)=k1_enumset1(A_25, B_26, C_27))), inference(superposition, [status(thm), theory('equality')], [c_14, c_230])).
% 5.37/2.03  tff(c_624, plain, (![F_184, A_183]: (k2_enumset1(F_184, A_183, A_183, F_184)=k1_enumset1(F_184, F_184, A_183))), inference(superposition, [status(thm), theory('equality')], [c_596, c_265])).
% 5.37/2.03  tff(c_721, plain, (![F_193, A_194]: (k2_enumset1(F_193, A_194, A_194, F_193)=k2_tarski(F_193, A_194))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_624])).
% 5.37/2.03  tff(c_540, plain, (![B_179, A_180, F_181]: (k2_enumset1(B_179, A_180, A_180, F_181)=k2_enumset1(A_180, B_179, B_179, F_181))), inference(superposition, [status(thm), theory('equality')], [c_531, c_460])).
% 5.37/2.03  tff(c_727, plain, (![A_194, F_193]: (k2_enumset1(A_194, F_193, F_193, F_193)=k2_tarski(F_193, A_194))), inference(superposition, [status(thm), theory('equality')], [c_721, c_540])).
% 5.37/2.03  tff(c_10, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.37/2.03  tff(c_740, plain, (![F_193]: (k1_enumset1(F_193, F_193, F_193)=k2_tarski(F_193, F_193))), inference(superposition, [status(thm), theory('equality')], [c_721, c_265])).
% 5.37/2.03  tff(c_770, plain, (![F_193]: (k1_enumset1(F_193, F_193, F_193)=k1_tarski(F_193))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_740])).
% 5.37/2.03  tff(c_20, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (k5_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, F_42)=k4_enumset1(A_37, B_38, C_39, D_40, E_41, F_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.37/2.03  tff(c_22, plain, (![G_49, E_47, F_48, D_46, C_45, A_43, B_44]: (k6_enumset1(A_43, A_43, B_44, C_45, D_46, E_47, F_48, G_49)=k5_enumset1(A_43, B_44, C_45, D_46, E_47, F_48, G_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.37/2.03  tff(c_699, plain, (![D_188, C_190, B_191, G_189, E_186, A_192, F_187, H_185]: (k2_xboole_0(k3_enumset1(A_192, B_191, C_190, D_188, E_186), k1_enumset1(F_187, G_189, H_185))=k6_enumset1(A_192, B_191, C_190, D_188, E_186, F_187, G_189, H_185))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.37/2.03  tff(c_714, plain, (![C_30, G_189, D_31, B_29, F_187, A_28, H_185]: (k6_enumset1(A_28, A_28, B_29, C_30, D_31, F_187, G_189, H_185)=k2_xboole_0(k2_enumset1(A_28, B_29, C_30, D_31), k1_enumset1(F_187, G_189, H_185)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_699])).
% 5.37/2.03  tff(c_821, plain, (![A_200, D_204, B_203, G_202, F_205, C_201, H_199]: (k2_xboole_0(k2_enumset1(A_200, B_203, C_201, D_204), k1_enumset1(F_205, G_202, H_199))=k5_enumset1(A_200, B_203, C_201, D_204, F_205, G_202, H_199))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_714])).
% 5.37/2.03  tff(c_860, plain, (![A_25, G_202, F_205, C_27, H_199, B_26]: (k5_enumset1(A_25, A_25, B_26, C_27, F_205, G_202, H_199)=k2_xboole_0(k1_enumset1(A_25, B_26, C_27), k1_enumset1(F_205, G_202, H_199)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_821])).
% 5.37/2.03  tff(c_2982, plain, (![C_290, F_293, A_288, H_292, G_289, B_291]: (k2_xboole_0(k1_enumset1(A_288, B_291, C_290), k1_enumset1(F_293, G_289, H_292))=k4_enumset1(A_288, B_291, C_290, F_293, G_289, H_292))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_860])).
% 5.37/2.03  tff(c_2998, plain, (![A_288, B_291, C_290, F_193]: (k4_enumset1(A_288, B_291, C_290, F_193, F_193, F_193)=k2_xboole_0(k1_enumset1(A_288, B_291, C_290), k1_tarski(F_193)))), inference(superposition, [status(thm), theory('equality')], [c_770, c_2982])).
% 5.37/2.03  tff(c_3409, plain, (![A_318, B_319, C_320, F_321]: (k4_enumset1(A_318, B_319, C_320, F_321, F_321, F_321)=k2_enumset1(A_318, B_319, C_320, F_321))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_2998])).
% 5.37/2.03  tff(c_3447, plain, (![A_32, B_33, E_36]: (k3_enumset1(A_32, B_33, E_36, E_36, E_36)=k2_enumset1(A_32, A_32, B_33, E_36))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3409])).
% 5.37/2.03  tff(c_3843, plain, (![A_330, B_331, E_332]: (k3_enumset1(A_330, B_331, E_332, E_332, E_332)=k1_enumset1(A_330, B_331, E_332))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3447])).
% 5.37/2.03  tff(c_3899, plain, (![B_331, E_332]: (k2_enumset1(B_331, E_332, E_332, E_332)=k1_enumset1(B_331, B_331, E_332))), inference(superposition, [status(thm), theory('equality')], [c_3843, c_16])).
% 5.37/2.03  tff(c_3960, plain, (![E_333, B_334]: (k2_tarski(E_333, B_334)=k2_tarski(B_334, E_333))), inference(demodulation, [status(thm), theory('equality')], [c_727, c_12, c_3899])).
% 5.37/2.03  tff(c_36, plain, (![A_57, B_58]: (k1_setfam_1(k2_tarski(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.37/2.03  tff(c_4188, plain, (![B_344, E_345]: (k1_setfam_1(k2_tarski(B_344, E_345))=k3_xboole_0(E_345, B_344))), inference(superposition, [status(thm), theory('equality')], [c_3960, c_36])).
% 5.37/2.03  tff(c_4194, plain, (![E_345, B_344]: (k3_xboole_0(E_345, B_344)=k3_xboole_0(B_344, E_345))), inference(superposition, [status(thm), theory('equality')], [c_4188, c_36])).
% 5.37/2.03  tff(c_56, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.37/2.03  tff(c_4215, plain, (r2_hidden('#skF_1', k3_xboole_0('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4194, c_56])).
% 5.37/2.03  tff(c_26, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.03  tff(c_181, plain, (![A_95, B_96, C_97]: (r1_tarski(A_95, B_96) | ~r1_tarski(A_95, k3_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.37/2.03  tff(c_189, plain, (![A_50, B_96, C_97]: (r1_tarski(k1_tarski(A_50), B_96) | ~r2_hidden(A_50, k3_xboole_0(B_96, C_97)))), inference(resolution, [status(thm)], [c_26, c_181])).
% 5.37/2.03  tff(c_4271, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_4215, c_189])).
% 5.37/2.03  tff(c_24, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | ~r1_tarski(k1_tarski(A_50), B_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.03  tff(c_4274, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4271, c_24])).
% 5.37/2.03  tff(c_4278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1102, c_4274])).
% 5.37/2.03  tff(c_4280, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1056])).
% 5.37/2.03  tff(c_52, plain, (![B_69, A_68]: (k1_funct_1(k6_relat_1(B_69), A_68)=A_68 | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.37/2.03  tff(c_4279, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1056])).
% 5.37/2.03  tff(c_4309, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_52, c_4279])).
% 5.37/2.03  tff(c_4313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4280, c_4309])).
% 5.37/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.03  
% 5.37/2.03  Inference rules
% 5.37/2.03  ----------------------
% 5.37/2.03  #Ref     : 0
% 5.37/2.03  #Sup     : 1053
% 5.37/2.03  #Fact    : 0
% 5.37/2.03  #Define  : 0
% 5.37/2.03  #Split   : 1
% 5.37/2.03  #Chain   : 0
% 5.37/2.03  #Close   : 0
% 5.37/2.03  
% 5.37/2.03  Ordering : KBO
% 5.37/2.03  
% 5.37/2.03  Simplification rules
% 5.37/2.03  ----------------------
% 5.37/2.03  #Subsume      : 208
% 5.37/2.03  #Demod        : 683
% 5.37/2.03  #Tautology    : 575
% 5.37/2.03  #SimpNegUnit  : 1
% 5.37/2.03  #BackRed      : 10
% 5.37/2.03  
% 5.37/2.03  #Partial instantiations: 0
% 5.37/2.03  #Strategies tried      : 1
% 5.37/2.03  
% 5.37/2.03  Timing (in seconds)
% 5.37/2.03  ----------------------
% 5.37/2.03  Preprocessing        : 0.34
% 5.37/2.03  Parsing              : 0.18
% 5.37/2.03  CNF conversion       : 0.02
% 5.37/2.03  Main loop            : 0.92
% 5.37/2.03  Inferencing          : 0.32
% 5.37/2.03  Reduction            : 0.40
% 5.37/2.03  Demodulation         : 0.33
% 5.37/2.03  BG Simplification    : 0.04
% 5.37/2.03  Subsumption          : 0.11
% 5.37/2.03  Abstraction          : 0.05
% 5.37/2.03  MUC search           : 0.00
% 5.37/2.03  Cooper               : 0.00
% 5.37/2.03  Total                : 1.30
% 5.37/2.03  Index Insertion      : 0.00
% 5.37/2.03  Index Deletion       : 0.00
% 5.37/2.03  Index Matching       : 0.00
% 5.37/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
