%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:19 EST 2020

% Result     : Theorem 29.91s
% Output     : CNFRefutation 30.03s
% Verified   : 
% Statistics : Number of formulae       :  163 (1648 expanded)
%              Number of leaves         :   37 ( 605 expanded)
%              Depth                    :   37
%              Number of atoms          :  275 (2931 expanded)
%              Number of equality atoms :   92 (1262 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    ! [A_36] : k2_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_40,A_39)),A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_128,plain,(
    ! [B_60,A_61] : k1_setfam_1(k2_tarski(B_60,A_61)) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_113])).

tff(c_14,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_14])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_167,plain,(
    ! [B_62,A_63] : r1_tarski(k3_xboole_0(B_62,A_63),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_40,plain,(
    ! [A_45] : v1_relat_1(k6_relat_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_36] : k1_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_265,plain,(
    ! [B_81,A_82] :
      ( k5_relat_1(B_81,k6_relat_1(A_82)) = B_81
      | ~ r1_tarski(k2_relat_1(B_81),A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_271,plain,(
    ! [A_36,A_82] :
      ( k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_82)) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_82)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_265])).

tff(c_296,plain,(
    ! [A_85,A_86] :
      ( k5_relat_1(k6_relat_1(A_85),k6_relat_1(A_86)) = k6_relat_1(A_85)
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_271])).

tff(c_38,plain,(
    ! [A_43,B_44] :
      ( k5_relat_1(k6_relat_1(A_43),B_44) = k7_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_302,plain,(
    ! [A_86,A_85] :
      ( k7_relat_1(k6_relat_1(A_86),A_85) = k6_relat_1(A_85)
      | ~ v1_relat_1(k6_relat_1(A_86))
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_38])).

tff(c_316,plain,(
    ! [A_87,A_88] :
      ( k7_relat_1(k6_relat_1(A_87),A_88) = k6_relat_1(A_88)
      | ~ r1_tarski(A_88,A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_302])).

tff(c_22,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(k7_relat_1(B_27,A_26)) = k9_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_322,plain,(
    ! [A_87,A_88] :
      ( k9_relat_1(k6_relat_1(A_87),A_88) = k2_relat_1(k6_relat_1(A_88))
      | ~ v1_relat_1(k6_relat_1(A_87))
      | ~ r1_tarski(A_88,A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_22])).

tff(c_446,plain,(
    ! [A_102,A_103] :
      ( k9_relat_1(k6_relat_1(A_102),A_103) = A_103
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_322])).

tff(c_18,plain,(
    ! [B_24,A_23] :
      ( k9_relat_1(B_24,k3_xboole_0(k1_relat_1(B_24),A_23)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_453,plain,(
    ! [A_102,A_23] :
      ( k3_xboole_0(k1_relat_1(k6_relat_1(A_102)),A_23) = k9_relat_1(k6_relat_1(A_102),A_23)
      | ~ v1_relat_1(k6_relat_1(A_102))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_102)),A_23),A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_18])).

tff(c_478,plain,(
    ! [A_102,A_23] : k9_relat_1(k6_relat_1(A_102),A_23) = k3_xboole_0(A_102,A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28,c_40,c_28,c_453])).

tff(c_585,plain,(
    ! [A_113,B_114] :
      ( k7_relat_1(A_113,k1_relat_1(k7_relat_1(B_114,k1_relat_1(A_113)))) = k7_relat_1(A_113,k1_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_631,plain,(
    ! [A_36,B_114] :
      ( k7_relat_1(k6_relat_1(A_36),k1_relat_1(k7_relat_1(B_114,A_36))) = k7_relat_1(k6_relat_1(A_36),k1_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_585])).

tff(c_964,plain,(
    ! [A_126,B_127] :
      ( k7_relat_1(k6_relat_1(A_126),k1_relat_1(k7_relat_1(B_127,A_126))) = k7_relat_1(k6_relat_1(A_126),k1_relat_1(B_127))
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_631])).

tff(c_16,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_994,plain,(
    ! [A_126,B_127] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_126),k1_relat_1(B_127)))
      | ~ v1_relat_1(k6_relat_1(A_126))
      | ~ v1_relat_1(B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_16])).

tff(c_1037,plain,(
    ! [A_128,B_129] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_128),k1_relat_1(B_129)))
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_994])).

tff(c_1055,plain,(
    ! [A_128,A_36] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_128),A_36))
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1037])).

tff(c_1061,plain,(
    ! [A_128,A_36] : v1_relat_1(k7_relat_1(k6_relat_1(A_128),A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1055])).

tff(c_415,plain,(
    ! [A_99,C_100,B_101] :
      ( k9_relat_1(k7_relat_1(A_99,C_100),B_101) = k9_relat_1(A_99,B_101)
      | ~ r1_tarski(B_101,C_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_relat_1(A_25)) = k2_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2877,plain,(
    ! [A_165,C_166] :
      ( k9_relat_1(A_165,k1_relat_1(k7_relat_1(A_165,C_166))) = k2_relat_1(k7_relat_1(A_165,C_166))
      | ~ v1_relat_1(k7_relat_1(A_165,C_166))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_165,C_166)),C_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_20])).

tff(c_9219,plain,(
    ! [B_259,A_260] :
      ( k9_relat_1(B_259,k1_relat_1(k7_relat_1(B_259,A_260))) = k2_relat_1(k7_relat_1(B_259,A_260))
      | ~ v1_relat_1(k7_relat_1(B_259,A_260))
      | ~ v1_relat_1(B_259) ) ),
    inference(resolution,[status(thm)],[c_34,c_2877])).

tff(c_9287,plain,(
    ! [A_102,A_260] :
      ( k3_xboole_0(A_102,k1_relat_1(k7_relat_1(k6_relat_1(A_102),A_260))) = k2_relat_1(k7_relat_1(k6_relat_1(A_102),A_260))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_102),A_260))
      | ~ v1_relat_1(k6_relat_1(A_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_9219])).

tff(c_35213,plain,(
    ! [A_464,A_465] : k3_xboole_0(A_464,k1_relat_1(k7_relat_1(k6_relat_1(A_464),A_465))) = k2_relat_1(k7_relat_1(k6_relat_1(A_464),A_465)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1061,c_9287])).

tff(c_35990,plain,(
    ! [A_468,A_469] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_468),A_469)),k1_relat_1(k7_relat_1(k6_relat_1(A_468),A_469))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35213,c_167])).

tff(c_36229,plain,(
    ! [A_468,A_26] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_468),A_26),k1_relat_1(k7_relat_1(k6_relat_1(A_468),A_26)))
      | ~ v1_relat_1(k6_relat_1(A_468)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_35990])).

tff(c_36295,plain,(
    ! [A_468,A_26] : r1_tarski(k3_xboole_0(A_468,A_26),k1_relat_1(k7_relat_1(k6_relat_1(A_468),A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_478,c_36229])).

tff(c_226,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_70,A_71)),k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_229,plain,(
    ! [A_36,A_71] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_36),A_71)),A_36)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_226])).

tff(c_231,plain,(
    ! [A_36,A_71] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_36),A_71)),A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_229])).

tff(c_312,plain,(
    ! [A_86,A_85] :
      ( k7_relat_1(k6_relat_1(A_86),A_85) = k6_relat_1(A_85)
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_302])).

tff(c_36,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_42,A_41)),k1_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_340,plain,(
    ! [A_87,A_88] :
      ( k9_relat_1(k6_relat_1(A_87),A_88) = A_88
      | ~ r1_tarski(A_88,A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_322])).

tff(c_648,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = A_116
      | ~ r1_tarski(A_116,A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_340])).

tff(c_3452,plain,(
    ! [B_181,A_182] :
      ( k3_xboole_0(k1_relat_1(B_181),k1_relat_1(k7_relat_1(B_181,A_182))) = k1_relat_1(k7_relat_1(B_181,A_182))
      | ~ v1_relat_1(B_181) ) ),
    inference(resolution,[status(thm)],[c_36,c_648])).

tff(c_3565,plain,(
    ! [A_86,A_85] :
      ( k3_xboole_0(k1_relat_1(k6_relat_1(A_86)),k1_relat_1(k6_relat_1(A_85))) = k1_relat_1(k7_relat_1(k6_relat_1(A_86),A_85))
      | ~ v1_relat_1(k6_relat_1(A_86))
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_3452])).

tff(c_3609,plain,(
    ! [A_86,A_85] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_86),A_85)) = k3_xboole_0(A_86,A_85)
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_28,c_3565])).

tff(c_489,plain,(
    ! [A_104,A_105] : k9_relat_1(k6_relat_1(A_104),A_105) = k3_xboole_0(A_104,A_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28,c_40,c_28,c_453])).

tff(c_200,plain,(
    ! [A_66] :
      ( k9_relat_1(A_66,k1_relat_1(A_66)) = k2_relat_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_209,plain,(
    ! [A_36] :
      ( k9_relat_1(k6_relat_1(A_36),A_36) = k2_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_200])).

tff(c_213,plain,(
    ! [A_36] : k9_relat_1(k6_relat_1(A_36),A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_209])).

tff(c_500,plain,(
    ! [A_105] : k3_xboole_0(A_105,A_105) = A_105 ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_213])).

tff(c_529,plain,(
    ! [A_106] : k3_xboole_0(A_106,A_106) = A_106 ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_213])).

tff(c_134,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_14])).

tff(c_331,plain,(
    ! [A_88,A_87] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_88)),A_88)
      | ~ v1_relat_1(k6_relat_1(A_87))
      | ~ r1_tarski(A_88,A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_34])).

tff(c_349,plain,(
    ! [A_89,A_90] :
      ( r1_tarski(A_89,A_89)
      | ~ r1_tarski(A_89,A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_331])).

tff(c_365,plain,(
    ! [B_91,A_92] : r1_tarski(k3_xboole_0(B_91,A_92),k3_xboole_0(B_91,A_92)) ),
    inference(resolution,[status(thm)],[c_167,c_349])).

tff(c_373,plain,(
    ! [A_61,B_60] : r1_tarski(k3_xboole_0(A_61,B_60),k3_xboole_0(B_60,A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_365])).

tff(c_535,plain,(
    ! [A_106] : r1_tarski(A_106,k3_xboole_0(A_106,A_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_373])).

tff(c_567,plain,(
    ! [A_107] : r1_tarski(A_107,A_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_535])).

tff(c_32,plain,(
    ! [B_38,A_37] :
      ( k5_relat_1(B_38,k6_relat_1(A_37)) = B_38
      | ~ r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_759,plain,(
    ! [B_121] :
      ( k5_relat_1(B_121,k6_relat_1(k2_relat_1(B_121))) = B_121
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_567,c_32])).

tff(c_770,plain,(
    ! [A_43] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_43))),A_43) = k6_relat_1(A_43)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_43))))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_38])).

tff(c_793,plain,(
    ! [A_43] : k7_relat_1(k6_relat_1(A_43),A_43) = k6_relat_1(A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_30,c_770])).

tff(c_1009,plain,(
    ! [A_85,A_86] :
      ( k7_relat_1(k6_relat_1(A_85),k1_relat_1(k6_relat_1(A_86))) = k7_relat_1(k6_relat_1(A_85),k1_relat_1(k6_relat_1(A_85)))
      | ~ v1_relat_1(k6_relat_1(A_86))
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_964])).

tff(c_1036,plain,(
    ! [A_85,A_86] :
      ( k7_relat_1(k6_relat_1(A_85),A_86) = k6_relat_1(A_85)
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_793,c_28,c_28,c_1009])).

tff(c_1440,plain,(
    ! [A_140,B_141] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_140,k1_relat_1(B_141))),k1_relat_1(k7_relat_1(B_141,k1_relat_1(A_140))))
      | ~ v1_relat_1(A_140)
      | ~ v1_relat_1(B_141)
      | ~ v1_relat_1(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_34])).

tff(c_1477,plain,(
    ! [A_36,B_141] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_36),k1_relat_1(B_141))),k1_relat_1(k7_relat_1(B_141,A_36)))
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(B_141)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1440])).

tff(c_6300,plain,(
    ! [A_224,B_225] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_224),k1_relat_1(B_225))),k1_relat_1(k7_relat_1(B_225,A_224)))
      | ~ v1_relat_1(B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_1477])).

tff(c_6413,plain,(
    ! [A_224,A_36] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_224),A_36)),k1_relat_1(k7_relat_1(k6_relat_1(A_36),A_224)))
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6300])).

tff(c_6531,plain,(
    ! [A_228,A_229] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_228),A_229)),k1_relat_1(k7_relat_1(k6_relat_1(A_229),A_228))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6413])).

tff(c_6592,plain,(
    ! [A_85,A_86] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_85)),k1_relat_1(k7_relat_1(k6_relat_1(A_86),A_85)))
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_6531])).

tff(c_6734,plain,(
    ! [A_232,A_233] :
      ( r1_tarski(A_232,k1_relat_1(k7_relat_1(k6_relat_1(A_233),A_232)))
      | ~ r1_tarski(A_232,A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6592])).

tff(c_8935,plain,(
    ! [A_255,A_256] :
      ( r1_tarski(A_255,k3_xboole_0(A_256,A_255))
      | ~ r1_tarski(A_255,A_256)
      | ~ r1_tarski(A_255,A_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3609,c_6734])).

tff(c_496,plain,(
    ! [A_104,A_23] :
      ( k3_xboole_0(A_104,k3_xboole_0(k1_relat_1(k6_relat_1(A_104)),A_23)) = k9_relat_1(k6_relat_1(A_104),A_23)
      | ~ v1_relat_1(k6_relat_1(A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_18])).

tff(c_705,plain,(
    ! [A_119,A_120] : k3_xboole_0(A_119,k3_xboole_0(A_119,A_120)) = k3_xboole_0(A_119,A_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_478,c_28,c_496])).

tff(c_745,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,k3_xboole_0(A_61,B_60)) = k3_xboole_0(B_60,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_705])).

tff(c_6618,plain,(
    ! [A_85,A_86] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_85)),k1_relat_1(k7_relat_1(k6_relat_1(A_85),A_86)))
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_6531])).

tff(c_6648,plain,(
    ! [A_230,A_231] :
      ( r1_tarski(A_230,k1_relat_1(k7_relat_1(k6_relat_1(A_230),A_231)))
      | ~ r1_tarski(A_230,A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6618])).

tff(c_8042,plain,(
    ! [A_243,A_244] :
      ( r1_tarski(A_243,k3_xboole_0(A_243,A_244))
      | ~ r1_tarski(A_243,A_244)
      | ~ r1_tarski(A_244,A_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3609,c_6648])).

tff(c_8110,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,k3_xboole_0(B_60,A_61))
      | ~ r1_tarski(B_60,k3_xboole_0(A_61,B_60))
      | ~ r1_tarski(k3_xboole_0(A_61,B_60),B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_8042])).

tff(c_8169,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,k3_xboole_0(B_60,A_61))
      | ~ r1_tarski(B_60,k3_xboole_0(A_61,B_60)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_8110])).

tff(c_9079,plain,(
    ! [A_257,A_258] :
      ( r1_tarski(A_257,k3_xboole_0(A_257,A_258))
      | ~ r1_tarski(A_257,A_258) ) ),
    inference(resolution,[status(thm)],[c_8935,c_8169])).

tff(c_894,plain,(
    ! [A_124,B_125] : k3_xboole_0(A_124,k3_xboole_0(B_125,A_124)) = k3_xboole_0(B_125,A_124) ),
    inference(resolution,[status(thm)],[c_167,c_648])).

tff(c_945,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,k3_xboole_0(B_60,A_61)) = k3_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_894])).

tff(c_8113,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,k3_xboole_0(A_61,B_60))
      | ~ r1_tarski(B_60,k3_xboole_0(B_60,A_61))
      | ~ r1_tarski(k3_xboole_0(B_60,A_61),B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_8042])).

tff(c_8171,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,k3_xboole_0(A_61,B_60))
      | ~ r1_tarski(B_60,k3_xboole_0(B_60,A_61)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8113])).

tff(c_9174,plain,(
    ! [A_257,A_258] :
      ( r1_tarski(A_257,k3_xboole_0(A_258,A_257))
      | ~ r1_tarski(A_257,A_258) ) ),
    inference(resolution,[status(thm)],[c_9079,c_8171])).

tff(c_35416,plain,(
    ! [A_464,A_465] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_464),A_465)),k2_relat_1(k7_relat_1(k6_relat_1(A_464),A_465)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_464),A_465)),A_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35213,c_9174])).

tff(c_55246,plain,(
    ! [A_562,A_563] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_562),A_563)),k2_relat_1(k7_relat_1(k6_relat_1(A_562),A_563))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_35416])).

tff(c_55499,plain,(
    ! [A_562,A_26] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_562),A_26)),k9_relat_1(k6_relat_1(A_562),A_26))
      | ~ v1_relat_1(k6_relat_1(A_562)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_55246])).

tff(c_55573,plain,(
    ! [A_564,A_565] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_564),A_565)),k3_xboole_0(A_564,A_565)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_478,c_55499])).

tff(c_2912,plain,(
    ! [A_167,B_168] :
      ( k3_xboole_0(A_167,k1_relat_1(k7_relat_1(B_168,A_167))) = k1_relat_1(k7_relat_1(B_168,A_167))
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_34,c_648])).

tff(c_3000,plain,(
    ! [A_85,A_86] :
      ( k3_xboole_0(A_85,k1_relat_1(k6_relat_1(A_85))) = k1_relat_1(k7_relat_1(k6_relat_1(A_86),A_85))
      | ~ v1_relat_1(k6_relat_1(A_86))
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_2912])).

tff(c_3031,plain,(
    ! [A_169,A_170] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_169),A_170)) = A_170
      | ~ r1_tarski(A_170,A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_500,c_28,c_3000])).

tff(c_3097,plain,(
    ! [A_85,A_86] :
      ( k1_relat_1(k6_relat_1(A_85)) = A_86
      | ~ r1_tarski(A_86,A_85)
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_3031])).

tff(c_3147,plain,(
    ! [A_86,A_85] :
      ( A_86 = A_85
      | ~ r1_tarski(A_86,A_85)
      | ~ r1_tarski(A_85,A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3097])).

tff(c_55579,plain,(
    ! [A_564,A_565] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_564),A_565)) = k3_xboole_0(A_564,A_565)
      | ~ r1_tarski(k3_xboole_0(A_564,A_565),k1_relat_1(k7_relat_1(k6_relat_1(A_564),A_565))) ) ),
    inference(resolution,[status(thm)],[c_55573,c_3147])).

tff(c_55904,plain,(
    ! [A_566,A_567] : k1_relat_1(k7_relat_1(k6_relat_1(A_566),A_567)) = k3_xboole_0(A_566,A_567) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36295,c_55579])).

tff(c_643,plain,(
    ! [A_36,B_114] :
      ( k7_relat_1(k6_relat_1(A_36),k1_relat_1(k7_relat_1(B_114,A_36))) = k7_relat_1(k6_relat_1(A_36),k1_relat_1(B_114))
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_631])).

tff(c_56321,plain,(
    ! [A_567,A_566] :
      ( k7_relat_1(k6_relat_1(A_567),k3_xboole_0(A_566,A_567)) = k7_relat_1(k6_relat_1(A_567),k1_relat_1(k6_relat_1(A_566)))
      | ~ v1_relat_1(k6_relat_1(A_566)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55904,c_643])).

tff(c_57807,plain,(
    ! [A_576,A_577] : k7_relat_1(k6_relat_1(A_576),k3_xboole_0(A_577,A_576)) = k7_relat_1(k6_relat_1(A_576),A_577) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_56321])).

tff(c_57899,plain,(
    ! [A_576,A_577] :
      ( k7_relat_1(k6_relat_1(A_576),A_577) = k6_relat_1(k3_xboole_0(A_577,A_576))
      | ~ r1_tarski(k3_xboole_0(A_577,A_576),A_576) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57807,c_312])).

tff(c_58087,plain,(
    ! [A_576,A_577] : k7_relat_1(k6_relat_1(A_576),A_577) = k6_relat_1(k3_xboole_0(A_577,A_576)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_57899])).

tff(c_598,plain,(
    ! [B_114,A_86] :
      ( k6_relat_1(k1_relat_1(k7_relat_1(B_114,k1_relat_1(k6_relat_1(A_86))))) = k7_relat_1(k6_relat_1(A_86),k1_relat_1(B_114))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_114,k1_relat_1(k6_relat_1(A_86)))),A_86)
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(k6_relat_1(A_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_312])).

tff(c_634,plain,(
    ! [A_86,B_114] :
      ( k7_relat_1(k6_relat_1(A_86),k1_relat_1(B_114)) = k6_relat_1(k1_relat_1(k7_relat_1(B_114,A_86)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_114,A_86)),A_86)
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_28,c_598])).

tff(c_79280,plain,(
    ! [B_719,A_720] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(B_719),A_720)) = k6_relat_1(k1_relat_1(k7_relat_1(B_719,A_720)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_719,A_720)),A_720)
      | ~ v1_relat_1(B_719) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58087,c_634])).

tff(c_84644,plain,(
    ! [B_769,A_770] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(B_769),A_770)) = k6_relat_1(k1_relat_1(k7_relat_1(B_769,A_770)))
      | ~ v1_relat_1(B_769) ) ),
    inference(resolution,[status(thm)],[c_34,c_79280])).

tff(c_2047,plain,(
    ! [A_152,A_153] :
      ( k7_relat_1(k6_relat_1(A_152),A_153) = k6_relat_1(A_152)
      | ~ r1_tarski(A_152,A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_793,c_28,c_28,c_1009])).

tff(c_4097,plain,(
    ! [A_196,A_195] :
      ( k6_relat_1(A_196) = k6_relat_1(A_195)
      | ~ r1_tarski(A_195,A_196)
      | ~ r1_tarski(A_196,A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_2047])).

tff(c_4103,plain,(
    ! [B_60,A_61] :
      ( k6_relat_1(k3_xboole_0(B_60,A_61)) = k6_relat_1(k3_xboole_0(A_61,B_60))
      | ~ r1_tarski(k3_xboole_0(B_60,A_61),k3_xboole_0(A_61,B_60)) ) ),
    inference(resolution,[status(thm)],[c_373,c_4097])).

tff(c_4127,plain,(
    ! [B_197,A_198] : k6_relat_1(k3_xboole_0(B_197,A_198)) = k6_relat_1(k3_xboole_0(A_198,B_197)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_4103])).

tff(c_4254,plain,(
    ! [B_197,A_198] : k2_relat_1(k6_relat_1(k3_xboole_0(B_197,A_198))) = k3_xboole_0(A_198,B_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_4127,c_30])).

tff(c_84738,plain,(
    ! [B_769,A_770] :
      ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(B_769,A_770)))) = k3_xboole_0(A_770,k1_relat_1(B_769))
      | ~ v1_relat_1(B_769) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84644,c_4254])).

tff(c_100086,plain,(
    ! [A_896,B_897] :
      ( k3_xboole_0(A_896,k1_relat_1(B_897)) = k1_relat_1(k7_relat_1(B_897,A_896))
      | ~ v1_relat_1(B_897) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_84738])).

tff(c_251,plain,(
    ! [A_79,B_80] :
      ( k5_relat_1(k6_relat_1(A_79),B_80) = k7_relat_1(B_80,A_79)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_151,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) != k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_44])).

tff(c_257,plain,
    ( k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_151])).

tff(c_263,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_257])).

tff(c_100862,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100086,c_263])).

tff(c_101005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_100862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.91/19.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.91/19.66  
% 29.91/19.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.91/19.66  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 29.91/19.66  
% 29.91/19.66  %Foreground sorts:
% 29.91/19.66  
% 29.91/19.66  
% 29.91/19.66  %Background operators:
% 29.91/19.66  
% 29.91/19.66  
% 29.91/19.66  %Foreground operators:
% 29.91/19.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 29.91/19.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.91/19.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 29.91/19.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 29.91/19.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 29.91/19.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.91/19.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 29.91/19.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.91/19.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 29.91/19.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 29.91/19.66  tff('#skF_2', type, '#skF_2': $i).
% 29.91/19.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 29.91/19.66  tff('#skF_1', type, '#skF_1': $i).
% 29.91/19.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 29.91/19.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.91/19.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.91/19.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 29.91/19.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.91/19.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.91/19.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.91/19.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 29.91/19.66  
% 30.03/19.69  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_1)).
% 30.03/19.69  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 30.03/19.69  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 30.03/19.69  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 30.03/19.69  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 30.03/19.69  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 30.03/19.69  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 30.03/19.69  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 30.03/19.69  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 30.03/19.69  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 30.03/19.69  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 30.03/19.69  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 30.03/19.69  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 30.03/19.69  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 30.03/19.69  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 30.03/19.69  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 30.03/19.69  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 30.03/19.69  tff(c_30, plain, (![A_36]: (k2_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_73])).
% 30.03/19.69  tff(c_34, plain, (![B_40, A_39]: (r1_tarski(k1_relat_1(k7_relat_1(B_40, A_39)), A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_83])).
% 30.03/19.69  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 30.03/19.69  tff(c_113, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.03/19.69  tff(c_128, plain, (![B_60, A_61]: (k1_setfam_1(k2_tarski(B_60, A_61))=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_4, c_113])).
% 30.03/19.69  tff(c_14, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.03/19.69  tff(c_152, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_128, c_14])).
% 30.03/19.69  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 30.03/19.69  tff(c_167, plain, (![B_62, A_63]: (r1_tarski(k3_xboole_0(B_62, A_63), A_63))), inference(superposition, [status(thm), theory('equality')], [c_152, c_2])).
% 30.03/19.69  tff(c_40, plain, (![A_45]: (v1_relat_1(k6_relat_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 30.03/19.69  tff(c_28, plain, (![A_36]: (k1_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_73])).
% 30.03/19.69  tff(c_265, plain, (![B_81, A_82]: (k5_relat_1(B_81, k6_relat_1(A_82))=B_81 | ~r1_tarski(k2_relat_1(B_81), A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_79])).
% 30.03/19.69  tff(c_271, plain, (![A_36, A_82]: (k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_82))=k6_relat_1(A_36) | ~r1_tarski(A_36, A_82) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_265])).
% 30.03/19.69  tff(c_296, plain, (![A_85, A_86]: (k5_relat_1(k6_relat_1(A_85), k6_relat_1(A_86))=k6_relat_1(A_85) | ~r1_tarski(A_85, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_271])).
% 30.03/19.69  tff(c_38, plain, (![A_43, B_44]: (k5_relat_1(k6_relat_1(A_43), B_44)=k7_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_91])).
% 30.03/19.69  tff(c_302, plain, (![A_86, A_85]: (k7_relat_1(k6_relat_1(A_86), A_85)=k6_relat_1(A_85) | ~v1_relat_1(k6_relat_1(A_86)) | ~r1_tarski(A_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_296, c_38])).
% 30.03/19.69  tff(c_316, plain, (![A_87, A_88]: (k7_relat_1(k6_relat_1(A_87), A_88)=k6_relat_1(A_88) | ~r1_tarski(A_88, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_302])).
% 30.03/19.69  tff(c_22, plain, (![B_27, A_26]: (k2_relat_1(k7_relat_1(B_27, A_26))=k9_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 30.03/19.69  tff(c_322, plain, (![A_87, A_88]: (k9_relat_1(k6_relat_1(A_87), A_88)=k2_relat_1(k6_relat_1(A_88)) | ~v1_relat_1(k6_relat_1(A_87)) | ~r1_tarski(A_88, A_87))), inference(superposition, [status(thm), theory('equality')], [c_316, c_22])).
% 30.03/19.69  tff(c_446, plain, (![A_102, A_103]: (k9_relat_1(k6_relat_1(A_102), A_103)=A_103 | ~r1_tarski(A_103, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_322])).
% 30.03/19.69  tff(c_18, plain, (![B_24, A_23]: (k9_relat_1(B_24, k3_xboole_0(k1_relat_1(B_24), A_23))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 30.03/19.69  tff(c_453, plain, (![A_102, A_23]: (k3_xboole_0(k1_relat_1(k6_relat_1(A_102)), A_23)=k9_relat_1(k6_relat_1(A_102), A_23) | ~v1_relat_1(k6_relat_1(A_102)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_102)), A_23), A_102))), inference(superposition, [status(thm), theory('equality')], [c_446, c_18])).
% 30.03/19.69  tff(c_478, plain, (![A_102, A_23]: (k9_relat_1(k6_relat_1(A_102), A_23)=k3_xboole_0(A_102, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28, c_40, c_28, c_453])).
% 30.03/19.69  tff(c_585, plain, (![A_113, B_114]: (k7_relat_1(A_113, k1_relat_1(k7_relat_1(B_114, k1_relat_1(A_113))))=k7_relat_1(A_113, k1_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_69])).
% 30.03/19.69  tff(c_631, plain, (![A_36, B_114]: (k7_relat_1(k6_relat_1(A_36), k1_relat_1(k7_relat_1(B_114, A_36)))=k7_relat_1(k6_relat_1(A_36), k1_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_585])).
% 30.03/19.69  tff(c_964, plain, (![A_126, B_127]: (k7_relat_1(k6_relat_1(A_126), k1_relat_1(k7_relat_1(B_127, A_126)))=k7_relat_1(k6_relat_1(A_126), k1_relat_1(B_127)) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_631])).
% 30.03/19.69  tff(c_16, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.03/19.69  tff(c_994, plain, (![A_126, B_127]: (v1_relat_1(k7_relat_1(k6_relat_1(A_126), k1_relat_1(B_127))) | ~v1_relat_1(k6_relat_1(A_126)) | ~v1_relat_1(B_127))), inference(superposition, [status(thm), theory('equality')], [c_964, c_16])).
% 30.03/19.69  tff(c_1037, plain, (![A_128, B_129]: (v1_relat_1(k7_relat_1(k6_relat_1(A_128), k1_relat_1(B_129))) | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_994])).
% 30.03/19.69  tff(c_1055, plain, (![A_128, A_36]: (v1_relat_1(k7_relat_1(k6_relat_1(A_128), A_36)) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1037])).
% 30.03/19.69  tff(c_1061, plain, (![A_128, A_36]: (v1_relat_1(k7_relat_1(k6_relat_1(A_128), A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1055])).
% 30.03/19.69  tff(c_415, plain, (![A_99, C_100, B_101]: (k9_relat_1(k7_relat_1(A_99, C_100), B_101)=k9_relat_1(A_99, B_101) | ~r1_tarski(B_101, C_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_62])).
% 30.03/19.69  tff(c_20, plain, (![A_25]: (k9_relat_1(A_25, k1_relat_1(A_25))=k2_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.03/19.69  tff(c_2877, plain, (![A_165, C_166]: (k9_relat_1(A_165, k1_relat_1(k7_relat_1(A_165, C_166)))=k2_relat_1(k7_relat_1(A_165, C_166)) | ~v1_relat_1(k7_relat_1(A_165, C_166)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_165, C_166)), C_166) | ~v1_relat_1(A_165))), inference(superposition, [status(thm), theory('equality')], [c_415, c_20])).
% 30.03/19.69  tff(c_9219, plain, (![B_259, A_260]: (k9_relat_1(B_259, k1_relat_1(k7_relat_1(B_259, A_260)))=k2_relat_1(k7_relat_1(B_259, A_260)) | ~v1_relat_1(k7_relat_1(B_259, A_260)) | ~v1_relat_1(B_259))), inference(resolution, [status(thm)], [c_34, c_2877])).
% 30.03/19.69  tff(c_9287, plain, (![A_102, A_260]: (k3_xboole_0(A_102, k1_relat_1(k7_relat_1(k6_relat_1(A_102), A_260)))=k2_relat_1(k7_relat_1(k6_relat_1(A_102), A_260)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_102), A_260)) | ~v1_relat_1(k6_relat_1(A_102)))), inference(superposition, [status(thm), theory('equality')], [c_478, c_9219])).
% 30.03/19.69  tff(c_35213, plain, (![A_464, A_465]: (k3_xboole_0(A_464, k1_relat_1(k7_relat_1(k6_relat_1(A_464), A_465)))=k2_relat_1(k7_relat_1(k6_relat_1(A_464), A_465)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1061, c_9287])).
% 30.03/19.69  tff(c_35990, plain, (![A_468, A_469]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_468), A_469)), k1_relat_1(k7_relat_1(k6_relat_1(A_468), A_469))))), inference(superposition, [status(thm), theory('equality')], [c_35213, c_167])).
% 30.03/19.69  tff(c_36229, plain, (![A_468, A_26]: (r1_tarski(k9_relat_1(k6_relat_1(A_468), A_26), k1_relat_1(k7_relat_1(k6_relat_1(A_468), A_26))) | ~v1_relat_1(k6_relat_1(A_468)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_35990])).
% 30.03/19.69  tff(c_36295, plain, (![A_468, A_26]: (r1_tarski(k3_xboole_0(A_468, A_26), k1_relat_1(k7_relat_1(k6_relat_1(A_468), A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_478, c_36229])).
% 30.03/19.69  tff(c_226, plain, (![B_70, A_71]: (r1_tarski(k1_relat_1(k7_relat_1(B_70, A_71)), k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_87])).
% 30.03/19.69  tff(c_229, plain, (![A_36, A_71]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_36), A_71)), A_36) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_226])).
% 30.03/19.69  tff(c_231, plain, (![A_36, A_71]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_36), A_71)), A_36))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_229])).
% 30.03/19.69  tff(c_312, plain, (![A_86, A_85]: (k7_relat_1(k6_relat_1(A_86), A_85)=k6_relat_1(A_85) | ~r1_tarski(A_85, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_302])).
% 30.03/19.69  tff(c_36, plain, (![B_42, A_41]: (r1_tarski(k1_relat_1(k7_relat_1(B_42, A_41)), k1_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_87])).
% 30.03/19.69  tff(c_340, plain, (![A_87, A_88]: (k9_relat_1(k6_relat_1(A_87), A_88)=A_88 | ~r1_tarski(A_88, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_322])).
% 30.03/19.69  tff(c_648, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=A_116 | ~r1_tarski(A_116, A_115))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_340])).
% 30.03/19.69  tff(c_3452, plain, (![B_181, A_182]: (k3_xboole_0(k1_relat_1(B_181), k1_relat_1(k7_relat_1(B_181, A_182)))=k1_relat_1(k7_relat_1(B_181, A_182)) | ~v1_relat_1(B_181))), inference(resolution, [status(thm)], [c_36, c_648])).
% 30.03/19.69  tff(c_3565, plain, (![A_86, A_85]: (k3_xboole_0(k1_relat_1(k6_relat_1(A_86)), k1_relat_1(k6_relat_1(A_85)))=k1_relat_1(k7_relat_1(k6_relat_1(A_86), A_85)) | ~v1_relat_1(k6_relat_1(A_86)) | ~r1_tarski(A_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_312, c_3452])).
% 30.03/19.69  tff(c_3609, plain, (![A_86, A_85]: (k1_relat_1(k7_relat_1(k6_relat_1(A_86), A_85))=k3_xboole_0(A_86, A_85) | ~r1_tarski(A_85, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_28, c_3565])).
% 30.03/19.69  tff(c_489, plain, (![A_104, A_105]: (k9_relat_1(k6_relat_1(A_104), A_105)=k3_xboole_0(A_104, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28, c_40, c_28, c_453])).
% 30.03/19.69  tff(c_200, plain, (![A_66]: (k9_relat_1(A_66, k1_relat_1(A_66))=k2_relat_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 30.03/19.69  tff(c_209, plain, (![A_36]: (k9_relat_1(k6_relat_1(A_36), A_36)=k2_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_200])).
% 30.03/19.69  tff(c_213, plain, (![A_36]: (k9_relat_1(k6_relat_1(A_36), A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_209])).
% 30.03/19.69  tff(c_500, plain, (![A_105]: (k3_xboole_0(A_105, A_105)=A_105)), inference(superposition, [status(thm), theory('equality')], [c_489, c_213])).
% 30.03/19.69  tff(c_529, plain, (![A_106]: (k3_xboole_0(A_106, A_106)=A_106)), inference(superposition, [status(thm), theory('equality')], [c_489, c_213])).
% 30.03/19.69  tff(c_134, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_128, c_14])).
% 30.03/19.69  tff(c_331, plain, (![A_88, A_87]: (r1_tarski(k1_relat_1(k6_relat_1(A_88)), A_88) | ~v1_relat_1(k6_relat_1(A_87)) | ~r1_tarski(A_88, A_87))), inference(superposition, [status(thm), theory('equality')], [c_316, c_34])).
% 30.03/19.69  tff(c_349, plain, (![A_89, A_90]: (r1_tarski(A_89, A_89) | ~r1_tarski(A_89, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_331])).
% 30.03/19.69  tff(c_365, plain, (![B_91, A_92]: (r1_tarski(k3_xboole_0(B_91, A_92), k3_xboole_0(B_91, A_92)))), inference(resolution, [status(thm)], [c_167, c_349])).
% 30.03/19.69  tff(c_373, plain, (![A_61, B_60]: (r1_tarski(k3_xboole_0(A_61, B_60), k3_xboole_0(B_60, A_61)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_365])).
% 30.03/19.69  tff(c_535, plain, (![A_106]: (r1_tarski(A_106, k3_xboole_0(A_106, A_106)))), inference(superposition, [status(thm), theory('equality')], [c_529, c_373])).
% 30.03/19.69  tff(c_567, plain, (![A_107]: (r1_tarski(A_107, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_500, c_535])).
% 30.03/19.69  tff(c_32, plain, (![B_38, A_37]: (k5_relat_1(B_38, k6_relat_1(A_37))=B_38 | ~r1_tarski(k2_relat_1(B_38), A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_79])).
% 30.03/19.69  tff(c_759, plain, (![B_121]: (k5_relat_1(B_121, k6_relat_1(k2_relat_1(B_121)))=B_121 | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_567, c_32])).
% 30.03/19.69  tff(c_770, plain, (![A_43]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_43))), A_43)=k6_relat_1(A_43) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_43)))) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_759, c_38])).
% 30.03/19.69  tff(c_793, plain, (![A_43]: (k7_relat_1(k6_relat_1(A_43), A_43)=k6_relat_1(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_30, c_770])).
% 30.03/19.69  tff(c_1009, plain, (![A_85, A_86]: (k7_relat_1(k6_relat_1(A_85), k1_relat_1(k6_relat_1(A_86)))=k7_relat_1(k6_relat_1(A_85), k1_relat_1(k6_relat_1(A_85))) | ~v1_relat_1(k6_relat_1(A_86)) | ~r1_tarski(A_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_312, c_964])).
% 30.03/19.69  tff(c_1036, plain, (![A_85, A_86]: (k7_relat_1(k6_relat_1(A_85), A_86)=k6_relat_1(A_85) | ~r1_tarski(A_85, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_793, c_28, c_28, c_1009])).
% 30.03/19.69  tff(c_1440, plain, (![A_140, B_141]: (r1_tarski(k1_relat_1(k7_relat_1(A_140, k1_relat_1(B_141))), k1_relat_1(k7_relat_1(B_141, k1_relat_1(A_140)))) | ~v1_relat_1(A_140) | ~v1_relat_1(B_141) | ~v1_relat_1(A_140))), inference(superposition, [status(thm), theory('equality')], [c_585, c_34])).
% 30.03/19.69  tff(c_1477, plain, (![A_36, B_141]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_36), k1_relat_1(B_141))), k1_relat_1(k7_relat_1(B_141, A_36))) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(B_141) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1440])).
% 30.03/19.69  tff(c_6300, plain, (![A_224, B_225]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_224), k1_relat_1(B_225))), k1_relat_1(k7_relat_1(B_225, A_224))) | ~v1_relat_1(B_225))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_1477])).
% 30.03/19.69  tff(c_6413, plain, (![A_224, A_36]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_224), A_36)), k1_relat_1(k7_relat_1(k6_relat_1(A_36), A_224))) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6300])).
% 30.03/19.69  tff(c_6531, plain, (![A_228, A_229]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_228), A_229)), k1_relat_1(k7_relat_1(k6_relat_1(A_229), A_228))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6413])).
% 30.03/19.69  tff(c_6592, plain, (![A_85, A_86]: (r1_tarski(k1_relat_1(k6_relat_1(A_85)), k1_relat_1(k7_relat_1(k6_relat_1(A_86), A_85))) | ~r1_tarski(A_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_1036, c_6531])).
% 30.03/19.69  tff(c_6734, plain, (![A_232, A_233]: (r1_tarski(A_232, k1_relat_1(k7_relat_1(k6_relat_1(A_233), A_232))) | ~r1_tarski(A_232, A_233))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6592])).
% 30.03/19.69  tff(c_8935, plain, (![A_255, A_256]: (r1_tarski(A_255, k3_xboole_0(A_256, A_255)) | ~r1_tarski(A_255, A_256) | ~r1_tarski(A_255, A_256))), inference(superposition, [status(thm), theory('equality')], [c_3609, c_6734])).
% 30.03/19.69  tff(c_496, plain, (![A_104, A_23]: (k3_xboole_0(A_104, k3_xboole_0(k1_relat_1(k6_relat_1(A_104)), A_23))=k9_relat_1(k6_relat_1(A_104), A_23) | ~v1_relat_1(k6_relat_1(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_489, c_18])).
% 30.03/19.69  tff(c_705, plain, (![A_119, A_120]: (k3_xboole_0(A_119, k3_xboole_0(A_119, A_120))=k3_xboole_0(A_119, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_478, c_28, c_496])).
% 30.03/19.69  tff(c_745, plain, (![B_60, A_61]: (k3_xboole_0(B_60, k3_xboole_0(A_61, B_60))=k3_xboole_0(B_60, A_61))), inference(superposition, [status(thm), theory('equality')], [c_134, c_705])).
% 30.03/19.69  tff(c_6618, plain, (![A_85, A_86]: (r1_tarski(k1_relat_1(k6_relat_1(A_85)), k1_relat_1(k7_relat_1(k6_relat_1(A_85), A_86))) | ~r1_tarski(A_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_312, c_6531])).
% 30.03/19.69  tff(c_6648, plain, (![A_230, A_231]: (r1_tarski(A_230, k1_relat_1(k7_relat_1(k6_relat_1(A_230), A_231))) | ~r1_tarski(A_230, A_231))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6618])).
% 30.03/19.69  tff(c_8042, plain, (![A_243, A_244]: (r1_tarski(A_243, k3_xboole_0(A_243, A_244)) | ~r1_tarski(A_243, A_244) | ~r1_tarski(A_244, A_243))), inference(superposition, [status(thm), theory('equality')], [c_3609, c_6648])).
% 30.03/19.69  tff(c_8110, plain, (![B_60, A_61]: (r1_tarski(B_60, k3_xboole_0(B_60, A_61)) | ~r1_tarski(B_60, k3_xboole_0(A_61, B_60)) | ~r1_tarski(k3_xboole_0(A_61, B_60), B_60))), inference(superposition, [status(thm), theory('equality')], [c_745, c_8042])).
% 30.03/19.69  tff(c_8169, plain, (![B_60, A_61]: (r1_tarski(B_60, k3_xboole_0(B_60, A_61)) | ~r1_tarski(B_60, k3_xboole_0(A_61, B_60)))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_8110])).
% 30.03/19.69  tff(c_9079, plain, (![A_257, A_258]: (r1_tarski(A_257, k3_xboole_0(A_257, A_258)) | ~r1_tarski(A_257, A_258))), inference(resolution, [status(thm)], [c_8935, c_8169])).
% 30.03/19.69  tff(c_894, plain, (![A_124, B_125]: (k3_xboole_0(A_124, k3_xboole_0(B_125, A_124))=k3_xboole_0(B_125, A_124))), inference(resolution, [status(thm)], [c_167, c_648])).
% 30.03/19.69  tff(c_945, plain, (![B_60, A_61]: (k3_xboole_0(B_60, k3_xboole_0(B_60, A_61))=k3_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_134, c_894])).
% 30.03/19.69  tff(c_8113, plain, (![B_60, A_61]: (r1_tarski(B_60, k3_xboole_0(A_61, B_60)) | ~r1_tarski(B_60, k3_xboole_0(B_60, A_61)) | ~r1_tarski(k3_xboole_0(B_60, A_61), B_60))), inference(superposition, [status(thm), theory('equality')], [c_945, c_8042])).
% 30.03/19.69  tff(c_8171, plain, (![B_60, A_61]: (r1_tarski(B_60, k3_xboole_0(A_61, B_60)) | ~r1_tarski(B_60, k3_xboole_0(B_60, A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8113])).
% 30.03/19.69  tff(c_9174, plain, (![A_257, A_258]: (r1_tarski(A_257, k3_xboole_0(A_258, A_257)) | ~r1_tarski(A_257, A_258))), inference(resolution, [status(thm)], [c_9079, c_8171])).
% 30.03/19.69  tff(c_35416, plain, (![A_464, A_465]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_464), A_465)), k2_relat_1(k7_relat_1(k6_relat_1(A_464), A_465))) | ~r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_464), A_465)), A_464))), inference(superposition, [status(thm), theory('equality')], [c_35213, c_9174])).
% 30.03/19.69  tff(c_55246, plain, (![A_562, A_563]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_562), A_563)), k2_relat_1(k7_relat_1(k6_relat_1(A_562), A_563))))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_35416])).
% 30.03/19.69  tff(c_55499, plain, (![A_562, A_26]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_562), A_26)), k9_relat_1(k6_relat_1(A_562), A_26)) | ~v1_relat_1(k6_relat_1(A_562)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_55246])).
% 30.03/19.69  tff(c_55573, plain, (![A_564, A_565]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_564), A_565)), k3_xboole_0(A_564, A_565)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_478, c_55499])).
% 30.03/19.69  tff(c_2912, plain, (![A_167, B_168]: (k3_xboole_0(A_167, k1_relat_1(k7_relat_1(B_168, A_167)))=k1_relat_1(k7_relat_1(B_168, A_167)) | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_34, c_648])).
% 30.03/19.69  tff(c_3000, plain, (![A_85, A_86]: (k3_xboole_0(A_85, k1_relat_1(k6_relat_1(A_85)))=k1_relat_1(k7_relat_1(k6_relat_1(A_86), A_85)) | ~v1_relat_1(k6_relat_1(A_86)) | ~r1_tarski(A_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_312, c_2912])).
% 30.03/19.69  tff(c_3031, plain, (![A_169, A_170]: (k1_relat_1(k7_relat_1(k6_relat_1(A_169), A_170))=A_170 | ~r1_tarski(A_170, A_169))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_500, c_28, c_3000])).
% 30.03/19.69  tff(c_3097, plain, (![A_85, A_86]: (k1_relat_1(k6_relat_1(A_85))=A_86 | ~r1_tarski(A_86, A_85) | ~r1_tarski(A_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_1036, c_3031])).
% 30.03/19.69  tff(c_3147, plain, (![A_86, A_85]: (A_86=A_85 | ~r1_tarski(A_86, A_85) | ~r1_tarski(A_85, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3097])).
% 30.03/19.69  tff(c_55579, plain, (![A_564, A_565]: (k1_relat_1(k7_relat_1(k6_relat_1(A_564), A_565))=k3_xboole_0(A_564, A_565) | ~r1_tarski(k3_xboole_0(A_564, A_565), k1_relat_1(k7_relat_1(k6_relat_1(A_564), A_565))))), inference(resolution, [status(thm)], [c_55573, c_3147])).
% 30.03/19.69  tff(c_55904, plain, (![A_566, A_567]: (k1_relat_1(k7_relat_1(k6_relat_1(A_566), A_567))=k3_xboole_0(A_566, A_567))), inference(demodulation, [status(thm), theory('equality')], [c_36295, c_55579])).
% 30.03/19.69  tff(c_643, plain, (![A_36, B_114]: (k7_relat_1(k6_relat_1(A_36), k1_relat_1(k7_relat_1(B_114, A_36)))=k7_relat_1(k6_relat_1(A_36), k1_relat_1(B_114)) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_631])).
% 30.03/19.69  tff(c_56321, plain, (![A_567, A_566]: (k7_relat_1(k6_relat_1(A_567), k3_xboole_0(A_566, A_567))=k7_relat_1(k6_relat_1(A_567), k1_relat_1(k6_relat_1(A_566))) | ~v1_relat_1(k6_relat_1(A_566)))), inference(superposition, [status(thm), theory('equality')], [c_55904, c_643])).
% 30.03/19.69  tff(c_57807, plain, (![A_576, A_577]: (k7_relat_1(k6_relat_1(A_576), k3_xboole_0(A_577, A_576))=k7_relat_1(k6_relat_1(A_576), A_577))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_56321])).
% 30.03/19.69  tff(c_57899, plain, (![A_576, A_577]: (k7_relat_1(k6_relat_1(A_576), A_577)=k6_relat_1(k3_xboole_0(A_577, A_576)) | ~r1_tarski(k3_xboole_0(A_577, A_576), A_576))), inference(superposition, [status(thm), theory('equality')], [c_57807, c_312])).
% 30.03/19.69  tff(c_58087, plain, (![A_576, A_577]: (k7_relat_1(k6_relat_1(A_576), A_577)=k6_relat_1(k3_xboole_0(A_577, A_576)))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_57899])).
% 30.03/19.69  tff(c_598, plain, (![B_114, A_86]: (k6_relat_1(k1_relat_1(k7_relat_1(B_114, k1_relat_1(k6_relat_1(A_86)))))=k7_relat_1(k6_relat_1(A_86), k1_relat_1(B_114)) | ~r1_tarski(k1_relat_1(k7_relat_1(B_114, k1_relat_1(k6_relat_1(A_86)))), A_86) | ~v1_relat_1(B_114) | ~v1_relat_1(k6_relat_1(A_86)))), inference(superposition, [status(thm), theory('equality')], [c_585, c_312])).
% 30.03/19.69  tff(c_634, plain, (![A_86, B_114]: (k7_relat_1(k6_relat_1(A_86), k1_relat_1(B_114))=k6_relat_1(k1_relat_1(k7_relat_1(B_114, A_86))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_114, A_86)), A_86) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_28, c_598])).
% 30.03/19.69  tff(c_79280, plain, (![B_719, A_720]: (k6_relat_1(k3_xboole_0(k1_relat_1(B_719), A_720))=k6_relat_1(k1_relat_1(k7_relat_1(B_719, A_720))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_719, A_720)), A_720) | ~v1_relat_1(B_719))), inference(demodulation, [status(thm), theory('equality')], [c_58087, c_634])).
% 30.03/19.69  tff(c_84644, plain, (![B_769, A_770]: (k6_relat_1(k3_xboole_0(k1_relat_1(B_769), A_770))=k6_relat_1(k1_relat_1(k7_relat_1(B_769, A_770))) | ~v1_relat_1(B_769))), inference(resolution, [status(thm)], [c_34, c_79280])).
% 30.03/19.69  tff(c_2047, plain, (![A_152, A_153]: (k7_relat_1(k6_relat_1(A_152), A_153)=k6_relat_1(A_152) | ~r1_tarski(A_152, A_153))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_793, c_28, c_28, c_1009])).
% 30.03/19.69  tff(c_4097, plain, (![A_196, A_195]: (k6_relat_1(A_196)=k6_relat_1(A_195) | ~r1_tarski(A_195, A_196) | ~r1_tarski(A_196, A_195))), inference(superposition, [status(thm), theory('equality')], [c_312, c_2047])).
% 30.03/19.69  tff(c_4103, plain, (![B_60, A_61]: (k6_relat_1(k3_xboole_0(B_60, A_61))=k6_relat_1(k3_xboole_0(A_61, B_60)) | ~r1_tarski(k3_xboole_0(B_60, A_61), k3_xboole_0(A_61, B_60)))), inference(resolution, [status(thm)], [c_373, c_4097])).
% 30.03/19.69  tff(c_4127, plain, (![B_197, A_198]: (k6_relat_1(k3_xboole_0(B_197, A_198))=k6_relat_1(k3_xboole_0(A_198, B_197)))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_4103])).
% 30.03/19.69  tff(c_4254, plain, (![B_197, A_198]: (k2_relat_1(k6_relat_1(k3_xboole_0(B_197, A_198)))=k3_xboole_0(A_198, B_197))), inference(superposition, [status(thm), theory('equality')], [c_4127, c_30])).
% 30.03/19.69  tff(c_84738, plain, (![B_769, A_770]: (k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(B_769, A_770))))=k3_xboole_0(A_770, k1_relat_1(B_769)) | ~v1_relat_1(B_769))), inference(superposition, [status(thm), theory('equality')], [c_84644, c_4254])).
% 30.03/19.69  tff(c_100086, plain, (![A_896, B_897]: (k3_xboole_0(A_896, k1_relat_1(B_897))=k1_relat_1(k7_relat_1(B_897, A_896)) | ~v1_relat_1(B_897))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_84738])).
% 30.03/19.69  tff(c_251, plain, (![A_79, B_80]: (k5_relat_1(k6_relat_1(A_79), B_80)=k7_relat_1(B_80, A_79) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_91])).
% 30.03/19.69  tff(c_44, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 30.03/19.69  tff(c_151, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))!=k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_44])).
% 30.03/19.69  tff(c_257, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_251, c_151])).
% 30.03/19.69  tff(c_263, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_257])).
% 30.03/19.69  tff(c_100862, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100086, c_263])).
% 30.03/19.69  tff(c_101005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_100862])).
% 30.03/19.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.03/19.69  
% 30.03/19.69  Inference rules
% 30.03/19.69  ----------------------
% 30.03/19.69  #Ref     : 0
% 30.03/19.69  #Sup     : 24968
% 30.03/19.69  #Fact    : 0
% 30.03/19.69  #Define  : 0
% 30.03/19.69  #Split   : 0
% 30.03/19.69  #Chain   : 0
% 30.03/19.69  #Close   : 0
% 30.03/19.69  
% 30.03/19.69  Ordering : KBO
% 30.03/19.69  
% 30.03/19.69  Simplification rules
% 30.03/19.69  ----------------------
% 30.03/19.69  #Subsume      : 4236
% 30.03/19.69  #Demod        : 31558
% 30.03/19.69  #Tautology    : 5469
% 30.03/19.69  #SimpNegUnit  : 0
% 30.03/19.69  #BackRed      : 72
% 30.03/19.69  
% 30.03/19.69  #Partial instantiations: 0
% 30.03/19.69  #Strategies tried      : 1
% 30.03/19.69  
% 30.03/19.69  Timing (in seconds)
% 30.03/19.69  ----------------------
% 30.03/19.70  Preprocessing        : 0.32
% 30.03/19.70  Parsing              : 0.18
% 30.03/19.70  CNF conversion       : 0.02
% 30.03/19.70  Main loop            : 18.58
% 30.03/19.70  Inferencing          : 2.70
% 30.03/19.70  Reduction            : 9.73
% 30.03/19.70  Demodulation         : 8.82
% 30.03/19.70  BG Simplification    : 0.49
% 30.03/19.70  Subsumption          : 4.70
% 30.03/19.70  Abstraction          : 0.86
% 30.03/19.70  MUC search           : 0.00
% 30.03/19.70  Cooper               : 0.00
% 30.03/19.70  Total                : 18.96
% 30.03/19.70  Index Insertion      : 0.00
% 30.03/19.70  Index Deletion       : 0.00
% 30.03/19.70  Index Matching       : 0.00
% 30.03/19.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
