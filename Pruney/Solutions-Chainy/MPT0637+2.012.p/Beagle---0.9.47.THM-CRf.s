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
% DateTime   : Thu Dec  3 10:03:25 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.40s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 355 expanded)
%              Number of leaves         :   33 ( 135 expanded)
%              Depth                    :   15
%              Number of atoms          :  171 ( 607 expanded)
%              Number of equality atoms :   60 ( 178 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [B_57,A_58] : k1_setfam_1(k2_tarski(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_110])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_10])).

tff(c_30,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_125,plain,(
    ! [A_55] :
      ( k7_relat_1(A_55,k1_relat_1(A_55)) = A_55
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_134,plain,(
    ! [A_32] :
      ( k7_relat_1(k6_relat_1(A_32),A_32) = k6_relat_1(A_32)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_138,plain,(
    ! [A_32] : k7_relat_1(k6_relat_1(A_32),A_32) = k6_relat_1(A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_134])).

tff(c_682,plain,(
    ! [C_112,A_113,B_114] :
      ( k7_relat_1(k7_relat_1(C_112,A_113),B_114) = k7_relat_1(C_112,k3_xboole_0(A_113,B_114))
      | ~ v1_relat_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_716,plain,(
    ! [A_32,B_114] :
      ( k7_relat_1(k6_relat_1(A_32),k3_xboole_0(A_32,B_114)) = k7_relat_1(k6_relat_1(A_32),B_114)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_682])).

tff(c_752,plain,(
    ! [A_117,B_118] : k7_relat_1(k6_relat_1(A_117),k3_xboole_0(A_117,B_118)) = k7_relat_1(k6_relat_1(A_117),B_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_716])).

tff(c_274,plain,(
    ! [A_78,B_79] :
      ( k5_relat_1(k6_relat_1(A_78),B_79) = k7_relat_1(B_79,A_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k5_relat_1(B_34,k6_relat_1(A_33)),B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_285,plain,(
    ! [A_33,A_78] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_33),A_78),k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_36])).

tff(c_306,plain,(
    ! [A_33,A_78] : r1_tarski(k7_relat_1(k6_relat_1(A_33),A_78),k6_relat_1(A_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_285])).

tff(c_778,plain,(
    ! [A_117,B_118] : r1_tarski(k7_relat_1(k6_relat_1(A_117),B_118),k6_relat_1(k3_xboole_0(A_117,B_118))) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_306])).

tff(c_18,plain,(
    ! [C_19,A_17,B_18] :
      ( k7_relat_1(k7_relat_1(C_19,A_17),B_18) = k7_relat_1(C_19,k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [B_25,A_24] :
      ( k5_relat_1(B_25,k6_relat_1(A_24)) = k8_relat_1(A_24,B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_281,plain,(
    ! [A_24,A_78] :
      ( k8_relat_1(A_24,k6_relat_1(A_78)) = k7_relat_1(k6_relat_1(A_24),A_78)
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_22])).

tff(c_364,plain,(
    ! [A_86,A_87] : k8_relat_1(A_86,k6_relat_1(A_87)) = k7_relat_1(k6_relat_1(A_86),A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_281])).

tff(c_240,plain,(
    ! [B_72,A_73] :
      ( k5_relat_1(B_72,k6_relat_1(A_73)) = k8_relat_1(A_73,B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k5_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_253,plain,(
    ! [A_73,B_72] :
      ( v1_relat_1(k8_relat_1(A_73,B_72))
      | ~ v1_relat_1(k6_relat_1(A_73))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_12])).

tff(c_264,plain,(
    ! [A_73,B_72] :
      ( v1_relat_1(k8_relat_1(A_73,B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_253])).

tff(c_370,plain,(
    ! [A_86,A_87] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87))
      | ~ v1_relat_1(k6_relat_1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_264])).

tff(c_376,plain,(
    ! [A_86,A_87] : v1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_370])).

tff(c_40,plain,(
    ! [A_37,B_38] :
      ( k5_relat_1(k6_relat_1(A_37),B_38) = k7_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1287,plain,(
    ! [B_139,C_140,A_141] :
      ( k7_relat_1(k5_relat_1(B_139,C_140),A_141) = k5_relat_1(k7_relat_1(B_139,A_141),C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1324,plain,(
    ! [A_37,A_141,B_38] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_37),A_141),B_38) = k7_relat_1(k7_relat_1(B_38,A_37),A_141)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1287])).

tff(c_2829,plain,(
    ! [A_193,A_194,B_195] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_193),A_194),B_195) = k7_relat_1(k7_relat_1(B_195,A_193),A_194)
      | ~ v1_relat_1(B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1324])).

tff(c_2855,plain,(
    ! [A_33,A_193,A_194] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_33),A_193),A_194),k7_relat_1(k6_relat_1(A_193),A_194))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_193),A_194))
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2829,c_36])).

tff(c_3821,plain,(
    ! [A_216,A_217,A_218] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_216),A_217),A_218),k7_relat_1(k6_relat_1(A_217),A_218)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_376,c_2855])).

tff(c_3867,plain,(
    ! [A_216,A_17,B_18] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_216),k3_xboole_0(A_17,B_18)),k7_relat_1(k6_relat_1(A_17),B_18))
      | ~ v1_relat_1(k6_relat_1(A_216)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3821])).

tff(c_9033,plain,(
    ! [A_288,A_289,B_290] : r1_tarski(k7_relat_1(k6_relat_1(A_288),k3_xboole_0(A_289,B_290)),k7_relat_1(k6_relat_1(A_289),B_290)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3867])).

tff(c_9223,plain,(
    ! [A_291,B_292] : r1_tarski(k6_relat_1(k3_xboole_0(A_291,B_292)),k7_relat_1(k6_relat_1(A_291),B_292)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_9033])).

tff(c_32,plain,(
    ! [A_32] : k2_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_529,plain,(
    ! [B_104,A_105] :
      ( k5_relat_1(B_104,k6_relat_1(A_105)) = B_104
      | ~ r1_tarski(k2_relat_1(B_104),A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_536,plain,(
    ! [A_32,A_105] :
      ( k5_relat_1(k6_relat_1(A_32),k6_relat_1(A_105)) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_105)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_529])).

tff(c_540,plain,(
    ! [A_106,A_107] :
      ( k5_relat_1(k6_relat_1(A_106),k6_relat_1(A_107)) = k6_relat_1(A_106)
      | ~ r1_tarski(A_106,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_536])).

tff(c_546,plain,(
    ! [A_107,A_106] :
      ( k7_relat_1(k6_relat_1(A_107),A_106) = k6_relat_1(A_106)
      | ~ v1_relat_1(k6_relat_1(A_107))
      | ~ r1_tarski(A_106,A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_40])).

tff(c_589,plain,(
    ! [A_108,A_109] :
      ( k7_relat_1(k6_relat_1(A_108),A_109) = k6_relat_1(A_109)
      | ~ r1_tarski(A_109,A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_546])).

tff(c_403,plain,(
    ! [B_92,A_93] :
      ( k7_relat_1(B_92,A_93) = B_92
      | ~ r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_406,plain,(
    ! [A_32,A_93] :
      ( k7_relat_1(k6_relat_1(A_32),A_93) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_93)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_403])).

tff(c_408,plain,(
    ! [A_32,A_93] :
      ( k7_relat_1(k6_relat_1(A_32),A_93) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_406])).

tff(c_598,plain,(
    ! [A_109,A_108] :
      ( k6_relat_1(A_109) = k6_relat_1(A_108)
      | ~ r1_tarski(A_108,A_109)
      | ~ r1_tarski(A_109,A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_408])).

tff(c_9234,plain,(
    ! [A_291,B_292] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_291),B_292)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_291,B_292)))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_291),B_292),k6_relat_1(k3_xboole_0(A_291,B_292))) ) ),
    inference(resolution,[status(thm)],[c_9223,c_598])).

tff(c_9361,plain,(
    ! [A_291,B_292] : k6_relat_1(k7_relat_1(k6_relat_1(A_291),B_292)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_291,B_292))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_9234])).

tff(c_304,plain,(
    ! [A_24,A_78] : k8_relat_1(A_24,k6_relat_1(A_78)) = k7_relat_1(k6_relat_1(A_24),A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_281])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_33),B_34),B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_250,plain,(
    ! [A_73,A_33] :
      ( r1_tarski(k8_relat_1(A_73,k6_relat_1(A_33)),k6_relat_1(A_73))
      | ~ v1_relat_1(k6_relat_1(A_73))
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_34])).

tff(c_262,plain,(
    ! [A_73,A_33] : r1_tarski(k8_relat_1(A_73,k6_relat_1(A_33)),k6_relat_1(A_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_250])).

tff(c_363,plain,(
    ! [A_73,A_33] : r1_tarski(k7_relat_1(k6_relat_1(A_73),A_33),k6_relat_1(A_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_262])).

tff(c_1069,plain,(
    ! [A_133,B_134] :
      ( r1_tarski(k1_relat_1(A_133),k1_relat_1(B_134))
      | ~ r1_tarski(A_133,B_134)
      | ~ v1_relat_1(B_134)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1081,plain,(
    ! [A_133,A_32] :
      ( r1_tarski(k1_relat_1(A_133),A_32)
      | ~ r1_tarski(A_133,k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1069])).

tff(c_1344,plain,(
    ! [A_142,A_143] :
      ( r1_tarski(k1_relat_1(A_142),A_143)
      | ~ r1_tarski(A_142,k6_relat_1(A_143))
      | ~ v1_relat_1(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1081])).

tff(c_42,plain,(
    ! [B_40,A_39] :
      ( k7_relat_1(B_40,A_39) = B_40
      | ~ r1_tarski(k1_relat_1(B_40),A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1369,plain,(
    ! [A_146,A_147] :
      ( k7_relat_1(A_146,A_147) = A_146
      | ~ r1_tarski(A_146,k6_relat_1(A_147))
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_1344,c_42])).

tff(c_1397,plain,(
    ! [A_73,A_33] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_73),A_33),A_73) = k7_relat_1(k6_relat_1(A_73),A_33)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_73),A_33)) ) ),
    inference(resolution,[status(thm)],[c_363,c_1369])).

tff(c_1430,plain,(
    ! [A_73,A_33] : k7_relat_1(k7_relat_1(k6_relat_1(A_73),A_33),A_73) = k7_relat_1(k6_relat_1(A_73),A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_1397])).

tff(c_3836,plain,(
    ! [A_73,A_33] : r1_tarski(k7_relat_1(k6_relat_1(A_73),A_33),k7_relat_1(k6_relat_1(A_33),A_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_3821])).

tff(c_3923,plain,(
    ! [A_219,A_220] : r1_tarski(k7_relat_1(k6_relat_1(A_219),A_220),k7_relat_1(k6_relat_1(A_220),A_219)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_3821])).

tff(c_3928,plain,(
    ! [A_220,A_219] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_220),A_219)) = k6_relat_1(k7_relat_1(k6_relat_1(A_219),A_220))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_220),A_219),k7_relat_1(k6_relat_1(A_219),A_220)) ) ),
    inference(resolution,[status(thm)],[c_3923,c_598])).

tff(c_3997,plain,(
    ! [A_222,A_221] : k6_relat_1(k7_relat_1(k6_relat_1(A_222),A_221)) = k6_relat_1(k7_relat_1(k6_relat_1(A_221),A_222)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3836,c_3928])).

tff(c_4323,plain,(
    ! [A_221,A_222] : k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_221),A_222))) = k7_relat_1(k6_relat_1(A_222),A_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_3997,c_30])).

tff(c_11080,plain,(
    ! [A_221,A_222] : k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_221,A_222)))) = k7_relat_1(k6_relat_1(A_222),A_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9361,c_4323])).

tff(c_11083,plain,(
    ! [A_222,A_221] : k7_relat_1(k6_relat_1(A_222),A_221) = k6_relat_1(k3_xboole_0(A_221,A_222)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_11080])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_294,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_46])).

tff(c_310,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_294])).

tff(c_11512,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11083,c_310])).

tff(c_11532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_11512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:50:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.06/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.40/2.83  
% 8.40/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.40/2.83  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.40/2.83  
% 8.40/2.83  %Foreground sorts:
% 8.40/2.83  
% 8.40/2.83  
% 8.40/2.83  %Background operators:
% 8.40/2.83  
% 8.40/2.83  
% 8.40/2.83  %Foreground operators:
% 8.40/2.83  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.40/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.40/2.83  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.40/2.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.40/2.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.40/2.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.40/2.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.40/2.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.40/2.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.40/2.83  tff('#skF_2', type, '#skF_2': $i).
% 8.40/2.83  tff('#skF_1', type, '#skF_1': $i).
% 8.40/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.40/2.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.40/2.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.40/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.40/2.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.40/2.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.40/2.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.40/2.83  
% 8.40/2.85  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.40/2.85  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.40/2.85  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.40/2.85  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 8.40/2.85  tff(f_109, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 8.40/2.85  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 8.40/2.85  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 8.40/2.85  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 8.40/2.85  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 8.40/2.85  tff(f_43, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 8.40/2.85  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 8.40/2.85  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 8.40/2.85  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 8.40/2.85  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 8.40/2.85  tff(f_112, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 8.40/2.85  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.40/2.85  tff(c_110, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.40/2.85  tff(c_148, plain, (![B_57, A_58]: (k1_setfam_1(k2_tarski(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_4, c_110])).
% 8.40/2.85  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.40/2.85  tff(c_154, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_148, c_10])).
% 8.40/2.85  tff(c_30, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.40/2.85  tff(c_14, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.40/2.85  tff(c_125, plain, (![A_55]: (k7_relat_1(A_55, k1_relat_1(A_55))=A_55 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.40/2.85  tff(c_134, plain, (![A_32]: (k7_relat_1(k6_relat_1(A_32), A_32)=k6_relat_1(A_32) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_125])).
% 8.40/2.85  tff(c_138, plain, (![A_32]: (k7_relat_1(k6_relat_1(A_32), A_32)=k6_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_134])).
% 8.40/2.85  tff(c_682, plain, (![C_112, A_113, B_114]: (k7_relat_1(k7_relat_1(C_112, A_113), B_114)=k7_relat_1(C_112, k3_xboole_0(A_113, B_114)) | ~v1_relat_1(C_112))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.40/2.85  tff(c_716, plain, (![A_32, B_114]: (k7_relat_1(k6_relat_1(A_32), k3_xboole_0(A_32, B_114))=k7_relat_1(k6_relat_1(A_32), B_114) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_682])).
% 8.40/2.85  tff(c_752, plain, (![A_117, B_118]: (k7_relat_1(k6_relat_1(A_117), k3_xboole_0(A_117, B_118))=k7_relat_1(k6_relat_1(A_117), B_118))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_716])).
% 8.40/2.85  tff(c_274, plain, (![A_78, B_79]: (k5_relat_1(k6_relat_1(A_78), B_79)=k7_relat_1(B_79, A_78) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.40/2.85  tff(c_36, plain, (![B_34, A_33]: (r1_tarski(k5_relat_1(B_34, k6_relat_1(A_33)), B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.40/2.85  tff(c_285, plain, (![A_33, A_78]: (r1_tarski(k7_relat_1(k6_relat_1(A_33), A_78), k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_274, c_36])).
% 8.40/2.85  tff(c_306, plain, (![A_33, A_78]: (r1_tarski(k7_relat_1(k6_relat_1(A_33), A_78), k6_relat_1(A_78)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_285])).
% 8.40/2.85  tff(c_778, plain, (![A_117, B_118]: (r1_tarski(k7_relat_1(k6_relat_1(A_117), B_118), k6_relat_1(k3_xboole_0(A_117, B_118))))), inference(superposition, [status(thm), theory('equality')], [c_752, c_306])).
% 8.40/2.85  tff(c_18, plain, (![C_19, A_17, B_18]: (k7_relat_1(k7_relat_1(C_19, A_17), B_18)=k7_relat_1(C_19, k3_xboole_0(A_17, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.40/2.85  tff(c_22, plain, (![B_25, A_24]: (k5_relat_1(B_25, k6_relat_1(A_24))=k8_relat_1(A_24, B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.40/2.85  tff(c_281, plain, (![A_24, A_78]: (k8_relat_1(A_24, k6_relat_1(A_78))=k7_relat_1(k6_relat_1(A_24), A_78) | ~v1_relat_1(k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_274, c_22])).
% 8.40/2.85  tff(c_364, plain, (![A_86, A_87]: (k8_relat_1(A_86, k6_relat_1(A_87))=k7_relat_1(k6_relat_1(A_86), A_87))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_281])).
% 8.40/2.85  tff(c_240, plain, (![B_72, A_73]: (k5_relat_1(B_72, k6_relat_1(A_73))=k8_relat_1(A_73, B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.40/2.85  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.40/2.85  tff(c_253, plain, (![A_73, B_72]: (v1_relat_1(k8_relat_1(A_73, B_72)) | ~v1_relat_1(k6_relat_1(A_73)) | ~v1_relat_1(B_72) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_240, c_12])).
% 8.40/2.85  tff(c_264, plain, (![A_73, B_72]: (v1_relat_1(k8_relat_1(A_73, B_72)) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_253])).
% 8.40/2.85  tff(c_370, plain, (![A_86, A_87]: (v1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87)) | ~v1_relat_1(k6_relat_1(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_364, c_264])).
% 8.40/2.85  tff(c_376, plain, (![A_86, A_87]: (v1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_370])).
% 8.40/2.85  tff(c_40, plain, (![A_37, B_38]: (k5_relat_1(k6_relat_1(A_37), B_38)=k7_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.40/2.85  tff(c_1287, plain, (![B_139, C_140, A_141]: (k7_relat_1(k5_relat_1(B_139, C_140), A_141)=k5_relat_1(k7_relat_1(B_139, A_141), C_140) | ~v1_relat_1(C_140) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.40/2.85  tff(c_1324, plain, (![A_37, A_141, B_38]: (k5_relat_1(k7_relat_1(k6_relat_1(A_37), A_141), B_38)=k7_relat_1(k7_relat_1(B_38, A_37), A_141) | ~v1_relat_1(B_38) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1287])).
% 8.40/2.85  tff(c_2829, plain, (![A_193, A_194, B_195]: (k5_relat_1(k7_relat_1(k6_relat_1(A_193), A_194), B_195)=k7_relat_1(k7_relat_1(B_195, A_193), A_194) | ~v1_relat_1(B_195))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1324])).
% 8.40/2.85  tff(c_2855, plain, (![A_33, A_193, A_194]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_33), A_193), A_194), k7_relat_1(k6_relat_1(A_193), A_194)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_193), A_194)) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_2829, c_36])).
% 8.40/2.85  tff(c_3821, plain, (![A_216, A_217, A_218]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_216), A_217), A_218), k7_relat_1(k6_relat_1(A_217), A_218)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_376, c_2855])).
% 8.40/2.85  tff(c_3867, plain, (![A_216, A_17, B_18]: (r1_tarski(k7_relat_1(k6_relat_1(A_216), k3_xboole_0(A_17, B_18)), k7_relat_1(k6_relat_1(A_17), B_18)) | ~v1_relat_1(k6_relat_1(A_216)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3821])).
% 8.40/2.85  tff(c_9033, plain, (![A_288, A_289, B_290]: (r1_tarski(k7_relat_1(k6_relat_1(A_288), k3_xboole_0(A_289, B_290)), k7_relat_1(k6_relat_1(A_289), B_290)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3867])).
% 8.40/2.85  tff(c_9223, plain, (![A_291, B_292]: (r1_tarski(k6_relat_1(k3_xboole_0(A_291, B_292)), k7_relat_1(k6_relat_1(A_291), B_292)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_9033])).
% 8.40/2.85  tff(c_32, plain, (![A_32]: (k2_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.40/2.85  tff(c_529, plain, (![B_104, A_105]: (k5_relat_1(B_104, k6_relat_1(A_105))=B_104 | ~r1_tarski(k2_relat_1(B_104), A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.40/2.85  tff(c_536, plain, (![A_32, A_105]: (k5_relat_1(k6_relat_1(A_32), k6_relat_1(A_105))=k6_relat_1(A_32) | ~r1_tarski(A_32, A_105) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_529])).
% 8.40/2.85  tff(c_540, plain, (![A_106, A_107]: (k5_relat_1(k6_relat_1(A_106), k6_relat_1(A_107))=k6_relat_1(A_106) | ~r1_tarski(A_106, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_536])).
% 8.40/2.85  tff(c_546, plain, (![A_107, A_106]: (k7_relat_1(k6_relat_1(A_107), A_106)=k6_relat_1(A_106) | ~v1_relat_1(k6_relat_1(A_107)) | ~r1_tarski(A_106, A_107))), inference(superposition, [status(thm), theory('equality')], [c_540, c_40])).
% 8.40/2.85  tff(c_589, plain, (![A_108, A_109]: (k7_relat_1(k6_relat_1(A_108), A_109)=k6_relat_1(A_109) | ~r1_tarski(A_109, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_546])).
% 8.40/2.85  tff(c_403, plain, (![B_92, A_93]: (k7_relat_1(B_92, A_93)=B_92 | ~r1_tarski(k1_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.40/2.85  tff(c_406, plain, (![A_32, A_93]: (k7_relat_1(k6_relat_1(A_32), A_93)=k6_relat_1(A_32) | ~r1_tarski(A_32, A_93) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_403])).
% 8.40/2.85  tff(c_408, plain, (![A_32, A_93]: (k7_relat_1(k6_relat_1(A_32), A_93)=k6_relat_1(A_32) | ~r1_tarski(A_32, A_93))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_406])).
% 8.40/2.85  tff(c_598, plain, (![A_109, A_108]: (k6_relat_1(A_109)=k6_relat_1(A_108) | ~r1_tarski(A_108, A_109) | ~r1_tarski(A_109, A_108))), inference(superposition, [status(thm), theory('equality')], [c_589, c_408])).
% 8.40/2.85  tff(c_9234, plain, (![A_291, B_292]: (k6_relat_1(k7_relat_1(k6_relat_1(A_291), B_292))=k6_relat_1(k6_relat_1(k3_xboole_0(A_291, B_292))) | ~r1_tarski(k7_relat_1(k6_relat_1(A_291), B_292), k6_relat_1(k3_xboole_0(A_291, B_292))))), inference(resolution, [status(thm)], [c_9223, c_598])).
% 8.40/2.85  tff(c_9361, plain, (![A_291, B_292]: (k6_relat_1(k7_relat_1(k6_relat_1(A_291), B_292))=k6_relat_1(k6_relat_1(k3_xboole_0(A_291, B_292))))), inference(demodulation, [status(thm), theory('equality')], [c_778, c_9234])).
% 8.40/2.85  tff(c_304, plain, (![A_24, A_78]: (k8_relat_1(A_24, k6_relat_1(A_78))=k7_relat_1(k6_relat_1(A_24), A_78))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_281])).
% 8.40/2.85  tff(c_34, plain, (![A_33, B_34]: (r1_tarski(k5_relat_1(k6_relat_1(A_33), B_34), B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.40/2.85  tff(c_250, plain, (![A_73, A_33]: (r1_tarski(k8_relat_1(A_73, k6_relat_1(A_33)), k6_relat_1(A_73)) | ~v1_relat_1(k6_relat_1(A_73)) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_240, c_34])).
% 8.40/2.85  tff(c_262, plain, (![A_73, A_33]: (r1_tarski(k8_relat_1(A_73, k6_relat_1(A_33)), k6_relat_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_250])).
% 8.40/2.85  tff(c_363, plain, (![A_73, A_33]: (r1_tarski(k7_relat_1(k6_relat_1(A_73), A_33), k6_relat_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_262])).
% 8.40/2.85  tff(c_1069, plain, (![A_133, B_134]: (r1_tarski(k1_relat_1(A_133), k1_relat_1(B_134)) | ~r1_tarski(A_133, B_134) | ~v1_relat_1(B_134) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.40/2.85  tff(c_1081, plain, (![A_133, A_32]: (r1_tarski(k1_relat_1(A_133), A_32) | ~r1_tarski(A_133, k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1069])).
% 8.40/2.85  tff(c_1344, plain, (![A_142, A_143]: (r1_tarski(k1_relat_1(A_142), A_143) | ~r1_tarski(A_142, k6_relat_1(A_143)) | ~v1_relat_1(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1081])).
% 8.40/2.85  tff(c_42, plain, (![B_40, A_39]: (k7_relat_1(B_40, A_39)=B_40 | ~r1_tarski(k1_relat_1(B_40), A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.40/2.85  tff(c_1369, plain, (![A_146, A_147]: (k7_relat_1(A_146, A_147)=A_146 | ~r1_tarski(A_146, k6_relat_1(A_147)) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_1344, c_42])).
% 8.40/2.85  tff(c_1397, plain, (![A_73, A_33]: (k7_relat_1(k7_relat_1(k6_relat_1(A_73), A_33), A_73)=k7_relat_1(k6_relat_1(A_73), A_33) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_73), A_33)))), inference(resolution, [status(thm)], [c_363, c_1369])).
% 8.40/2.85  tff(c_1430, plain, (![A_73, A_33]: (k7_relat_1(k7_relat_1(k6_relat_1(A_73), A_33), A_73)=k7_relat_1(k6_relat_1(A_73), A_33))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_1397])).
% 8.40/2.85  tff(c_3836, plain, (![A_73, A_33]: (r1_tarski(k7_relat_1(k6_relat_1(A_73), A_33), k7_relat_1(k6_relat_1(A_33), A_73)))), inference(superposition, [status(thm), theory('equality')], [c_1430, c_3821])).
% 8.40/2.85  tff(c_3923, plain, (![A_219, A_220]: (r1_tarski(k7_relat_1(k6_relat_1(A_219), A_220), k7_relat_1(k6_relat_1(A_220), A_219)))), inference(superposition, [status(thm), theory('equality')], [c_1430, c_3821])).
% 8.40/2.85  tff(c_3928, plain, (![A_220, A_219]: (k6_relat_1(k7_relat_1(k6_relat_1(A_220), A_219))=k6_relat_1(k7_relat_1(k6_relat_1(A_219), A_220)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_220), A_219), k7_relat_1(k6_relat_1(A_219), A_220)))), inference(resolution, [status(thm)], [c_3923, c_598])).
% 8.40/2.85  tff(c_3997, plain, (![A_222, A_221]: (k6_relat_1(k7_relat_1(k6_relat_1(A_222), A_221))=k6_relat_1(k7_relat_1(k6_relat_1(A_221), A_222)))), inference(demodulation, [status(thm), theory('equality')], [c_3836, c_3928])).
% 8.40/2.85  tff(c_4323, plain, (![A_221, A_222]: (k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_221), A_222)))=k7_relat_1(k6_relat_1(A_222), A_221))), inference(superposition, [status(thm), theory('equality')], [c_3997, c_30])).
% 8.40/2.85  tff(c_11080, plain, (![A_221, A_222]: (k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_221, A_222))))=k7_relat_1(k6_relat_1(A_222), A_221))), inference(demodulation, [status(thm), theory('equality')], [c_9361, c_4323])).
% 8.40/2.85  tff(c_11083, plain, (![A_222, A_221]: (k7_relat_1(k6_relat_1(A_222), A_221)=k6_relat_1(k3_xboole_0(A_221, A_222)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_11080])).
% 8.40/2.85  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.40/2.85  tff(c_294, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_46])).
% 8.40/2.85  tff(c_310, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_294])).
% 8.40/2.85  tff(c_11512, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11083, c_310])).
% 8.40/2.85  tff(c_11532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_11512])).
% 8.40/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.40/2.85  
% 8.40/2.85  Inference rules
% 8.40/2.85  ----------------------
% 8.40/2.85  #Ref     : 0
% 8.40/2.85  #Sup     : 2665
% 8.40/2.85  #Fact    : 0
% 8.40/2.85  #Define  : 0
% 8.40/2.85  #Split   : 2
% 8.40/2.85  #Chain   : 0
% 8.40/2.85  #Close   : 0
% 8.40/2.85  
% 8.40/2.85  Ordering : KBO
% 8.40/2.85  
% 8.40/2.85  Simplification rules
% 8.40/2.85  ----------------------
% 8.40/2.85  #Subsume      : 350
% 8.40/2.85  #Demod        : 2827
% 8.40/2.85  #Tautology    : 996
% 8.40/2.85  #SimpNegUnit  : 0
% 8.40/2.85  #BackRed      : 60
% 8.40/2.85  
% 8.40/2.85  #Partial instantiations: 0
% 8.40/2.85  #Strategies tried      : 1
% 8.40/2.85  
% 8.40/2.85  Timing (in seconds)
% 8.40/2.85  ----------------------
% 8.40/2.86  Preprocessing        : 0.32
% 8.40/2.86  Parsing              : 0.17
% 8.40/2.86  CNF conversion       : 0.02
% 8.40/2.86  Main loop            : 1.77
% 8.40/2.86  Inferencing          : 0.49
% 8.40/2.86  Reduction            : 0.78
% 8.40/2.86  Demodulation         : 0.65
% 8.40/2.86  BG Simplification    : 0.07
% 8.40/2.86  Subsumption          : 0.32
% 8.40/2.86  Abstraction          : 0.10
% 8.40/2.86  MUC search           : 0.00
% 8.40/2.86  Cooper               : 0.00
% 8.40/2.86  Total                : 2.14
% 8.40/2.86  Index Insertion      : 0.00
% 8.40/2.86  Index Deletion       : 0.00
% 8.40/2.86  Index Matching       : 0.00
% 8.40/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
