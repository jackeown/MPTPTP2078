%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:25 EST 2020

% Result     : Theorem 8.22s
% Output     : CNFRefutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 390 expanded)
%              Number of leaves         :   34 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 667 expanded)
%              Number of equality atoms :   57 ( 196 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_90,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(B_61,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_165,plain,(
    ! [B_61,A_60] : k3_xboole_0(B_61,A_60) = k3_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_10])).

tff(c_32,plain,(
    ! [A_35] : k1_relat_1(k6_relat_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    ! [A_54] :
      ( k7_relat_1(A_54,k1_relat_1(A_54)) = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_121,plain,(
    ! [A_35] :
      ( k7_relat_1(k6_relat_1(A_35),A_35) = k6_relat_1(A_35)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_112])).

tff(c_125,plain,(
    ! [A_35] : k7_relat_1(k6_relat_1(A_35),A_35) = k6_relat_1(A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_121])).

tff(c_540,plain,(
    ! [C_107,A_108,B_109] :
      ( k7_relat_1(k7_relat_1(C_107,A_108),B_109) = k7_relat_1(C_107,k3_xboole_0(A_108,B_109))
      | ~ v1_relat_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_568,plain,(
    ! [A_35,B_109] :
      ( k7_relat_1(k6_relat_1(A_35),k3_xboole_0(A_35,B_109)) = k7_relat_1(k6_relat_1(A_35),B_109)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_540])).

tff(c_667,plain,(
    ! [A_117,B_118] : k7_relat_1(k6_relat_1(A_117),k3_xboole_0(A_117,B_118)) = k7_relat_1(k6_relat_1(A_117),B_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_568])).

tff(c_276,plain,(
    ! [A_78,B_79] :
      ( k5_relat_1(k6_relat_1(A_78),B_79) = k7_relat_1(B_79,A_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k5_relat_1(B_38,k6_relat_1(A_37)),B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_293,plain,(
    ! [A_37,A_78] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_37),A_78),k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_40])).

tff(c_310,plain,(
    ! [A_37,A_78] : r1_tarski(k7_relat_1(k6_relat_1(A_37),A_78),k6_relat_1(A_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_293])).

tff(c_693,plain,(
    ! [A_117,B_118] : r1_tarski(k7_relat_1(k6_relat_1(A_117),B_118),k6_relat_1(k3_xboole_0(A_117,B_118))) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_310])).

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

tff(c_283,plain,(
    ! [A_24,A_78] :
      ( k8_relat_1(A_24,k6_relat_1(A_78)) = k7_relat_1(k6_relat_1(A_24),A_78)
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_22])).

tff(c_366,plain,(
    ! [A_86,A_87] : k8_relat_1(A_86,k6_relat_1(A_87)) = k7_relat_1(k6_relat_1(A_86),A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_283])).

tff(c_242,plain,(
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

tff(c_248,plain,(
    ! [A_73,B_72] :
      ( v1_relat_1(k8_relat_1(A_73,B_72))
      | ~ v1_relat_1(k6_relat_1(A_73))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_12])).

tff(c_264,plain,(
    ! [A_73,B_72] :
      ( v1_relat_1(k8_relat_1(A_73,B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_248])).

tff(c_372,plain,(
    ! [A_86,A_87] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87))
      | ~ v1_relat_1(k6_relat_1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_264])).

tff(c_378,plain,(
    ! [A_86,A_87] : v1_relat_1(k7_relat_1(k6_relat_1(A_86),A_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_372])).

tff(c_42,plain,(
    ! [A_39,B_40] :
      ( k5_relat_1(k6_relat_1(A_39),B_40) = k7_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1046,plain,(
    ! [B_143,C_144,A_145] :
      ( k7_relat_1(k5_relat_1(B_143,C_144),A_145) = k5_relat_1(k7_relat_1(B_143,A_145),C_144)
      | ~ v1_relat_1(C_144)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1077,plain,(
    ! [A_39,A_145,B_40] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_39),A_145),B_40) = k7_relat_1(k7_relat_1(B_40,A_39),A_145)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1046])).

tff(c_3542,plain,(
    ! [A_217,A_218,B_219] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_217),A_218),B_219) = k7_relat_1(k7_relat_1(B_219,A_217),A_218)
      | ~ v1_relat_1(B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1077])).

tff(c_3567,plain,(
    ! [A_37,A_217,A_218] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_37),A_217),A_218),k7_relat_1(k6_relat_1(A_217),A_218))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_217),A_218))
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3542,c_40])).

tff(c_4225,plain,(
    ! [A_232,A_233,A_234] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_232),A_233),A_234),k7_relat_1(k6_relat_1(A_233),A_234)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_378,c_3567])).

tff(c_4297,plain,(
    ! [A_232,A_17,B_18] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_232),k3_xboole_0(A_17,B_18)),k7_relat_1(k6_relat_1(A_17),B_18))
      | ~ v1_relat_1(k6_relat_1(A_232)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4225])).

tff(c_8580,plain,(
    ! [A_301,A_302,B_303] : r1_tarski(k7_relat_1(k6_relat_1(A_301),k3_xboole_0(A_302,B_303)),k7_relat_1(k6_relat_1(A_302),B_303)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4297])).

tff(c_8774,plain,(
    ! [A_304,B_305] : r1_tarski(k6_relat_1(k3_xboole_0(A_304,B_305)),k7_relat_1(k6_relat_1(A_304),B_305)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_8580])).

tff(c_440,plain,(
    ! [B_99,A_100] :
      ( k7_relat_1(B_99,A_100) = B_99
      | ~ r1_tarski(k1_relat_1(B_99),A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_443,plain,(
    ! [A_35,A_100] :
      ( k7_relat_1(k6_relat_1(A_35),A_100) = k6_relat_1(A_35)
      | ~ r1_tarski(A_35,A_100)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_440])).

tff(c_446,plain,(
    ! [A_101,A_102] :
      ( k7_relat_1(k6_relat_1(A_101),A_102) = k6_relat_1(A_101)
      | ~ r1_tarski(A_101,A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_443])).

tff(c_501,plain,(
    ! [A_103,A_104] :
      ( r1_tarski(k6_relat_1(A_103),k6_relat_1(A_104))
      | ~ r1_tarski(A_103,A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_310])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1563,plain,(
    ! [A_156,A_157] :
      ( k3_xboole_0(k6_relat_1(A_156),k6_relat_1(A_157)) = k6_relat_1(A_156)
      | ~ r1_tarski(A_156,A_157) ) ),
    inference(resolution,[status(thm)],[c_501,c_2])).

tff(c_2390,plain,(
    ! [A_186,A_187] :
      ( k3_xboole_0(k6_relat_1(A_186),k6_relat_1(A_187)) = k6_relat_1(A_187)
      | ~ r1_tarski(A_187,A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_165])).

tff(c_505,plain,(
    ! [A_103,A_104] :
      ( k3_xboole_0(k6_relat_1(A_103),k6_relat_1(A_104)) = k6_relat_1(A_103)
      | ~ r1_tarski(A_103,A_104) ) ),
    inference(resolution,[status(thm)],[c_501,c_2])).

tff(c_2417,plain,(
    ! [A_187,A_186] :
      ( k6_relat_1(A_187) = k6_relat_1(A_186)
      | ~ r1_tarski(A_186,A_187)
      | ~ r1_tarski(A_187,A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2390,c_505])).

tff(c_8782,plain,(
    ! [A_304,B_305] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_304),B_305)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_304,B_305)))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_304),B_305),k6_relat_1(k3_xboole_0(A_304,B_305))) ) ),
    inference(resolution,[status(thm)],[c_8774,c_2417])).

tff(c_8903,plain,(
    ! [A_304,B_305] : k6_relat_1(k7_relat_1(k6_relat_1(A_304),B_305)) = k6_relat_1(k6_relat_1(k3_xboole_0(A_304,B_305))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_8782])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_37),B_38),B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_289,plain,(
    ! [B_79,A_78] :
      ( r1_tarski(k7_relat_1(B_79,A_78),B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_38])).

tff(c_826,plain,(
    ! [A_124,B_125] :
      ( r1_tarski(k1_relat_1(A_124),k1_relat_1(B_125))
      | ~ r1_tarski(A_124,B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_838,plain,(
    ! [A_124,A_35] :
      ( r1_tarski(k1_relat_1(A_124),A_35)
      | ~ r1_tarski(A_124,k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_826])).

tff(c_1018,plain,(
    ! [A_139,A_140] :
      ( r1_tarski(k1_relat_1(A_139),A_140)
      | ~ r1_tarski(A_139,k6_relat_1(A_140))
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_838])).

tff(c_44,plain,(
    ! [B_42,A_41] :
      ( k7_relat_1(B_42,A_41) = B_42
      | ~ r1_tarski(k1_relat_1(B_42),A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1091,plain,(
    ! [A_146,A_147] :
      ( k7_relat_1(A_146,A_147) = A_146
      | ~ r1_tarski(A_146,k6_relat_1(A_147))
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_1018,c_44])).

tff(c_1116,plain,(
    ! [A_147,A_78] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_147),A_78),A_147) = k7_relat_1(k6_relat_1(A_147),A_78)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_147),A_78))
      | ~ v1_relat_1(k6_relat_1(A_147)) ) ),
    inference(resolution,[status(thm)],[c_289,c_1091])).

tff(c_1151,plain,(
    ! [A_147,A_78] : k7_relat_1(k7_relat_1(k6_relat_1(A_147),A_78),A_147) = k7_relat_1(k6_relat_1(A_147),A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_378,c_1116])).

tff(c_4284,plain,(
    ! [A_147,A_78] : r1_tarski(k7_relat_1(k6_relat_1(A_147),A_78),k7_relat_1(k6_relat_1(A_78),A_147)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_4225])).

tff(c_4377,plain,(
    ! [A_238,A_239] : r1_tarski(k7_relat_1(k6_relat_1(A_238),A_239),k7_relat_1(k6_relat_1(A_239),A_238)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_4225])).

tff(c_4379,plain,(
    ! [A_239,A_238] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_239),A_238)) = k6_relat_1(k7_relat_1(k6_relat_1(A_238),A_239))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_239),A_238),k7_relat_1(k6_relat_1(A_238),A_239)) ) ),
    inference(resolution,[status(thm)],[c_4377,c_2417])).

tff(c_4553,plain,(
    ! [A_243,A_242] : k6_relat_1(k7_relat_1(k6_relat_1(A_243),A_242)) = k6_relat_1(k7_relat_1(k6_relat_1(A_242),A_243)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4284,c_4379])).

tff(c_4894,plain,(
    ! [A_243,A_242] : k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_243),A_242))) = k7_relat_1(k6_relat_1(A_242),A_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_4553,c_32])).

tff(c_11297,plain,(
    ! [A_243,A_242] : k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_243,A_242)))) = k7_relat_1(k6_relat_1(A_242),A_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8903,c_4894])).

tff(c_11300,plain,(
    ! [A_242,A_243] : k7_relat_1(k6_relat_1(A_242),A_243) = k6_relat_1(k3_xboole_0(A_243,A_242)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11297])).

tff(c_48,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_296,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_48])).

tff(c_312,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_296])).

tff(c_11726,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11300,c_312])).

tff(c_11748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_11726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.22/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/3.00  
% 8.22/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/3.00  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.22/3.00  
% 8.22/3.00  %Foreground sorts:
% 8.22/3.00  
% 8.22/3.00  
% 8.22/3.00  %Background operators:
% 8.22/3.00  
% 8.22/3.00  
% 8.22/3.00  %Foreground operators:
% 8.22/3.00  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.22/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.22/3.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.22/3.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.22/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.22/3.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.22/3.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.22/3.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.22/3.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.22/3.00  tff('#skF_2', type, '#skF_2': $i).
% 8.22/3.00  tff('#skF_1', type, '#skF_1': $i).
% 8.22/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.22/3.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.22/3.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.22/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.22/3.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.22/3.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.22/3.00  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.22/3.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.22/3.00  
% 8.22/3.02  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.22/3.02  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.22/3.02  tff(f_90, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.22/3.02  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 8.22/3.02  tff(f_112, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 8.22/3.02  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 8.22/3.02  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 8.22/3.02  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 8.22/3.02  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 8.22/3.02  tff(f_43, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 8.22/3.02  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 8.22/3.02  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 8.22/3.02  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.22/3.02  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 8.22/3.02  tff(f_115, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 8.22/3.02  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.22/3.02  tff(c_135, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.22/3.02  tff(c_159, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(B_61, A_60))), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 8.22/3.02  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.22/3.02  tff(c_165, plain, (![B_61, A_60]: (k3_xboole_0(B_61, A_60)=k3_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_159, c_10])).
% 8.22/3.02  tff(c_32, plain, (![A_35]: (k1_relat_1(k6_relat_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.22/3.02  tff(c_14, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.22/3.02  tff(c_112, plain, (![A_54]: (k7_relat_1(A_54, k1_relat_1(A_54))=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.22/3.02  tff(c_121, plain, (![A_35]: (k7_relat_1(k6_relat_1(A_35), A_35)=k6_relat_1(A_35) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_112])).
% 8.22/3.02  tff(c_125, plain, (![A_35]: (k7_relat_1(k6_relat_1(A_35), A_35)=k6_relat_1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_121])).
% 8.22/3.02  tff(c_540, plain, (![C_107, A_108, B_109]: (k7_relat_1(k7_relat_1(C_107, A_108), B_109)=k7_relat_1(C_107, k3_xboole_0(A_108, B_109)) | ~v1_relat_1(C_107))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.22/3.02  tff(c_568, plain, (![A_35, B_109]: (k7_relat_1(k6_relat_1(A_35), k3_xboole_0(A_35, B_109))=k7_relat_1(k6_relat_1(A_35), B_109) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_540])).
% 8.22/3.02  tff(c_667, plain, (![A_117, B_118]: (k7_relat_1(k6_relat_1(A_117), k3_xboole_0(A_117, B_118))=k7_relat_1(k6_relat_1(A_117), B_118))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_568])).
% 8.22/3.02  tff(c_276, plain, (![A_78, B_79]: (k5_relat_1(k6_relat_1(A_78), B_79)=k7_relat_1(B_79, A_78) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.22/3.02  tff(c_40, plain, (![B_38, A_37]: (r1_tarski(k5_relat_1(B_38, k6_relat_1(A_37)), B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.22/3.02  tff(c_293, plain, (![A_37, A_78]: (r1_tarski(k7_relat_1(k6_relat_1(A_37), A_78), k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_40])).
% 8.22/3.02  tff(c_310, plain, (![A_37, A_78]: (r1_tarski(k7_relat_1(k6_relat_1(A_37), A_78), k6_relat_1(A_78)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_293])).
% 8.22/3.02  tff(c_693, plain, (![A_117, B_118]: (r1_tarski(k7_relat_1(k6_relat_1(A_117), B_118), k6_relat_1(k3_xboole_0(A_117, B_118))))), inference(superposition, [status(thm), theory('equality')], [c_667, c_310])).
% 8.22/3.02  tff(c_18, plain, (![C_19, A_17, B_18]: (k7_relat_1(k7_relat_1(C_19, A_17), B_18)=k7_relat_1(C_19, k3_xboole_0(A_17, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.22/3.02  tff(c_22, plain, (![B_25, A_24]: (k5_relat_1(B_25, k6_relat_1(A_24))=k8_relat_1(A_24, B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.22/3.02  tff(c_283, plain, (![A_24, A_78]: (k8_relat_1(A_24, k6_relat_1(A_78))=k7_relat_1(k6_relat_1(A_24), A_78) | ~v1_relat_1(k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_22])).
% 8.22/3.02  tff(c_366, plain, (![A_86, A_87]: (k8_relat_1(A_86, k6_relat_1(A_87))=k7_relat_1(k6_relat_1(A_86), A_87))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_283])).
% 8.22/3.02  tff(c_242, plain, (![B_72, A_73]: (k5_relat_1(B_72, k6_relat_1(A_73))=k8_relat_1(A_73, B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.22/3.02  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.22/3.02  tff(c_248, plain, (![A_73, B_72]: (v1_relat_1(k8_relat_1(A_73, B_72)) | ~v1_relat_1(k6_relat_1(A_73)) | ~v1_relat_1(B_72) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_242, c_12])).
% 8.22/3.02  tff(c_264, plain, (![A_73, B_72]: (v1_relat_1(k8_relat_1(A_73, B_72)) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_248])).
% 8.22/3.02  tff(c_372, plain, (![A_86, A_87]: (v1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87)) | ~v1_relat_1(k6_relat_1(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_366, c_264])).
% 8.22/3.02  tff(c_378, plain, (![A_86, A_87]: (v1_relat_1(k7_relat_1(k6_relat_1(A_86), A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_372])).
% 8.22/3.02  tff(c_42, plain, (![A_39, B_40]: (k5_relat_1(k6_relat_1(A_39), B_40)=k7_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.22/3.02  tff(c_1046, plain, (![B_143, C_144, A_145]: (k7_relat_1(k5_relat_1(B_143, C_144), A_145)=k5_relat_1(k7_relat_1(B_143, A_145), C_144) | ~v1_relat_1(C_144) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.22/3.02  tff(c_1077, plain, (![A_39, A_145, B_40]: (k5_relat_1(k7_relat_1(k6_relat_1(A_39), A_145), B_40)=k7_relat_1(k7_relat_1(B_40, A_39), A_145) | ~v1_relat_1(B_40) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1046])).
% 8.22/3.02  tff(c_3542, plain, (![A_217, A_218, B_219]: (k5_relat_1(k7_relat_1(k6_relat_1(A_217), A_218), B_219)=k7_relat_1(k7_relat_1(B_219, A_217), A_218) | ~v1_relat_1(B_219))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1077])).
% 8.22/3.02  tff(c_3567, plain, (![A_37, A_217, A_218]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_37), A_217), A_218), k7_relat_1(k6_relat_1(A_217), A_218)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_217), A_218)) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_3542, c_40])).
% 8.22/3.02  tff(c_4225, plain, (![A_232, A_233, A_234]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_232), A_233), A_234), k7_relat_1(k6_relat_1(A_233), A_234)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_378, c_3567])).
% 8.22/3.02  tff(c_4297, plain, (![A_232, A_17, B_18]: (r1_tarski(k7_relat_1(k6_relat_1(A_232), k3_xboole_0(A_17, B_18)), k7_relat_1(k6_relat_1(A_17), B_18)) | ~v1_relat_1(k6_relat_1(A_232)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4225])).
% 8.22/3.02  tff(c_8580, plain, (![A_301, A_302, B_303]: (r1_tarski(k7_relat_1(k6_relat_1(A_301), k3_xboole_0(A_302, B_303)), k7_relat_1(k6_relat_1(A_302), B_303)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4297])).
% 8.22/3.02  tff(c_8774, plain, (![A_304, B_305]: (r1_tarski(k6_relat_1(k3_xboole_0(A_304, B_305)), k7_relat_1(k6_relat_1(A_304), B_305)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_8580])).
% 8.22/3.02  tff(c_440, plain, (![B_99, A_100]: (k7_relat_1(B_99, A_100)=B_99 | ~r1_tarski(k1_relat_1(B_99), A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.22/3.02  tff(c_443, plain, (![A_35, A_100]: (k7_relat_1(k6_relat_1(A_35), A_100)=k6_relat_1(A_35) | ~r1_tarski(A_35, A_100) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_440])).
% 8.22/3.02  tff(c_446, plain, (![A_101, A_102]: (k7_relat_1(k6_relat_1(A_101), A_102)=k6_relat_1(A_101) | ~r1_tarski(A_101, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_443])).
% 8.22/3.02  tff(c_501, plain, (![A_103, A_104]: (r1_tarski(k6_relat_1(A_103), k6_relat_1(A_104)) | ~r1_tarski(A_103, A_104))), inference(superposition, [status(thm), theory('equality')], [c_446, c_310])).
% 8.22/3.02  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.22/3.02  tff(c_1563, plain, (![A_156, A_157]: (k3_xboole_0(k6_relat_1(A_156), k6_relat_1(A_157))=k6_relat_1(A_156) | ~r1_tarski(A_156, A_157))), inference(resolution, [status(thm)], [c_501, c_2])).
% 8.22/3.02  tff(c_2390, plain, (![A_186, A_187]: (k3_xboole_0(k6_relat_1(A_186), k6_relat_1(A_187))=k6_relat_1(A_187) | ~r1_tarski(A_187, A_186))), inference(superposition, [status(thm), theory('equality')], [c_1563, c_165])).
% 8.22/3.02  tff(c_505, plain, (![A_103, A_104]: (k3_xboole_0(k6_relat_1(A_103), k6_relat_1(A_104))=k6_relat_1(A_103) | ~r1_tarski(A_103, A_104))), inference(resolution, [status(thm)], [c_501, c_2])).
% 8.22/3.02  tff(c_2417, plain, (![A_187, A_186]: (k6_relat_1(A_187)=k6_relat_1(A_186) | ~r1_tarski(A_186, A_187) | ~r1_tarski(A_187, A_186))), inference(superposition, [status(thm), theory('equality')], [c_2390, c_505])).
% 8.22/3.02  tff(c_8782, plain, (![A_304, B_305]: (k6_relat_1(k7_relat_1(k6_relat_1(A_304), B_305))=k6_relat_1(k6_relat_1(k3_xboole_0(A_304, B_305))) | ~r1_tarski(k7_relat_1(k6_relat_1(A_304), B_305), k6_relat_1(k3_xboole_0(A_304, B_305))))), inference(resolution, [status(thm)], [c_8774, c_2417])).
% 8.22/3.02  tff(c_8903, plain, (![A_304, B_305]: (k6_relat_1(k7_relat_1(k6_relat_1(A_304), B_305))=k6_relat_1(k6_relat_1(k3_xboole_0(A_304, B_305))))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_8782])).
% 8.22/3.02  tff(c_38, plain, (![A_37, B_38]: (r1_tarski(k5_relat_1(k6_relat_1(A_37), B_38), B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.22/3.02  tff(c_289, plain, (![B_79, A_78]: (r1_tarski(k7_relat_1(B_79, A_78), B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(B_79))), inference(superposition, [status(thm), theory('equality')], [c_276, c_38])).
% 8.22/3.02  tff(c_826, plain, (![A_124, B_125]: (r1_tarski(k1_relat_1(A_124), k1_relat_1(B_125)) | ~r1_tarski(A_124, B_125) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.22/3.02  tff(c_838, plain, (![A_124, A_35]: (r1_tarski(k1_relat_1(A_124), A_35) | ~r1_tarski(A_124, k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_32, c_826])).
% 8.22/3.02  tff(c_1018, plain, (![A_139, A_140]: (r1_tarski(k1_relat_1(A_139), A_140) | ~r1_tarski(A_139, k6_relat_1(A_140)) | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_838])).
% 8.22/3.02  tff(c_44, plain, (![B_42, A_41]: (k7_relat_1(B_42, A_41)=B_42 | ~r1_tarski(k1_relat_1(B_42), A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.22/3.02  tff(c_1091, plain, (![A_146, A_147]: (k7_relat_1(A_146, A_147)=A_146 | ~r1_tarski(A_146, k6_relat_1(A_147)) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_1018, c_44])).
% 8.22/3.02  tff(c_1116, plain, (![A_147, A_78]: (k7_relat_1(k7_relat_1(k6_relat_1(A_147), A_78), A_147)=k7_relat_1(k6_relat_1(A_147), A_78) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_147), A_78)) | ~v1_relat_1(k6_relat_1(A_147)))), inference(resolution, [status(thm)], [c_289, c_1091])).
% 8.22/3.02  tff(c_1151, plain, (![A_147, A_78]: (k7_relat_1(k7_relat_1(k6_relat_1(A_147), A_78), A_147)=k7_relat_1(k6_relat_1(A_147), A_78))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_378, c_1116])).
% 8.22/3.02  tff(c_4284, plain, (![A_147, A_78]: (r1_tarski(k7_relat_1(k6_relat_1(A_147), A_78), k7_relat_1(k6_relat_1(A_78), A_147)))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_4225])).
% 8.22/3.02  tff(c_4377, plain, (![A_238, A_239]: (r1_tarski(k7_relat_1(k6_relat_1(A_238), A_239), k7_relat_1(k6_relat_1(A_239), A_238)))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_4225])).
% 8.22/3.02  tff(c_4379, plain, (![A_239, A_238]: (k6_relat_1(k7_relat_1(k6_relat_1(A_239), A_238))=k6_relat_1(k7_relat_1(k6_relat_1(A_238), A_239)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_239), A_238), k7_relat_1(k6_relat_1(A_238), A_239)))), inference(resolution, [status(thm)], [c_4377, c_2417])).
% 8.22/3.02  tff(c_4553, plain, (![A_243, A_242]: (k6_relat_1(k7_relat_1(k6_relat_1(A_243), A_242))=k6_relat_1(k7_relat_1(k6_relat_1(A_242), A_243)))), inference(demodulation, [status(thm), theory('equality')], [c_4284, c_4379])).
% 8.22/3.02  tff(c_4894, plain, (![A_243, A_242]: (k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_243), A_242)))=k7_relat_1(k6_relat_1(A_242), A_243))), inference(superposition, [status(thm), theory('equality')], [c_4553, c_32])).
% 8.22/3.02  tff(c_11297, plain, (![A_243, A_242]: (k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_243, A_242))))=k7_relat_1(k6_relat_1(A_242), A_243))), inference(demodulation, [status(thm), theory('equality')], [c_8903, c_4894])).
% 8.22/3.02  tff(c_11300, plain, (![A_242, A_243]: (k7_relat_1(k6_relat_1(A_242), A_243)=k6_relat_1(k3_xboole_0(A_243, A_242)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_11297])).
% 8.22/3.02  tff(c_48, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.22/3.02  tff(c_296, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_48])).
% 8.22/3.02  tff(c_312, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_296])).
% 8.22/3.02  tff(c_11726, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11300, c_312])).
% 8.22/3.02  tff(c_11748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_11726])).
% 8.22/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/3.02  
% 8.22/3.02  Inference rules
% 8.22/3.02  ----------------------
% 8.22/3.02  #Ref     : 0
% 8.22/3.02  #Sup     : 2765
% 8.22/3.02  #Fact    : 0
% 8.22/3.02  #Define  : 0
% 8.22/3.02  #Split   : 2
% 8.22/3.02  #Chain   : 0
% 8.22/3.02  #Close   : 0
% 8.22/3.02  
% 8.22/3.02  Ordering : KBO
% 8.22/3.02  
% 8.22/3.02  Simplification rules
% 8.22/3.02  ----------------------
% 8.22/3.02  #Subsume      : 366
% 8.22/3.02  #Demod        : 2868
% 8.22/3.02  #Tautology    : 1045
% 8.22/3.02  #SimpNegUnit  : 0
% 8.22/3.02  #BackRed      : 64
% 8.22/3.02  
% 8.22/3.02  #Partial instantiations: 0
% 8.22/3.02  #Strategies tried      : 1
% 8.22/3.02  
% 8.22/3.02  Timing (in seconds)
% 8.22/3.02  ----------------------
% 8.22/3.02  Preprocessing        : 0.32
% 8.22/3.02  Parsing              : 0.17
% 8.22/3.02  CNF conversion       : 0.02
% 8.22/3.02  Main loop            : 1.90
% 8.22/3.02  Inferencing          : 0.52
% 8.22/3.02  Reduction            : 0.85
% 8.22/3.02  Demodulation         : 0.71
% 8.22/3.02  BG Simplification    : 0.08
% 8.22/3.02  Subsumption          : 0.34
% 8.22/3.02  Abstraction          : 0.11
% 8.22/3.02  MUC search           : 0.00
% 8.22/3.02  Cooper               : 0.00
% 8.22/3.02  Total                : 2.26
% 8.22/3.02  Index Insertion      : 0.00
% 8.22/3.02  Index Deletion       : 0.00
% 8.22/3.02  Index Matching       : 0.00
% 8.22/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
