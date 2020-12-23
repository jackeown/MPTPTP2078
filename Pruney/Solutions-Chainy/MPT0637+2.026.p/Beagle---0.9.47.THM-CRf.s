%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:27 EST 2020

% Result     : Theorem 11.20s
% Output     : CNFRefutation 11.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 543 expanded)
%              Number of leaves         :   31 ( 203 expanded)
%              Depth                    :   15
%              Number of atoms          :  172 ( 845 expanded)
%              Number of equality atoms :   51 ( 326 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_28] : k1_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,(
    ! [A_51] :
      ( k7_relat_1(A_51,k1_relat_1(A_51)) = A_51
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_128,plain,(
    ! [A_28] :
      ( k7_relat_1(k6_relat_1(A_28),A_28) = k6_relat_1(A_28)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_119])).

tff(c_132,plain,(
    ! [A_28] : k7_relat_1(k6_relat_1(A_28),A_28) = k6_relat_1(A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_128])).

tff(c_468,plain,(
    ! [C_90,A_91,B_92] :
      ( k7_relat_1(k7_relat_1(C_90,A_91),B_92) = k7_relat_1(C_90,k3_xboole_0(A_91,B_92))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_493,plain,(
    ! [A_28,B_92] :
      ( k7_relat_1(k6_relat_1(A_28),k3_xboole_0(A_28,B_92)) = k7_relat_1(k6_relat_1(A_28),B_92)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_468])).

tff(c_1035,plain,(
    ! [A_119,B_120] : k7_relat_1(k6_relat_1(A_119),k3_xboole_0(A_119,B_120)) = k7_relat_1(k6_relat_1(A_119),B_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_493])).

tff(c_233,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_relat_1(A_66),B_67) = k7_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k5_relat_1(B_30,k6_relat_1(A_29)),B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_243,plain,(
    ! [A_29,A_66] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_29),A_66),k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_30])).

tff(c_252,plain,(
    ! [A_29,A_66] : r1_tarski(k7_relat_1(k6_relat_1(A_29),A_66),k6_relat_1(A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_243])).

tff(c_1053,plain,(
    ! [A_119,B_120] : r1_tarski(k7_relat_1(k6_relat_1(A_119),B_120),k6_relat_1(k3_xboole_0(A_119,B_120))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_252])).

tff(c_16,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_17,A_15),B_16) = k7_relat_1(C_17,k3_xboole_0(A_15,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_506,plain,(
    ! [A_28,B_92] : k7_relat_1(k6_relat_1(A_28),k3_xboole_0(A_28,B_92)) = k7_relat_1(k6_relat_1(A_28),B_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_493])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(B_54,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [B_54,A_53] : k3_xboole_0(B_54,A_53) = k3_xboole_0(A_53,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_10])).

tff(c_28,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_29),B_30),B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_301,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k7_relat_1(B_74,A_75),B_74)
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_28])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_304,plain,(
    ! [B_74,A_75] :
      ( k3_xboole_0(k7_relat_1(B_74,A_75),B_74) = k7_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_301,c_2])).

tff(c_1289,plain,(
    ! [B_129,A_130] :
      ( k3_xboole_0(B_129,k7_relat_1(B_129,A_130)) = k7_relat_1(B_129,A_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_304])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1351,plain,(
    ! [B_131,A_132] :
      ( v1_relat_1(k7_relat_1(B_131,A_132))
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_14])).

tff(c_1357,plain,(
    ! [A_28,B_92] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_28),B_92))
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_1351])).

tff(c_1374,plain,(
    ! [A_28,B_92] : v1_relat_1(k7_relat_1(k6_relat_1(A_28),B_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_1357])).

tff(c_256,plain,(
    ! [A_68,A_69] : r1_tarski(k7_relat_1(k6_relat_1(A_68),A_69),k6_relat_1(A_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_243])).

tff(c_2532,plain,(
    ! [A_167,A_168] : k3_xboole_0(k7_relat_1(k6_relat_1(A_167),A_168),k6_relat_1(A_168)) = k7_relat_1(k6_relat_1(A_167),A_168) ),
    inference(resolution,[status(thm)],[c_256,c_2])).

tff(c_2605,plain,(
    ! [A_168,A_167] : k3_xboole_0(k6_relat_1(A_168),k7_relat_1(k6_relat_1(A_167),A_168)) = k7_relat_1(k6_relat_1(A_167),A_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2532])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( k5_relat_1(k6_relat_1(A_35),B_36) = k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_211,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k5_relat_1(B_59,k6_relat_1(A_60)),B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_214,plain,(
    ! [B_59,A_60] :
      ( k3_xboole_0(k5_relat_1(B_59,k6_relat_1(A_60)),B_59) = k5_relat_1(B_59,k6_relat_1(A_60))
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_211,c_2])).

tff(c_7768,plain,(
    ! [B_283,A_284] :
      ( k3_xboole_0(B_283,k5_relat_1(B_283,k6_relat_1(A_284))) = k5_relat_1(B_283,k6_relat_1(A_284))
      | ~ v1_relat_1(B_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_214])).

tff(c_7896,plain,(
    ! [A_35,A_284] :
      ( k3_xboole_0(k6_relat_1(A_35),k7_relat_1(k6_relat_1(A_284),A_35)) = k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_284))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_284)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7768])).

tff(c_7939,plain,(
    ! [A_35,A_284] : k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_284)) = k7_relat_1(k6_relat_1(A_284),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_2605,c_7896])).

tff(c_729,plain,(
    ! [A_104,B_105,C_106] :
      ( k5_relat_1(k5_relat_1(A_104,B_105),C_106) = k5_relat_1(A_104,k5_relat_1(B_105,C_106))
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_743,plain,(
    ! [A_104,B_105,A_29] :
      ( r1_tarski(k5_relat_1(A_104,k5_relat_1(B_105,k6_relat_1(A_29))),k5_relat_1(A_104,B_105))
      | ~ v1_relat_1(k5_relat_1(A_104,B_105))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_30])).

tff(c_4639,plain,(
    ! [A_212,B_213,A_214] :
      ( r1_tarski(k5_relat_1(A_212,k5_relat_1(B_213,k6_relat_1(A_214))),k5_relat_1(A_212,B_213))
      | ~ v1_relat_1(k5_relat_1(A_212,B_213))
      | ~ v1_relat_1(B_213)
      | ~ v1_relat_1(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_743])).

tff(c_4739,plain,(
    ! [A_212,A_214,A_35] :
      ( r1_tarski(k5_relat_1(A_212,k7_relat_1(k6_relat_1(A_214),A_35)),k5_relat_1(A_212,k6_relat_1(A_35)))
      | ~ v1_relat_1(k5_relat_1(A_212,k6_relat_1(A_35)))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(A_212)
      | ~ v1_relat_1(k6_relat_1(A_214)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4639])).

tff(c_22959,plain,(
    ! [A_468,A_469,A_470] :
      ( r1_tarski(k5_relat_1(A_468,k7_relat_1(k6_relat_1(A_469),A_470)),k5_relat_1(A_468,k6_relat_1(A_470)))
      | ~ v1_relat_1(k5_relat_1(A_468,k6_relat_1(A_470)))
      | ~ v1_relat_1(A_468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_4739])).

tff(c_23129,plain,(
    ! [A_469,A_470,A_35] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_469),A_470),A_35),k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_470)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_470)))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_469),A_470)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_22959])).

tff(c_23212,plain,(
    ! [A_471,A_472,A_473] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_471),A_472),A_473),k7_relat_1(k6_relat_1(A_472),A_473)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_12,c_1374,c_7939,c_7939,c_23129])).

tff(c_23347,plain,(
    ! [A_471,A_15,B_16] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_471),k3_xboole_0(A_15,B_16)),k7_relat_1(k6_relat_1(A_15),B_16))
      | ~ v1_relat_1(k6_relat_1(A_471)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_23212])).

tff(c_23419,plain,(
    ! [A_474,A_475,B_476] : r1_tarski(k7_relat_1(k6_relat_1(A_474),k3_xboole_0(A_475,B_476)),k7_relat_1(k6_relat_1(A_475),B_476)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_23347])).

tff(c_23676,plain,(
    ! [A_477,B_478] : r1_tarski(k6_relat_1(k3_xboole_0(A_477,B_478)),k7_relat_1(k6_relat_1(A_477),B_478)) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_23419])).

tff(c_23891,plain,(
    ! [A_477,B_478] : k3_xboole_0(k6_relat_1(k3_xboole_0(A_477,B_478)),k7_relat_1(k6_relat_1(A_477),B_478)) = k6_relat_1(k3_xboole_0(A_477,B_478)) ),
    inference(resolution,[status(thm)],[c_23676,c_2])).

tff(c_23912,plain,(
    ! [A_479,B_480] : k3_xboole_0(k6_relat_1(k3_xboole_0(A_479,B_480)),k7_relat_1(k6_relat_1(A_479),B_480)) = k6_relat_1(k3_xboole_0(A_479,B_480)) ),
    inference(resolution,[status(thm)],[c_23676,c_2])).

tff(c_26,plain,(
    ! [A_28] : k2_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_295,plain,(
    ! [A_72,B_73] :
      ( k5_relat_1(k6_relat_1(A_72),B_73) = B_73
      | ~ r1_tarski(k1_relat_1(B_73),A_72)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_298,plain,(
    ! [A_72,A_28] :
      ( k5_relat_1(k6_relat_1(A_72),k6_relat_1(A_28)) = k6_relat_1(A_28)
      | ~ r1_tarski(A_28,A_72)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_295])).

tff(c_347,plain,(
    ! [A_80,A_81] :
      ( k5_relat_1(k6_relat_1(A_80),k6_relat_1(A_81)) = k6_relat_1(A_81)
      | ~ r1_tarski(A_81,A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_298])).

tff(c_369,plain,(
    ! [A_81,A_35] :
      ( k7_relat_1(k6_relat_1(A_81),A_35) = k6_relat_1(A_81)
      | ~ r1_tarski(A_81,A_35)
      | ~ v1_relat_1(k6_relat_1(A_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_347])).

tff(c_379,plain,(
    ! [A_81,A_35] :
      ( k7_relat_1(k6_relat_1(A_81),A_35) = k6_relat_1(A_81)
      | ~ r1_tarski(A_81,A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_369])).

tff(c_1114,plain,(
    ! [A_123,B_124] : r1_tarski(k7_relat_1(k6_relat_1(A_123),B_124),k6_relat_1(k3_xboole_0(A_123,B_124))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_252])).

tff(c_1764,plain,(
    ! [A_143,A_144] :
      ( r1_tarski(k6_relat_1(A_143),k6_relat_1(k3_xboole_0(A_143,A_144)))
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_1114])).

tff(c_640,plain,(
    ! [A_97,B_98] :
      ( r1_tarski(k2_relat_1(A_97),k2_relat_1(B_98))
      | ~ r1_tarski(A_97,B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_649,plain,(
    ! [A_28,B_98] :
      ( r1_tarski(A_28,k2_relat_1(B_98))
      | ~ r1_tarski(k6_relat_1(A_28),B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_640])).

tff(c_656,plain,(
    ! [A_28,B_98] :
      ( r1_tarski(A_28,k2_relat_1(B_98))
      | ~ r1_tarski(k6_relat_1(A_28),B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_649])).

tff(c_1772,plain,(
    ! [A_143,A_144] :
      ( r1_tarski(A_143,k2_relat_1(k6_relat_1(k3_xboole_0(A_143,A_144))))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_143,A_144)))
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(resolution,[status(thm)],[c_1764,c_656])).

tff(c_1815,plain,(
    ! [A_145,A_146] :
      ( r1_tarski(A_145,k3_xboole_0(A_145,A_146))
      | ~ r1_tarski(A_145,A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26,c_1772])).

tff(c_1936,plain,(
    ! [A_149,B_150] :
      ( r1_tarski(A_149,k3_xboole_0(B_150,A_149))
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_1815])).

tff(c_1984,plain,(
    ! [A_149,B_150] :
      ( k3_xboole_0(A_149,k3_xboole_0(B_150,A_149)) = A_149
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_1936,c_2])).

tff(c_23984,plain,(
    ! [A_479,B_480] :
      ( k3_xboole_0(k7_relat_1(k6_relat_1(A_479),B_480),k6_relat_1(k3_xboole_0(A_479,B_480))) = k7_relat_1(k6_relat_1(A_479),B_480)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_479),B_480),k6_relat_1(k3_xboole_0(A_479,B_480))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23912,c_1984])).

tff(c_24207,plain,(
    ! [A_479,B_480] : k7_relat_1(k6_relat_1(A_479),B_480) = k6_relat_1(k3_xboole_0(A_479,B_480)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_23891,c_148,c_23984])).

tff(c_40,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_246,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_40])).

tff(c_254,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_246])).

tff(c_24408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24207,c_254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.20/4.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.20/4.65  
% 11.20/4.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.20/4.66  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 11.20/4.66  
% 11.20/4.66  %Foreground sorts:
% 11.20/4.66  
% 11.20/4.66  
% 11.20/4.66  %Background operators:
% 11.20/4.66  
% 11.20/4.66  
% 11.20/4.66  %Foreground operators:
% 11.20/4.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.20/4.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.20/4.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.20/4.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.20/4.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.20/4.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.20/4.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.20/4.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.20/4.66  tff('#skF_2', type, '#skF_2': $i).
% 11.20/4.66  tff('#skF_1', type, '#skF_1': $i).
% 11.20/4.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.20/4.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.20/4.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.20/4.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.20/4.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.20/4.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.20/4.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.20/4.66  
% 11.20/4.67  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 11.20/4.67  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.20/4.67  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 11.20/4.67  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 11.20/4.67  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 11.20/4.67  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 11.20/4.67  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.20/4.67  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.20/4.67  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.20/4.67  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 11.20/4.67  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 11.20/4.67  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 11.20/4.67  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 11.20/4.67  tff(f_101, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 11.20/4.67  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.20/4.67  tff(c_24, plain, (![A_28]: (k1_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.20/4.67  tff(c_119, plain, (![A_51]: (k7_relat_1(A_51, k1_relat_1(A_51))=A_51 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.20/4.67  tff(c_128, plain, (![A_28]: (k7_relat_1(k6_relat_1(A_28), A_28)=k6_relat_1(A_28) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_119])).
% 11.20/4.67  tff(c_132, plain, (![A_28]: (k7_relat_1(k6_relat_1(A_28), A_28)=k6_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_128])).
% 11.20/4.67  tff(c_468, plain, (![C_90, A_91, B_92]: (k7_relat_1(k7_relat_1(C_90, A_91), B_92)=k7_relat_1(C_90, k3_xboole_0(A_91, B_92)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.20/4.67  tff(c_493, plain, (![A_28, B_92]: (k7_relat_1(k6_relat_1(A_28), k3_xboole_0(A_28, B_92))=k7_relat_1(k6_relat_1(A_28), B_92) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_468])).
% 11.20/4.67  tff(c_1035, plain, (![A_119, B_120]: (k7_relat_1(k6_relat_1(A_119), k3_xboole_0(A_119, B_120))=k7_relat_1(k6_relat_1(A_119), B_120))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_493])).
% 11.20/4.67  tff(c_233, plain, (![A_66, B_67]: (k5_relat_1(k6_relat_1(A_66), B_67)=k7_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.20/4.67  tff(c_30, plain, (![B_30, A_29]: (r1_tarski(k5_relat_1(B_30, k6_relat_1(A_29)), B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.20/4.67  tff(c_243, plain, (![A_29, A_66]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_66), k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_233, c_30])).
% 11.20/4.67  tff(c_252, plain, (![A_29, A_66]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_66), k6_relat_1(A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_243])).
% 11.20/4.67  tff(c_1053, plain, (![A_119, B_120]: (r1_tarski(k7_relat_1(k6_relat_1(A_119), B_120), k6_relat_1(k3_xboole_0(A_119, B_120))))), inference(superposition, [status(thm), theory('equality')], [c_1035, c_252])).
% 11.20/4.67  tff(c_16, plain, (![C_17, A_15, B_16]: (k7_relat_1(k7_relat_1(C_17, A_15), B_16)=k7_relat_1(C_17, k3_xboole_0(A_15, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.20/4.67  tff(c_506, plain, (![A_28, B_92]: (k7_relat_1(k6_relat_1(A_28), k3_xboole_0(A_28, B_92))=k7_relat_1(k6_relat_1(A_28), B_92))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_493])).
% 11.20/4.67  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.20/4.67  tff(c_94, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.20/4.67  tff(c_142, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(B_54, A_53))), inference(superposition, [status(thm), theory('equality')], [c_4, c_94])).
% 11.20/4.67  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.20/4.67  tff(c_148, plain, (![B_54, A_53]: (k3_xboole_0(B_54, A_53)=k3_xboole_0(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_142, c_10])).
% 11.20/4.67  tff(c_28, plain, (![A_29, B_30]: (r1_tarski(k5_relat_1(k6_relat_1(A_29), B_30), B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.20/4.67  tff(c_301, plain, (![B_74, A_75]: (r1_tarski(k7_relat_1(B_74, A_75), B_74) | ~v1_relat_1(B_74) | ~v1_relat_1(B_74))), inference(superposition, [status(thm), theory('equality')], [c_233, c_28])).
% 11.20/4.67  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.20/4.67  tff(c_304, plain, (![B_74, A_75]: (k3_xboole_0(k7_relat_1(B_74, A_75), B_74)=k7_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_301, c_2])).
% 11.20/4.67  tff(c_1289, plain, (![B_129, A_130]: (k3_xboole_0(B_129, k7_relat_1(B_129, A_130))=k7_relat_1(B_129, A_130) | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_304])).
% 11.20/4.67  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.20/4.67  tff(c_1351, plain, (![B_131, A_132]: (v1_relat_1(k7_relat_1(B_131, A_132)) | ~v1_relat_1(B_131) | ~v1_relat_1(B_131))), inference(superposition, [status(thm), theory('equality')], [c_1289, c_14])).
% 11.20/4.67  tff(c_1357, plain, (![A_28, B_92]: (v1_relat_1(k7_relat_1(k6_relat_1(A_28), B_92)) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_506, c_1351])).
% 11.20/4.67  tff(c_1374, plain, (![A_28, B_92]: (v1_relat_1(k7_relat_1(k6_relat_1(A_28), B_92)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_1357])).
% 11.20/4.67  tff(c_256, plain, (![A_68, A_69]: (r1_tarski(k7_relat_1(k6_relat_1(A_68), A_69), k6_relat_1(A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_243])).
% 11.20/4.67  tff(c_2532, plain, (![A_167, A_168]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_167), A_168), k6_relat_1(A_168))=k7_relat_1(k6_relat_1(A_167), A_168))), inference(resolution, [status(thm)], [c_256, c_2])).
% 11.20/4.67  tff(c_2605, plain, (![A_168, A_167]: (k3_xboole_0(k6_relat_1(A_168), k7_relat_1(k6_relat_1(A_167), A_168))=k7_relat_1(k6_relat_1(A_167), A_168))), inference(superposition, [status(thm), theory('equality')], [c_148, c_2532])).
% 11.20/4.67  tff(c_36, plain, (![A_35, B_36]: (k5_relat_1(k6_relat_1(A_35), B_36)=k7_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.20/4.67  tff(c_211, plain, (![B_59, A_60]: (r1_tarski(k5_relat_1(B_59, k6_relat_1(A_60)), B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.20/4.67  tff(c_214, plain, (![B_59, A_60]: (k3_xboole_0(k5_relat_1(B_59, k6_relat_1(A_60)), B_59)=k5_relat_1(B_59, k6_relat_1(A_60)) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_211, c_2])).
% 11.20/4.67  tff(c_7768, plain, (![B_283, A_284]: (k3_xboole_0(B_283, k5_relat_1(B_283, k6_relat_1(A_284)))=k5_relat_1(B_283, k6_relat_1(A_284)) | ~v1_relat_1(B_283))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_214])).
% 11.20/4.67  tff(c_7896, plain, (![A_35, A_284]: (k3_xboole_0(k6_relat_1(A_35), k7_relat_1(k6_relat_1(A_284), A_35))=k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_284)) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_284)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_7768])).
% 11.20/4.67  tff(c_7939, plain, (![A_35, A_284]: (k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_284))=k7_relat_1(k6_relat_1(A_284), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_2605, c_7896])).
% 11.20/4.67  tff(c_729, plain, (![A_104, B_105, C_106]: (k5_relat_1(k5_relat_1(A_104, B_105), C_106)=k5_relat_1(A_104, k5_relat_1(B_105, C_106)) | ~v1_relat_1(C_106) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.20/4.67  tff(c_743, plain, (![A_104, B_105, A_29]: (r1_tarski(k5_relat_1(A_104, k5_relat_1(B_105, k6_relat_1(A_29))), k5_relat_1(A_104, B_105)) | ~v1_relat_1(k5_relat_1(A_104, B_105)) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_729, c_30])).
% 11.20/4.67  tff(c_4639, plain, (![A_212, B_213, A_214]: (r1_tarski(k5_relat_1(A_212, k5_relat_1(B_213, k6_relat_1(A_214))), k5_relat_1(A_212, B_213)) | ~v1_relat_1(k5_relat_1(A_212, B_213)) | ~v1_relat_1(B_213) | ~v1_relat_1(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_743])).
% 11.20/4.67  tff(c_4739, plain, (![A_212, A_214, A_35]: (r1_tarski(k5_relat_1(A_212, k7_relat_1(k6_relat_1(A_214), A_35)), k5_relat_1(A_212, k6_relat_1(A_35))) | ~v1_relat_1(k5_relat_1(A_212, k6_relat_1(A_35))) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(A_212) | ~v1_relat_1(k6_relat_1(A_214)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4639])).
% 11.20/4.67  tff(c_22959, plain, (![A_468, A_469, A_470]: (r1_tarski(k5_relat_1(A_468, k7_relat_1(k6_relat_1(A_469), A_470)), k5_relat_1(A_468, k6_relat_1(A_470))) | ~v1_relat_1(k5_relat_1(A_468, k6_relat_1(A_470))) | ~v1_relat_1(A_468))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_4739])).
% 11.20/4.67  tff(c_23129, plain, (![A_469, A_470, A_35]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_469), A_470), A_35), k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_470))) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_470))) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_469), A_470)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_22959])).
% 11.20/4.67  tff(c_23212, plain, (![A_471, A_472, A_473]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_471), A_472), A_473), k7_relat_1(k6_relat_1(A_472), A_473)))), inference(demodulation, [status(thm), theory('equality')], [c_1374, c_12, c_1374, c_7939, c_7939, c_23129])).
% 11.20/4.67  tff(c_23347, plain, (![A_471, A_15, B_16]: (r1_tarski(k7_relat_1(k6_relat_1(A_471), k3_xboole_0(A_15, B_16)), k7_relat_1(k6_relat_1(A_15), B_16)) | ~v1_relat_1(k6_relat_1(A_471)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_23212])).
% 11.20/4.67  tff(c_23419, plain, (![A_474, A_475, B_476]: (r1_tarski(k7_relat_1(k6_relat_1(A_474), k3_xboole_0(A_475, B_476)), k7_relat_1(k6_relat_1(A_475), B_476)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_23347])).
% 11.20/4.67  tff(c_23676, plain, (![A_477, B_478]: (r1_tarski(k6_relat_1(k3_xboole_0(A_477, B_478)), k7_relat_1(k6_relat_1(A_477), B_478)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_23419])).
% 11.20/4.67  tff(c_23891, plain, (![A_477, B_478]: (k3_xboole_0(k6_relat_1(k3_xboole_0(A_477, B_478)), k7_relat_1(k6_relat_1(A_477), B_478))=k6_relat_1(k3_xboole_0(A_477, B_478)))), inference(resolution, [status(thm)], [c_23676, c_2])).
% 11.20/4.67  tff(c_23912, plain, (![A_479, B_480]: (k3_xboole_0(k6_relat_1(k3_xboole_0(A_479, B_480)), k7_relat_1(k6_relat_1(A_479), B_480))=k6_relat_1(k3_xboole_0(A_479, B_480)))), inference(resolution, [status(thm)], [c_23676, c_2])).
% 11.20/4.67  tff(c_26, plain, (![A_28]: (k2_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.20/4.67  tff(c_295, plain, (![A_72, B_73]: (k5_relat_1(k6_relat_1(A_72), B_73)=B_73 | ~r1_tarski(k1_relat_1(B_73), A_72) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.20/4.67  tff(c_298, plain, (![A_72, A_28]: (k5_relat_1(k6_relat_1(A_72), k6_relat_1(A_28))=k6_relat_1(A_28) | ~r1_tarski(A_28, A_72) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_295])).
% 11.20/4.67  tff(c_347, plain, (![A_80, A_81]: (k5_relat_1(k6_relat_1(A_80), k6_relat_1(A_81))=k6_relat_1(A_81) | ~r1_tarski(A_81, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_298])).
% 11.20/4.67  tff(c_369, plain, (![A_81, A_35]: (k7_relat_1(k6_relat_1(A_81), A_35)=k6_relat_1(A_81) | ~r1_tarski(A_81, A_35) | ~v1_relat_1(k6_relat_1(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_347])).
% 11.20/4.67  tff(c_379, plain, (![A_81, A_35]: (k7_relat_1(k6_relat_1(A_81), A_35)=k6_relat_1(A_81) | ~r1_tarski(A_81, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_369])).
% 11.20/4.67  tff(c_1114, plain, (![A_123, B_124]: (r1_tarski(k7_relat_1(k6_relat_1(A_123), B_124), k6_relat_1(k3_xboole_0(A_123, B_124))))), inference(superposition, [status(thm), theory('equality')], [c_1035, c_252])).
% 11.20/4.67  tff(c_1764, plain, (![A_143, A_144]: (r1_tarski(k6_relat_1(A_143), k6_relat_1(k3_xboole_0(A_143, A_144))) | ~r1_tarski(A_143, A_144))), inference(superposition, [status(thm), theory('equality')], [c_379, c_1114])).
% 11.20/4.67  tff(c_640, plain, (![A_97, B_98]: (r1_tarski(k2_relat_1(A_97), k2_relat_1(B_98)) | ~r1_tarski(A_97, B_98) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.20/4.67  tff(c_649, plain, (![A_28, B_98]: (r1_tarski(A_28, k2_relat_1(B_98)) | ~r1_tarski(k6_relat_1(A_28), B_98) | ~v1_relat_1(B_98) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_640])).
% 11.20/4.67  tff(c_656, plain, (![A_28, B_98]: (r1_tarski(A_28, k2_relat_1(B_98)) | ~r1_tarski(k6_relat_1(A_28), B_98) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_649])).
% 11.20/4.67  tff(c_1772, plain, (![A_143, A_144]: (r1_tarski(A_143, k2_relat_1(k6_relat_1(k3_xboole_0(A_143, A_144)))) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_143, A_144))) | ~r1_tarski(A_143, A_144))), inference(resolution, [status(thm)], [c_1764, c_656])).
% 11.20/4.67  tff(c_1815, plain, (![A_145, A_146]: (r1_tarski(A_145, k3_xboole_0(A_145, A_146)) | ~r1_tarski(A_145, A_146))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26, c_1772])).
% 11.20/4.67  tff(c_1936, plain, (![A_149, B_150]: (r1_tarski(A_149, k3_xboole_0(B_150, A_149)) | ~r1_tarski(A_149, B_150))), inference(superposition, [status(thm), theory('equality')], [c_148, c_1815])).
% 11.20/4.67  tff(c_1984, plain, (![A_149, B_150]: (k3_xboole_0(A_149, k3_xboole_0(B_150, A_149))=A_149 | ~r1_tarski(A_149, B_150))), inference(resolution, [status(thm)], [c_1936, c_2])).
% 11.20/4.67  tff(c_23984, plain, (![A_479, B_480]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_479), B_480), k6_relat_1(k3_xboole_0(A_479, B_480)))=k7_relat_1(k6_relat_1(A_479), B_480) | ~r1_tarski(k7_relat_1(k6_relat_1(A_479), B_480), k6_relat_1(k3_xboole_0(A_479, B_480))))), inference(superposition, [status(thm), theory('equality')], [c_23912, c_1984])).
% 11.20/4.67  tff(c_24207, plain, (![A_479, B_480]: (k7_relat_1(k6_relat_1(A_479), B_480)=k6_relat_1(k3_xboole_0(A_479, B_480)))), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_23891, c_148, c_23984])).
% 11.20/4.67  tff(c_40, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.20/4.67  tff(c_246, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_233, c_40])).
% 11.20/4.67  tff(c_254, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_246])).
% 11.20/4.67  tff(c_24408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24207, c_254])).
% 11.20/4.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.20/4.67  
% 11.20/4.67  Inference rules
% 11.20/4.67  ----------------------
% 11.20/4.67  #Ref     : 0
% 11.20/4.67  #Sup     : 5629
% 11.20/4.67  #Fact    : 0
% 11.20/4.67  #Define  : 0
% 11.20/4.67  #Split   : 2
% 11.20/4.67  #Chain   : 0
% 11.20/4.67  #Close   : 0
% 11.20/4.67  
% 11.20/4.67  Ordering : KBO
% 11.20/4.67  
% 11.20/4.67  Simplification rules
% 11.20/4.67  ----------------------
% 11.20/4.67  #Subsume      : 856
% 11.20/4.67  #Demod        : 6795
% 11.20/4.67  #Tautology    : 2282
% 11.20/4.67  #SimpNegUnit  : 0
% 11.20/4.67  #BackRed      : 110
% 11.20/4.67  
% 11.20/4.67  #Partial instantiations: 0
% 11.20/4.67  #Strategies tried      : 1
% 11.20/4.67  
% 11.20/4.67  Timing (in seconds)
% 11.20/4.67  ----------------------
% 11.20/4.68  Preprocessing        : 0.53
% 11.20/4.68  Parsing              : 0.27
% 11.20/4.68  CNF conversion       : 0.04
% 11.20/4.68  Main loop            : 3.21
% 11.20/4.68  Inferencing          : 0.80
% 11.20/4.68  Reduction            : 1.46
% 11.20/4.68  Demodulation         : 1.23
% 11.20/4.68  BG Simplification    : 0.11
% 11.20/4.68  Subsumption          : 0.66
% 11.20/4.68  Abstraction          : 0.17
% 11.20/4.68  MUC search           : 0.00
% 11.20/4.68  Cooper               : 0.00
% 11.20/4.68  Total                : 3.79
% 11.20/4.68  Index Insertion      : 0.00
% 11.20/4.68  Index Deletion       : 0.00
% 11.20/4.68  Index Matching       : 0.00
% 11.20/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
