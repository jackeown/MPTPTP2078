%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:25 EST 2020

% Result     : Theorem 13.66s
% Output     : CNFRefutation 13.75s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 428 expanded)
%              Number of leaves         :   31 ( 162 expanded)
%              Depth                    :   15
%              Number of atoms          :  176 ( 653 expanded)
%              Number of equality atoms :   66 ( 295 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_28] : k1_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_662,plain,(
    ! [B_85,A_86] :
      ( k7_relat_1(B_85,k3_xboole_0(k1_relat_1(B_85),A_86)) = k7_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_319,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(k6_relat_1(A_69),B_70) = k7_relat_1(B_70,A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k5_relat_1(B_30,k6_relat_1(A_29)),B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_334,plain,(
    ! [A_29,A_69] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_29),A_69),k6_relat_1(A_69))
      | ~ v1_relat_1(k6_relat_1(A_69))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_34])).

tff(c_357,plain,(
    ! [A_29,A_69] : r1_tarski(k7_relat_1(k6_relat_1(A_29),A_69),k6_relat_1(A_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_334])).

tff(c_669,plain,(
    ! [A_29,A_86] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_29),A_86),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_29)),A_86)))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_357])).

tff(c_698,plain,(
    ! [A_29,A_86] : r1_tarski(k7_relat_1(k6_relat_1(A_29),A_86),k6_relat_1(k3_xboole_0(A_29,A_86))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28,c_669])).

tff(c_12,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_148,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(B_54,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_99])).

tff(c_16,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_154,plain,(
    ! [B_54,A_53] : k3_xboole_0(B_54,A_53) = k3_xboole_0(A_53,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_16])).

tff(c_30,plain,(
    ! [A_28] : k2_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_33] :
      ( k5_relat_1(A_33,k6_relat_1(k2_relat_1(A_33))) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_330,plain,(
    ! [A_69] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_69))),A_69) = k6_relat_1(A_69)
      | ~ v1_relat_1(k6_relat_1(A_69))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_69)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_38])).

tff(c_355,plain,(
    ! [A_69] : k7_relat_1(k6_relat_1(A_69),A_69) = k6_relat_1(A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_30,c_330])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k3_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_114])).

tff(c_695,plain,(
    ! [A_28,A_86] :
      ( k7_relat_1(k6_relat_1(A_28),k3_xboole_0(A_28,A_86)) = k7_relat_1(k6_relat_1(A_28),A_86)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_662])).

tff(c_1757,plain,(
    ! [A_118,A_119] : k7_relat_1(k6_relat_1(A_118),k3_xboole_0(A_118,A_119)) = k7_relat_1(k6_relat_1(A_118),A_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_695])).

tff(c_1806,plain,(
    ! [A_3,B_4] : k7_relat_1(k6_relat_1(k3_xboole_0(A_3,B_4)),k3_xboole_0(A_3,B_4)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_3,B_4)),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_1757])).

tff(c_2320,plain,(
    ! [A_140,B_141] : k7_relat_1(k6_relat_1(k3_xboole_0(A_140,B_141)),A_140) = k6_relat_1(k3_xboole_0(A_140,B_141)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_1806])).

tff(c_2389,plain,(
    ! [B_54,A_53] : k7_relat_1(k6_relat_1(k3_xboole_0(B_54,A_53)),A_53) = k6_relat_1(k3_xboole_0(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_2320])).

tff(c_703,plain,(
    ! [A_28,A_86] : k7_relat_1(k6_relat_1(A_28),k3_xboole_0(A_28,A_86)) = k7_relat_1(k6_relat_1(A_28),A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_695])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_389,plain,(
    ! [A_74,B_75] : k3_xboole_0(k3_xboole_0(A_74,B_75),A_74) = k3_xboole_0(A_74,B_75) ),
    inference(resolution,[status(thm)],[c_8,c_114])).

tff(c_392,plain,(
    ! [A_74,B_75] : k3_xboole_0(k3_xboole_0(A_74,B_75),k3_xboole_0(A_74,B_75)) = k3_xboole_0(k3_xboole_0(A_74,B_75),A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_121])).

tff(c_444,plain,(
    ! [A_76,B_77] : k3_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_122,c_392])).

tff(c_480,plain,(
    ! [B_54,A_53] : k3_xboole_0(B_54,k3_xboole_0(A_53,B_54)) = k3_xboole_0(B_54,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_444])).

tff(c_676,plain,(
    ! [B_85,A_53] :
      ( k7_relat_1(B_85,k3_xboole_0(k1_relat_1(B_85),A_53)) = k7_relat_1(B_85,k3_xboole_0(A_53,k1_relat_1(B_85)))
      | ~ v1_relat_1(B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_662])).

tff(c_32,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_29),B_30),B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1340,plain,(
    ! [B_105,A_106] :
      ( r1_tarski(k7_relat_1(B_105,A_106),B_105)
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_32])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1345,plain,(
    ! [B_105,A_106] :
      ( k3_xboole_0(k7_relat_1(B_105,A_106),B_105) = k7_relat_1(B_105,A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_1340,c_10])).

tff(c_2115,plain,(
    ! [B_132,A_133] :
      ( k3_xboole_0(B_132,k7_relat_1(B_132,A_133)) = k7_relat_1(B_132,A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1345])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2273,plain,(
    ! [B_136,A_137] :
      ( v1_relat_1(k7_relat_1(B_136,A_137))
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2115,c_20])).

tff(c_2276,plain,(
    ! [A_28,A_86] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_28),A_86))
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_2273])).

tff(c_2293,plain,(
    ! [A_28,A_86] : v1_relat_1(k7_relat_1(k6_relat_1(A_28),A_86)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_2276])).

tff(c_2193,plain,(
    ! [A_28,A_86] :
      ( k3_xboole_0(k6_relat_1(A_28),k7_relat_1(k6_relat_1(A_28),A_86)) = k7_relat_1(k6_relat_1(A_28),k3_xboole_0(A_28,A_86))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_2115])).

tff(c_18391,plain,(
    ! [A_346,A_347] : k3_xboole_0(k6_relat_1(A_346),k7_relat_1(k6_relat_1(A_346),A_347)) = k7_relat_1(k6_relat_1(A_346),A_347) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_703,c_2193])).

tff(c_40,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(k6_relat_1(A_34),B_35) = k7_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_257,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_63),B_64),B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_262,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(k5_relat_1(k6_relat_1(A_63),B_64),B_64) = k5_relat_1(k6_relat_1(A_63),B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_257,c_10])).

tff(c_13263,plain,(
    ! [B_295,A_296] :
      ( k3_xboole_0(B_295,k5_relat_1(k6_relat_1(A_296),B_295)) = k5_relat_1(k6_relat_1(A_296),B_295)
      | ~ v1_relat_1(B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_262])).

tff(c_13501,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(k6_relat_1(A_34),B_35) = k3_xboole_0(B_35,k7_relat_1(B_35,A_34))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_13263])).

tff(c_18413,plain,(
    ! [A_347,A_346] :
      ( k5_relat_1(k6_relat_1(A_347),k6_relat_1(A_346)) = k7_relat_1(k6_relat_1(A_346),A_347)
      | ~ v1_relat_1(k6_relat_1(A_346))
      | ~ v1_relat_1(k6_relat_1(A_346)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18391,c_13501])).

tff(c_18699,plain,(
    ! [A_347,A_346] : k5_relat_1(k6_relat_1(A_347),k6_relat_1(A_346)) = k7_relat_1(k6_relat_1(A_346),A_347) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_18413])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,k3_xboole_0(k1_relat_1(B_20),A_19)) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_811,plain,(
    ! [C_89,A_90,B_91] :
      ( k7_relat_1(k7_relat_1(C_89,A_90),B_91) = k7_relat_1(C_89,k3_xboole_0(A_90,B_91))
      | ~ v1_relat_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_830,plain,(
    ! [B_20,A_19,B_91] :
      ( k7_relat_1(B_20,k3_xboole_0(k3_xboole_0(k1_relat_1(B_20),A_19),B_91)) = k7_relat_1(k7_relat_1(B_20,A_19),B_91)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_811])).

tff(c_6494,plain,(
    ! [A_222,B_223] : k7_relat_1(k6_relat_1(A_222),k3_xboole_0(B_223,A_222)) = k7_relat_1(k6_relat_1(A_222),B_223) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_1757])).

tff(c_6579,plain,(
    ! [B_91,A_19] :
      ( k7_relat_1(k6_relat_1(B_91),k3_xboole_0(k1_relat_1(k6_relat_1(B_91)),A_19)) = k7_relat_1(k7_relat_1(k6_relat_1(B_91),A_19),B_91)
      | ~ v1_relat_1(k6_relat_1(B_91))
      | ~ v1_relat_1(k6_relat_1(B_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_6494])).

tff(c_6675,plain,(
    ! [B_91,A_19] : k7_relat_1(k7_relat_1(k6_relat_1(B_91),A_19),B_91) = k7_relat_1(k6_relat_1(B_91),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_703,c_28,c_6579])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2528,plain,(
    ! [A_146,B_147] :
      ( k5_relat_1(k6_relat_1(A_146),B_147) = B_147
      | ~ r1_tarski(B_147,k5_relat_1(k6_relat_1(A_146),B_147))
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_257,c_2])).

tff(c_19508,plain,(
    ! [A_352,B_353] :
      ( k5_relat_1(k6_relat_1(A_352),B_353) = B_353
      | ~ r1_tarski(B_353,k7_relat_1(B_353,A_352))
      | ~ v1_relat_1(B_353)
      | ~ v1_relat_1(B_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2528])).

tff(c_19526,plain,(
    ! [B_91,A_19] :
      ( k5_relat_1(k6_relat_1(B_91),k7_relat_1(k6_relat_1(B_91),A_19)) = k7_relat_1(k6_relat_1(B_91),A_19)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(B_91),A_19),k7_relat_1(k6_relat_1(B_91),A_19))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_91),A_19))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_91),A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6675,c_19508])).

tff(c_19573,plain,(
    ! [B_91,A_19] : k5_relat_1(k6_relat_1(B_91),k7_relat_1(k6_relat_1(B_91),A_19)) = k7_relat_1(k6_relat_1(B_91),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2293,c_2293,c_6,c_19526])).

tff(c_870,plain,(
    ! [A_94,B_95,C_96] :
      ( k5_relat_1(k5_relat_1(A_94,B_95),C_96) = k5_relat_1(A_94,k5_relat_1(B_95,C_96))
      | ~ v1_relat_1(C_96)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_884,plain,(
    ! [A_94,B_95,A_29] :
      ( r1_tarski(k5_relat_1(A_94,k5_relat_1(B_95,k6_relat_1(A_29))),k5_relat_1(A_94,B_95))
      | ~ v1_relat_1(k5_relat_1(A_94,B_95))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_34])).

tff(c_5221,plain,(
    ! [A_199,B_200,A_201] :
      ( r1_tarski(k5_relat_1(A_199,k5_relat_1(B_200,k6_relat_1(A_201))),k5_relat_1(A_199,B_200))
      | ~ v1_relat_1(k5_relat_1(A_199,B_200))
      | ~ v1_relat_1(B_200)
      | ~ v1_relat_1(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_884])).

tff(c_5281,plain,(
    ! [A_199,A_201,A_34] :
      ( r1_tarski(k5_relat_1(A_199,k7_relat_1(k6_relat_1(A_201),A_34)),k5_relat_1(A_199,k6_relat_1(A_34)))
      | ~ v1_relat_1(k5_relat_1(A_199,k6_relat_1(A_34)))
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(A_199)
      | ~ v1_relat_1(k6_relat_1(A_201)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5221])).

tff(c_37060,plain,(
    ! [A_470,A_471,A_472] :
      ( r1_tarski(k5_relat_1(A_470,k7_relat_1(k6_relat_1(A_471),A_472)),k5_relat_1(A_470,k6_relat_1(A_472)))
      | ~ v1_relat_1(k5_relat_1(A_470,k6_relat_1(A_472)))
      | ~ v1_relat_1(A_470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_5281])).

tff(c_37111,plain,(
    ! [B_91,A_19] :
      ( r1_tarski(k7_relat_1(k6_relat_1(B_91),A_19),k5_relat_1(k6_relat_1(B_91),k6_relat_1(A_19)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(B_91),k6_relat_1(A_19)))
      | ~ v1_relat_1(k6_relat_1(B_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19573,c_37060])).

tff(c_37345,plain,(
    ! [B_473,A_474] : r1_tarski(k7_relat_1(k6_relat_1(B_473),A_474),k7_relat_1(k6_relat_1(A_474),B_473)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2293,c_18699,c_18699,c_37111])).

tff(c_37383,plain,(
    ! [A_53,A_474] :
      ( r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_53,k1_relat_1(k6_relat_1(A_474)))),A_474),k7_relat_1(k6_relat_1(A_474),k3_xboole_0(k1_relat_1(k6_relat_1(A_474)),A_53)))
      | ~ v1_relat_1(k6_relat_1(A_474)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_37345])).

tff(c_38290,plain,(
    ! [A_477,A_478] : r1_tarski(k6_relat_1(k3_xboole_0(A_477,A_478)),k7_relat_1(k6_relat_1(A_477),A_478)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2389,c_703,c_28,c_28,c_37383])).

tff(c_38297,plain,(
    ! [A_477,A_478] :
      ( k7_relat_1(k6_relat_1(A_477),A_478) = k6_relat_1(k3_xboole_0(A_477,A_478))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_477),A_478),k6_relat_1(k3_xboole_0(A_477,A_478))) ) ),
    inference(resolution,[status(thm)],[c_38290,c_2])).

tff(c_38528,plain,(
    ! [A_477,A_478] : k7_relat_1(k6_relat_1(A_477),A_478) = k6_relat_1(k3_xboole_0(A_477,A_478)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_38297])).

tff(c_42,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_340,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_42])).

tff(c_359,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_340])).

tff(c_39336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38528,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.66/6.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.66/6.81  
% 13.66/6.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.66/6.81  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 13.66/6.81  
% 13.66/6.81  %Foreground sorts:
% 13.66/6.81  
% 13.66/6.81  
% 13.66/6.81  %Background operators:
% 13.66/6.81  
% 13.66/6.81  
% 13.66/6.81  %Foreground operators:
% 13.66/6.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.66/6.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.66/6.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.66/6.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.66/6.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.66/6.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.66/6.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.66/6.81  tff('#skF_2', type, '#skF_2': $i).
% 13.66/6.81  tff('#skF_1', type, '#skF_1': $i).
% 13.66/6.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.66/6.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.66/6.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.66/6.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.66/6.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.66/6.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.66/6.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.66/6.81  
% 13.75/6.83  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 13.75/6.83  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.75/6.83  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 13.75/6.83  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 13.75/6.83  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 13.75/6.83  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.75/6.83  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 13.75/6.83  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 13.75/6.83  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.75/6.83  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.75/6.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.75/6.83  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 13.75/6.83  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 13.75/6.83  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 13.75/6.83  tff(f_94, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 13.75/6.83  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.75/6.83  tff(c_28, plain, (![A_28]: (k1_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.75/6.83  tff(c_662, plain, (![B_85, A_86]: (k7_relat_1(B_85, k3_xboole_0(k1_relat_1(B_85), A_86))=k7_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.75/6.83  tff(c_319, plain, (![A_69, B_70]: (k5_relat_1(k6_relat_1(A_69), B_70)=k7_relat_1(B_70, A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.75/6.83  tff(c_34, plain, (![B_30, A_29]: (r1_tarski(k5_relat_1(B_30, k6_relat_1(A_29)), B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.75/6.83  tff(c_334, plain, (![A_29, A_69]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_69), k6_relat_1(A_69)) | ~v1_relat_1(k6_relat_1(A_69)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_319, c_34])).
% 13.75/6.83  tff(c_357, plain, (![A_29, A_69]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_69), k6_relat_1(A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_334])).
% 13.75/6.83  tff(c_669, plain, (![A_29, A_86]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_86), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_29)), A_86))) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_662, c_357])).
% 13.75/6.83  tff(c_698, plain, (![A_29, A_86]: (r1_tarski(k7_relat_1(k6_relat_1(A_29), A_86), k6_relat_1(k3_xboole_0(A_29, A_86))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28, c_669])).
% 13.75/6.83  tff(c_12, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.75/6.83  tff(c_99, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.75/6.83  tff(c_148, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(B_54, A_53))), inference(superposition, [status(thm), theory('equality')], [c_12, c_99])).
% 13.75/6.83  tff(c_16, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.75/6.83  tff(c_154, plain, (![B_54, A_53]: (k3_xboole_0(B_54, A_53)=k3_xboole_0(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_148, c_16])).
% 13.75/6.83  tff(c_30, plain, (![A_28]: (k2_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.75/6.83  tff(c_38, plain, (![A_33]: (k5_relat_1(A_33, k6_relat_1(k2_relat_1(A_33)))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.75/6.83  tff(c_330, plain, (![A_69]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_69))), A_69)=k6_relat_1(A_69) | ~v1_relat_1(k6_relat_1(A_69)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_69)))))), inference(superposition, [status(thm), theory('equality')], [c_319, c_38])).
% 13.75/6.83  tff(c_355, plain, (![A_69]: (k7_relat_1(k6_relat_1(A_69), A_69)=k6_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_30, c_330])).
% 13.75/6.83  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.75/6.83  tff(c_114, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.75/6.83  tff(c_121, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_114])).
% 13.75/6.83  tff(c_695, plain, (![A_28, A_86]: (k7_relat_1(k6_relat_1(A_28), k3_xboole_0(A_28, A_86))=k7_relat_1(k6_relat_1(A_28), A_86) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_662])).
% 13.75/6.83  tff(c_1757, plain, (![A_118, A_119]: (k7_relat_1(k6_relat_1(A_118), k3_xboole_0(A_118, A_119))=k7_relat_1(k6_relat_1(A_118), A_119))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_695])).
% 13.75/6.83  tff(c_1806, plain, (![A_3, B_4]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_3, B_4)), k3_xboole_0(A_3, B_4))=k7_relat_1(k6_relat_1(k3_xboole_0(A_3, B_4)), A_3))), inference(superposition, [status(thm), theory('equality')], [c_121, c_1757])).
% 13.75/6.83  tff(c_2320, plain, (![A_140, B_141]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_140, B_141)), A_140)=k6_relat_1(k3_xboole_0(A_140, B_141)))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_1806])).
% 13.75/6.83  tff(c_2389, plain, (![B_54, A_53]: (k7_relat_1(k6_relat_1(k3_xboole_0(B_54, A_53)), A_53)=k6_relat_1(k3_xboole_0(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_2320])).
% 13.75/6.83  tff(c_703, plain, (![A_28, A_86]: (k7_relat_1(k6_relat_1(A_28), k3_xboole_0(A_28, A_86))=k7_relat_1(k6_relat_1(A_28), A_86))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_695])).
% 13.75/6.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.75/6.83  tff(c_122, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_114])).
% 13.75/6.83  tff(c_389, plain, (![A_74, B_75]: (k3_xboole_0(k3_xboole_0(A_74, B_75), A_74)=k3_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_8, c_114])).
% 13.75/6.83  tff(c_392, plain, (![A_74, B_75]: (k3_xboole_0(k3_xboole_0(A_74, B_75), k3_xboole_0(A_74, B_75))=k3_xboole_0(k3_xboole_0(A_74, B_75), A_74))), inference(superposition, [status(thm), theory('equality')], [c_389, c_121])).
% 13.75/6.83  tff(c_444, plain, (![A_76, B_77]: (k3_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_122, c_392])).
% 13.75/6.83  tff(c_480, plain, (![B_54, A_53]: (k3_xboole_0(B_54, k3_xboole_0(A_53, B_54))=k3_xboole_0(B_54, A_53))), inference(superposition, [status(thm), theory('equality')], [c_154, c_444])).
% 13.75/6.83  tff(c_676, plain, (![B_85, A_53]: (k7_relat_1(B_85, k3_xboole_0(k1_relat_1(B_85), A_53))=k7_relat_1(B_85, k3_xboole_0(A_53, k1_relat_1(B_85))) | ~v1_relat_1(B_85))), inference(superposition, [status(thm), theory('equality')], [c_480, c_662])).
% 13.75/6.83  tff(c_32, plain, (![A_29, B_30]: (r1_tarski(k5_relat_1(k6_relat_1(A_29), B_30), B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.75/6.83  tff(c_1340, plain, (![B_105, A_106]: (r1_tarski(k7_relat_1(B_105, A_106), B_105) | ~v1_relat_1(B_105) | ~v1_relat_1(B_105))), inference(superposition, [status(thm), theory('equality')], [c_319, c_32])).
% 13.75/6.83  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.75/6.83  tff(c_1345, plain, (![B_105, A_106]: (k3_xboole_0(k7_relat_1(B_105, A_106), B_105)=k7_relat_1(B_105, A_106) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_1340, c_10])).
% 13.75/6.83  tff(c_2115, plain, (![B_132, A_133]: (k3_xboole_0(B_132, k7_relat_1(B_132, A_133))=k7_relat_1(B_132, A_133) | ~v1_relat_1(B_132))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1345])).
% 13.75/6.83  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k3_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.75/6.83  tff(c_2273, plain, (![B_136, A_137]: (v1_relat_1(k7_relat_1(B_136, A_137)) | ~v1_relat_1(B_136) | ~v1_relat_1(B_136))), inference(superposition, [status(thm), theory('equality')], [c_2115, c_20])).
% 13.75/6.83  tff(c_2276, plain, (![A_28, A_86]: (v1_relat_1(k7_relat_1(k6_relat_1(A_28), A_86)) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_703, c_2273])).
% 13.75/6.83  tff(c_2293, plain, (![A_28, A_86]: (v1_relat_1(k7_relat_1(k6_relat_1(A_28), A_86)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_2276])).
% 13.75/6.83  tff(c_2193, plain, (![A_28, A_86]: (k3_xboole_0(k6_relat_1(A_28), k7_relat_1(k6_relat_1(A_28), A_86))=k7_relat_1(k6_relat_1(A_28), k3_xboole_0(A_28, A_86)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_703, c_2115])).
% 13.75/6.83  tff(c_18391, plain, (![A_346, A_347]: (k3_xboole_0(k6_relat_1(A_346), k7_relat_1(k6_relat_1(A_346), A_347))=k7_relat_1(k6_relat_1(A_346), A_347))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_703, c_2193])).
% 13.75/6.83  tff(c_40, plain, (![A_34, B_35]: (k5_relat_1(k6_relat_1(A_34), B_35)=k7_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.75/6.83  tff(c_257, plain, (![A_63, B_64]: (r1_tarski(k5_relat_1(k6_relat_1(A_63), B_64), B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.75/6.83  tff(c_262, plain, (![A_63, B_64]: (k3_xboole_0(k5_relat_1(k6_relat_1(A_63), B_64), B_64)=k5_relat_1(k6_relat_1(A_63), B_64) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_257, c_10])).
% 13.75/6.83  tff(c_13263, plain, (![B_295, A_296]: (k3_xboole_0(B_295, k5_relat_1(k6_relat_1(A_296), B_295))=k5_relat_1(k6_relat_1(A_296), B_295) | ~v1_relat_1(B_295))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_262])).
% 13.75/6.83  tff(c_13501, plain, (![A_34, B_35]: (k5_relat_1(k6_relat_1(A_34), B_35)=k3_xboole_0(B_35, k7_relat_1(B_35, A_34)) | ~v1_relat_1(B_35) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_40, c_13263])).
% 13.75/6.83  tff(c_18413, plain, (![A_347, A_346]: (k5_relat_1(k6_relat_1(A_347), k6_relat_1(A_346))=k7_relat_1(k6_relat_1(A_346), A_347) | ~v1_relat_1(k6_relat_1(A_346)) | ~v1_relat_1(k6_relat_1(A_346)))), inference(superposition, [status(thm), theory('equality')], [c_18391, c_13501])).
% 13.75/6.83  tff(c_18699, plain, (![A_347, A_346]: (k5_relat_1(k6_relat_1(A_347), k6_relat_1(A_346))=k7_relat_1(k6_relat_1(A_346), A_347))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_18413])).
% 13.75/6.83  tff(c_24, plain, (![B_20, A_19]: (k7_relat_1(B_20, k3_xboole_0(k1_relat_1(B_20), A_19))=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.75/6.83  tff(c_811, plain, (![C_89, A_90, B_91]: (k7_relat_1(k7_relat_1(C_89, A_90), B_91)=k7_relat_1(C_89, k3_xboole_0(A_90, B_91)) | ~v1_relat_1(C_89))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.75/6.83  tff(c_830, plain, (![B_20, A_19, B_91]: (k7_relat_1(B_20, k3_xboole_0(k3_xboole_0(k1_relat_1(B_20), A_19), B_91))=k7_relat_1(k7_relat_1(B_20, A_19), B_91) | ~v1_relat_1(B_20) | ~v1_relat_1(B_20))), inference(superposition, [status(thm), theory('equality')], [c_24, c_811])).
% 13.75/6.83  tff(c_6494, plain, (![A_222, B_223]: (k7_relat_1(k6_relat_1(A_222), k3_xboole_0(B_223, A_222))=k7_relat_1(k6_relat_1(A_222), B_223))), inference(superposition, [status(thm), theory('equality')], [c_154, c_1757])).
% 13.75/6.83  tff(c_6579, plain, (![B_91, A_19]: (k7_relat_1(k6_relat_1(B_91), k3_xboole_0(k1_relat_1(k6_relat_1(B_91)), A_19))=k7_relat_1(k7_relat_1(k6_relat_1(B_91), A_19), B_91) | ~v1_relat_1(k6_relat_1(B_91)) | ~v1_relat_1(k6_relat_1(B_91)))), inference(superposition, [status(thm), theory('equality')], [c_830, c_6494])).
% 13.75/6.83  tff(c_6675, plain, (![B_91, A_19]: (k7_relat_1(k7_relat_1(k6_relat_1(B_91), A_19), B_91)=k7_relat_1(k6_relat_1(B_91), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_703, c_28, c_6579])).
% 13.75/6.83  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.75/6.83  tff(c_2528, plain, (![A_146, B_147]: (k5_relat_1(k6_relat_1(A_146), B_147)=B_147 | ~r1_tarski(B_147, k5_relat_1(k6_relat_1(A_146), B_147)) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_257, c_2])).
% 13.75/6.83  tff(c_19508, plain, (![A_352, B_353]: (k5_relat_1(k6_relat_1(A_352), B_353)=B_353 | ~r1_tarski(B_353, k7_relat_1(B_353, A_352)) | ~v1_relat_1(B_353) | ~v1_relat_1(B_353))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2528])).
% 13.75/6.83  tff(c_19526, plain, (![B_91, A_19]: (k5_relat_1(k6_relat_1(B_91), k7_relat_1(k6_relat_1(B_91), A_19))=k7_relat_1(k6_relat_1(B_91), A_19) | ~r1_tarski(k7_relat_1(k6_relat_1(B_91), A_19), k7_relat_1(k6_relat_1(B_91), A_19)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_91), A_19)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_91), A_19)))), inference(superposition, [status(thm), theory('equality')], [c_6675, c_19508])).
% 13.75/6.83  tff(c_19573, plain, (![B_91, A_19]: (k5_relat_1(k6_relat_1(B_91), k7_relat_1(k6_relat_1(B_91), A_19))=k7_relat_1(k6_relat_1(B_91), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_2293, c_2293, c_6, c_19526])).
% 13.75/6.83  tff(c_870, plain, (![A_94, B_95, C_96]: (k5_relat_1(k5_relat_1(A_94, B_95), C_96)=k5_relat_1(A_94, k5_relat_1(B_95, C_96)) | ~v1_relat_1(C_96) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.75/6.83  tff(c_884, plain, (![A_94, B_95, A_29]: (r1_tarski(k5_relat_1(A_94, k5_relat_1(B_95, k6_relat_1(A_29))), k5_relat_1(A_94, B_95)) | ~v1_relat_1(k5_relat_1(A_94, B_95)) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_870, c_34])).
% 13.75/6.83  tff(c_5221, plain, (![A_199, B_200, A_201]: (r1_tarski(k5_relat_1(A_199, k5_relat_1(B_200, k6_relat_1(A_201))), k5_relat_1(A_199, B_200)) | ~v1_relat_1(k5_relat_1(A_199, B_200)) | ~v1_relat_1(B_200) | ~v1_relat_1(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_884])).
% 13.75/6.83  tff(c_5281, plain, (![A_199, A_201, A_34]: (r1_tarski(k5_relat_1(A_199, k7_relat_1(k6_relat_1(A_201), A_34)), k5_relat_1(A_199, k6_relat_1(A_34))) | ~v1_relat_1(k5_relat_1(A_199, k6_relat_1(A_34))) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(A_199) | ~v1_relat_1(k6_relat_1(A_201)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5221])).
% 13.75/6.83  tff(c_37060, plain, (![A_470, A_471, A_472]: (r1_tarski(k5_relat_1(A_470, k7_relat_1(k6_relat_1(A_471), A_472)), k5_relat_1(A_470, k6_relat_1(A_472))) | ~v1_relat_1(k5_relat_1(A_470, k6_relat_1(A_472))) | ~v1_relat_1(A_470))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_5281])).
% 13.75/6.83  tff(c_37111, plain, (![B_91, A_19]: (r1_tarski(k7_relat_1(k6_relat_1(B_91), A_19), k5_relat_1(k6_relat_1(B_91), k6_relat_1(A_19))) | ~v1_relat_1(k5_relat_1(k6_relat_1(B_91), k6_relat_1(A_19))) | ~v1_relat_1(k6_relat_1(B_91)))), inference(superposition, [status(thm), theory('equality')], [c_19573, c_37060])).
% 13.75/6.83  tff(c_37345, plain, (![B_473, A_474]: (r1_tarski(k7_relat_1(k6_relat_1(B_473), A_474), k7_relat_1(k6_relat_1(A_474), B_473)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2293, c_18699, c_18699, c_37111])).
% 13.75/6.83  tff(c_37383, plain, (![A_53, A_474]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_53, k1_relat_1(k6_relat_1(A_474)))), A_474), k7_relat_1(k6_relat_1(A_474), k3_xboole_0(k1_relat_1(k6_relat_1(A_474)), A_53))) | ~v1_relat_1(k6_relat_1(A_474)))), inference(superposition, [status(thm), theory('equality')], [c_676, c_37345])).
% 13.75/6.83  tff(c_38290, plain, (![A_477, A_478]: (r1_tarski(k6_relat_1(k3_xboole_0(A_477, A_478)), k7_relat_1(k6_relat_1(A_477), A_478)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2389, c_703, c_28, c_28, c_37383])).
% 13.75/6.83  tff(c_38297, plain, (![A_477, A_478]: (k7_relat_1(k6_relat_1(A_477), A_478)=k6_relat_1(k3_xboole_0(A_477, A_478)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_477), A_478), k6_relat_1(k3_xboole_0(A_477, A_478))))), inference(resolution, [status(thm)], [c_38290, c_2])).
% 13.75/6.83  tff(c_38528, plain, (![A_477, A_478]: (k7_relat_1(k6_relat_1(A_477), A_478)=k6_relat_1(k3_xboole_0(A_477, A_478)))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_38297])).
% 13.75/6.83  tff(c_42, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.75/6.83  tff(c_340, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_42])).
% 13.75/6.83  tff(c_359, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_340])).
% 13.75/6.83  tff(c_39336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38528, c_359])).
% 13.75/6.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.75/6.83  
% 13.75/6.83  Inference rules
% 13.75/6.83  ----------------------
% 13.75/6.83  #Ref     : 0
% 13.75/6.83  #Sup     : 9688
% 13.75/6.83  #Fact    : 0
% 13.75/6.83  #Define  : 0
% 13.75/6.83  #Split   : 1
% 13.75/6.83  #Chain   : 0
% 13.75/6.83  #Close   : 0
% 13.75/6.83  
% 13.75/6.83  Ordering : KBO
% 13.75/6.83  
% 13.75/6.83  Simplification rules
% 13.75/6.83  ----------------------
% 13.75/6.83  #Subsume      : 1132
% 13.75/6.83  #Demod        : 11959
% 13.75/6.83  #Tautology    : 3905
% 13.75/6.83  #SimpNegUnit  : 0
% 13.75/6.83  #BackRed      : 74
% 13.75/6.83  
% 13.75/6.83  #Partial instantiations: 0
% 13.75/6.83  #Strategies tried      : 1
% 13.75/6.83  
% 13.75/6.83  Timing (in seconds)
% 13.75/6.83  ----------------------
% 13.75/6.84  Preprocessing        : 0.31
% 13.75/6.84  Parsing              : 0.16
% 13.75/6.84  CNF conversion       : 0.02
% 13.75/6.84  Main loop            : 5.74
% 13.75/6.84  Inferencing          : 1.02
% 13.75/6.84  Reduction            : 3.11
% 13.75/6.84  Demodulation         : 2.77
% 13.75/6.84  BG Simplification    : 0.15
% 13.75/6.84  Subsumption          : 1.20
% 13.75/6.84  Abstraction          : 0.28
% 13.75/6.84  MUC search           : 0.00
% 13.75/6.84  Cooper               : 0.00
% 13.75/6.84  Total                : 6.08
% 13.75/6.84  Index Insertion      : 0.00
% 13.75/6.84  Index Deletion       : 0.00
% 13.75/6.84  Index Matching       : 0.00
% 13.75/6.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
