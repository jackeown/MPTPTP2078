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
% DateTime   : Thu Dec  3 10:03:30 EST 2020

% Result     : Theorem 22.03s
% Output     : CNFRefutation 22.24s
% Verified   : 
% Statistics : Number of formulae       :  152 (7815 expanded)
%              Number of leaves         :   31 (2753 expanded)
%              Depth                    :   29
%              Number of atoms          :  246 (14749 expanded)
%              Number of equality atoms :   97 (5408 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_40,plain,(
    ! [A_37] : v1_relat_1(k6_relat_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_167,plain,(
    ! [A_62,B_63] :
      ( k5_relat_1(k6_relat_1(A_62),B_63) = k7_relat_1(B_63,A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k5_relat_1(B_27,k6_relat_1(A_26)),B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_177,plain,(
    ! [A_26,A_62] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_26),A_62),k6_relat_1(A_62))
      | ~ v1_relat_1(k6_relat_1(A_62))
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_28])).

tff(c_204,plain,(
    ! [A_26,A_62] : r1_tarski(k7_relat_1(k6_relat_1(A_26),A_62),k6_relat_1(A_62)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_177])).

tff(c_22,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( k5_relat_1(k6_relat_1(A_35),B_36) = k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_329,plain,(
    ! [A_78,B_79] :
      ( k5_relat_1(k6_relat_1(A_78),B_79) = B_79
      | ~ r1_tarski(k1_relat_1(B_79),A_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_338,plain,(
    ! [A_78,A_25] :
      ( k5_relat_1(k6_relat_1(A_78),k6_relat_1(A_25)) = k6_relat_1(A_25)
      | ~ r1_tarski(A_25,A_78)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_329])).

tff(c_505,plain,(
    ! [A_87,A_88] :
      ( k5_relat_1(k6_relat_1(A_87),k6_relat_1(A_88)) = k6_relat_1(A_88)
      | ~ r1_tarski(A_88,A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_338])).

tff(c_546,plain,(
    ! [A_88,A_35] :
      ( k7_relat_1(k6_relat_1(A_88),A_35) = k6_relat_1(A_88)
      | ~ r1_tarski(A_88,A_35)
      | ~ v1_relat_1(k6_relat_1(A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_505])).

tff(c_587,plain,(
    ! [A_91,A_92] :
      ( k7_relat_1(k6_relat_1(A_91),A_92) = k6_relat_1(A_91)
      | ~ r1_tarski(A_91,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_546])).

tff(c_245,plain,(
    ! [B_71,A_72] :
      ( k3_xboole_0(k1_relat_1(B_71),A_72) = k1_relat_1(k7_relat_1(B_71,A_72))
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_260,plain,(
    ! [A_25,A_72] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_25),A_72)) = k3_xboole_0(A_25,A_72)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_245])).

tff(c_264,plain,(
    ! [A_25,A_72] : k1_relat_1(k7_relat_1(k6_relat_1(A_25),A_72)) = k3_xboole_0(A_25,A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_260])).

tff(c_607,plain,(
    ! [A_91,A_92] :
      ( k3_xboole_0(A_91,A_92) = k1_relat_1(k6_relat_1(A_91))
      | ~ r1_tarski(A_91,A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_264])).

tff(c_654,plain,(
    ! [A_93,A_94] :
      ( k3_xboole_0(A_93,A_94) = A_93
      | ~ r1_tarski(A_93,A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_607])).

tff(c_682,plain,(
    ! [A_26,A_62] : k3_xboole_0(k7_relat_1(k6_relat_1(A_26),A_62),k6_relat_1(A_62)) = k7_relat_1(k6_relat_1(A_26),A_62) ),
    inference(resolution,[status(thm)],[c_204,c_654])).

tff(c_2389,plain,(
    ! [B_163,A_164] :
      ( k3_xboole_0(k5_relat_1(B_163,k6_relat_1(A_164)),B_163) = k5_relat_1(B_163,k6_relat_1(A_164))
      | ~ v1_relat_1(B_163) ) ),
    inference(resolution,[status(thm)],[c_28,c_654])).

tff(c_2448,plain,(
    ! [A_164,A_35] :
      ( k3_xboole_0(k7_relat_1(k6_relat_1(A_164),A_35),k6_relat_1(A_35)) = k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_164))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2389])).

tff(c_2492,plain,(
    ! [A_165,A_166] : k5_relat_1(k6_relat_1(A_165),k6_relat_1(A_166)) = k7_relat_1(k6_relat_1(A_166),A_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_682,c_2448])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k5_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2529,plain,(
    ! [A_166,A_165] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_166),A_165))
      | ~ v1_relat_1(k6_relat_1(A_166))
      | ~ v1_relat_1(k6_relat_1(A_165)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2492,c_16])).

tff(c_2579,plain,(
    ! [A_166,A_165] : v1_relat_1(k7_relat_1(k6_relat_1(A_166),A_165)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_2529])).

tff(c_24,plain,(
    ! [A_25] : k2_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    ! [A_32] :
      ( k5_relat_1(A_32,k6_relat_1(k2_relat_1(A_32))) = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_201,plain,(
    ! [A_62] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_62))),A_62) = k6_relat_1(A_62)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_62))))
      | ~ v1_relat_1(k6_relat_1(A_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_167])).

tff(c_217,plain,(
    ! [A_62] : k7_relat_1(k6_relat_1(A_62),A_62) = k6_relat_1(A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_24,c_201])).

tff(c_265,plain,(
    ! [A_73,A_74] : k1_relat_1(k7_relat_1(k6_relat_1(A_73),A_74)) = k3_xboole_0(A_73,A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_260])).

tff(c_277,plain,(
    ! [A_62] : k3_xboole_0(A_62,A_62) = k1_relat_1(k6_relat_1(A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_265])).

tff(c_280,plain,(
    ! [A_62] : k3_xboole_0(A_62,A_62) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_277])).

tff(c_2483,plain,(
    ! [A_35,A_164] : k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_164)) = k7_relat_1(k6_relat_1(A_164),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_682,c_2448])).

tff(c_86,plain,(
    ! [A_49] :
      ( k5_relat_1(A_49,k6_relat_1(k2_relat_1(A_49))) = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_95,plain,(
    ! [A_25] :
      ( k5_relat_1(k6_relat_1(A_25),k6_relat_1(A_25)) = k6_relat_1(A_25)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_86])).

tff(c_99,plain,(
    ! [A_25] : k5_relat_1(k6_relat_1(A_25),k6_relat_1(A_25)) = k6_relat_1(A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95])).

tff(c_1047,plain,(
    ! [A_110,B_111,C_112] :
      ( k5_relat_1(k5_relat_1(A_110,B_111),C_112) = k5_relat_1(A_110,k5_relat_1(B_111,C_112))
      | ~ v1_relat_1(C_112)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1088,plain,(
    ! [A_25,C_112] :
      ( k5_relat_1(k6_relat_1(A_25),k5_relat_1(k6_relat_1(A_25),C_112)) = k5_relat_1(k6_relat_1(A_25),C_112)
      | ~ v1_relat_1(C_112)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1047])).

tff(c_13602,plain,(
    ! [A_333,C_334] :
      ( k5_relat_1(k6_relat_1(A_333),k5_relat_1(k6_relat_1(A_333),C_334)) = k5_relat_1(k6_relat_1(A_333),C_334)
      | ~ v1_relat_1(C_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_1088])).

tff(c_13753,plain,(
    ! [A_35,A_164] :
      ( k5_relat_1(k6_relat_1(A_35),k7_relat_1(k6_relat_1(A_164),A_35)) = k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_164))
      | ~ v1_relat_1(k6_relat_1(A_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2483,c_13602])).

tff(c_13831,plain,(
    ! [A_335,A_336] : k5_relat_1(k6_relat_1(A_335),k7_relat_1(k6_relat_1(A_336),A_335)) = k7_relat_1(k6_relat_1(A_336),A_335) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2483,c_13753])).

tff(c_13889,plain,(
    ! [A_336,A_335] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_336),A_335),A_335) = k7_relat_1(k6_relat_1(A_336),A_335)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_336),A_335)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13831,c_38])).

tff(c_14023,plain,(
    ! [A_337,A_338] : k7_relat_1(k7_relat_1(k6_relat_1(A_337),A_338),A_338) = k7_relat_1(k6_relat_1(A_337),A_338) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_13889])).

tff(c_36,plain,(
    ! [B_34,A_33] :
      ( k3_xboole_0(k1_relat_1(B_34),A_33) = k1_relat_1(k7_relat_1(B_34,A_33))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_494,plain,(
    ! [B_85,A_86] :
      ( k5_relat_1(B_85,k6_relat_1(A_86)) = B_85
      | ~ r1_tarski(k2_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_497,plain,(
    ! [A_25,A_86] :
      ( k5_relat_1(k6_relat_1(A_25),k6_relat_1(A_86)) = k6_relat_1(A_25)
      | ~ r1_tarski(A_25,A_86)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_494])).

tff(c_776,plain,(
    ! [A_100,A_101] :
      ( k5_relat_1(k6_relat_1(A_100),k6_relat_1(A_101)) = k6_relat_1(A_100)
      | ~ r1_tarski(A_100,A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_497])).

tff(c_792,plain,(
    ! [A_101,A_100] :
      ( k7_relat_1(k6_relat_1(A_101),A_100) = k6_relat_1(A_100)
      | ~ v1_relat_1(k6_relat_1(A_101))
      | ~ r1_tarski(A_100,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_38])).

tff(c_864,plain,(
    ! [A_102,A_103] :
      ( k7_relat_1(k6_relat_1(A_102),A_103) = k6_relat_1(A_103)
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_792])).

tff(c_887,plain,(
    ! [A_102,A_103] :
      ( k3_xboole_0(A_102,A_103) = k1_relat_1(k6_relat_1(A_103))
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_264])).

tff(c_936,plain,(
    ! [A_104,A_105] :
      ( k3_xboole_0(A_104,A_105) = A_105
      | ~ r1_tarski(A_105,A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_887])).

tff(c_971,plain,(
    ! [A_106,B_107] : k3_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k3_xboole_0(A_106,B_107) ),
    inference(resolution,[status(thm)],[c_8,c_936])).

tff(c_1005,plain,(
    ! [B_34,A_33] :
      ( k3_xboole_0(k1_relat_1(B_34),k1_relat_1(k7_relat_1(B_34,A_33))) = k3_xboole_0(k1_relat_1(B_34),A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_971])).

tff(c_14029,plain,(
    ! [A_337,A_338] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_337),A_338)),k1_relat_1(k7_relat_1(k6_relat_1(A_337),A_338))) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_337),A_338)),A_338)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_337),A_338)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14023,c_1005])).

tff(c_14149,plain,(
    ! [A_337,A_338] : k3_xboole_0(k3_xboole_0(A_337,A_338),A_338) = k3_xboole_0(A_337,A_338) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_280,c_264,c_264,c_264,c_14029])).

tff(c_254,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_71,A_72)),k1_relat_1(B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_8])).

tff(c_42604,plain,(
    ! [B_584,A_585] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_584)),k7_relat_1(B_584,A_585)) = k7_relat_1(B_584,A_585)
      | ~ v1_relat_1(k7_relat_1(B_584,A_585))
      | ~ v1_relat_1(B_584) ) ),
    inference(resolution,[status(thm)],[c_254,c_329])).

tff(c_1060,plain,(
    ! [A_110,B_111,A_26] :
      ( r1_tarski(k5_relat_1(A_110,k5_relat_1(B_111,k6_relat_1(A_26))),k5_relat_1(A_110,B_111))
      | ~ v1_relat_1(k5_relat_1(A_110,B_111))
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_28])).

tff(c_6474,plain,(
    ! [A_237,B_238,A_239] :
      ( r1_tarski(k5_relat_1(A_237,k5_relat_1(B_238,k6_relat_1(A_239))),k5_relat_1(A_237,B_238))
      | ~ v1_relat_1(k5_relat_1(A_237,B_238))
      | ~ v1_relat_1(B_238)
      | ~ v1_relat_1(A_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1060])).

tff(c_6530,plain,(
    ! [A_35,A_164,A_239] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_35),k5_relat_1(k6_relat_1(A_164),k6_relat_1(A_239))),k7_relat_1(k6_relat_1(A_164),A_35))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_164)))
      | ~ v1_relat_1(k6_relat_1(A_164))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2483,c_6474])).

tff(c_6631,plain,(
    ! [A_35,A_239,A_164] : r1_tarski(k5_relat_1(k6_relat_1(A_35),k7_relat_1(k6_relat_1(A_239),A_164)),k7_relat_1(k6_relat_1(A_164),A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_2579,c_2483,c_2483,c_6530])).

tff(c_42669,plain,(
    ! [A_239,A_585] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_239),A_585),k7_relat_1(k6_relat_1(A_585),k1_relat_1(k6_relat_1(A_239))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_239),A_585))
      | ~ v1_relat_1(k6_relat_1(A_239)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42604,c_6631])).

tff(c_42807,plain,(
    ! [A_239,A_585] : r1_tarski(k7_relat_1(k6_relat_1(A_239),A_585),k7_relat_1(k6_relat_1(A_585),A_239)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2579,c_22,c_42669])).

tff(c_42852,plain,(
    ! [A_586,A_587] : r1_tarski(k7_relat_1(k6_relat_1(A_586),A_587),k7_relat_1(k6_relat_1(A_587),A_586)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2579,c_22,c_42669])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42867,plain,(
    ! [A_587,A_586] :
      ( k7_relat_1(k6_relat_1(A_587),A_586) = k7_relat_1(k6_relat_1(A_586),A_587)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_587),A_586),k7_relat_1(k6_relat_1(A_586),A_587)) ) ),
    inference(resolution,[status(thm)],[c_42852,c_2])).

tff(c_43051,plain,(
    ! [A_589,A_588] : k7_relat_1(k6_relat_1(A_589),A_588) = k7_relat_1(k6_relat_1(A_588),A_589) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42807,c_42867])).

tff(c_688,plain,(
    ! [A_95,B_96] : k3_xboole_0(k3_xboole_0(A_95,B_96),A_95) = k3_xboole_0(A_95,B_96) ),
    inference(resolution,[status(thm)],[c_8,c_654])).

tff(c_712,plain,(
    ! [B_34,A_33] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_34,A_33)),k1_relat_1(B_34)) = k3_xboole_0(k1_relat_1(B_34),A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_688])).

tff(c_43607,plain,(
    ! [A_588,A_589] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_588),A_589)),k1_relat_1(k6_relat_1(A_589))) = k3_xboole_0(k1_relat_1(k6_relat_1(A_589)),A_588)
      | ~ v1_relat_1(k6_relat_1(A_589)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43051,c_712])).

tff(c_44091,plain,(
    ! [A_589,A_588] : k3_xboole_0(A_589,A_588) = k3_xboole_0(A_588,A_589) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14149,c_264,c_22,c_22,c_43607])).

tff(c_685,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k3_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_654])).

tff(c_576,plain,(
    ! [A_88,A_35] :
      ( k7_relat_1(k6_relat_1(A_88),A_35) = k6_relat_1(A_88)
      | ~ r1_tarski(A_88,A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_546])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_346,plain,(
    ! [B_79] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_79)),B_79) = B_79
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_329])).

tff(c_6839,plain,(
    ! [A_244,A_245,A_246] : r1_tarski(k5_relat_1(k6_relat_1(A_244),k7_relat_1(k6_relat_1(A_245),A_246)),k7_relat_1(k6_relat_1(A_246),A_244)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_2579,c_2483,c_2483,c_6530])).

tff(c_6922,plain,(
    ! [A_245,A_246] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_245),A_246),k7_relat_1(k6_relat_1(A_246),k1_relat_1(k7_relat_1(k6_relat_1(A_245),A_246))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_245),A_246)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_6839])).

tff(c_7579,plain,(
    ! [A_252,A_253] : r1_tarski(k7_relat_1(k6_relat_1(A_252),A_253),k7_relat_1(k6_relat_1(A_253),k3_xboole_0(A_252,A_253))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_264,c_6922])).

tff(c_8478,plain,(
    ! [A_263,A_264] :
      ( r1_tarski(k6_relat_1(A_263),k7_relat_1(k6_relat_1(A_264),k3_xboole_0(A_263,A_264)))
      | ~ r1_tarski(A_263,A_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_7579])).

tff(c_8609,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k6_relat_1(k3_xboole_0(A_3,B_4)),k7_relat_1(k6_relat_1(A_3),k3_xboole_0(A_3,B_4)))
      | ~ r1_tarski(k3_xboole_0(A_3,B_4),A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_8478])).

tff(c_8646,plain,(
    ! [A_265,B_266] : r1_tarski(k6_relat_1(k3_xboole_0(A_265,B_266)),k7_relat_1(k6_relat_1(A_265),k3_xboole_0(A_265,B_266))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8609])).

tff(c_236,plain,(
    ! [A_67,A_68] : r1_tarski(k7_relat_1(k6_relat_1(A_67),A_68),k6_relat_1(A_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_177])).

tff(c_242,plain,(
    ! [A_67,A_68] :
      ( k7_relat_1(k6_relat_1(A_67),A_68) = k6_relat_1(A_68)
      | ~ r1_tarski(k6_relat_1(A_68),k7_relat_1(k6_relat_1(A_67),A_68)) ) ),
    inference(resolution,[status(thm)],[c_236,c_2])).

tff(c_8861,plain,(
    ! [A_265,B_266] : k7_relat_1(k6_relat_1(A_265),k3_xboole_0(A_265,B_266)) = k6_relat_1(k3_xboole_0(A_265,B_266)) ),
    inference(resolution,[status(thm)],[c_8646,c_242])).

tff(c_44493,plain,(
    ! [A_595,A_594] : k3_xboole_0(A_595,A_594) = k3_xboole_0(A_594,A_595) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14149,c_264,c_22,c_22,c_43607])).

tff(c_6953,plain,(
    ! [A_245,A_246] : r1_tarski(k7_relat_1(k6_relat_1(A_245),A_246),k7_relat_1(k6_relat_1(A_246),k3_xboole_0(A_245,A_246))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_264,c_6922])).

tff(c_44855,plain,(
    ! [A_595,A_594] : r1_tarski(k7_relat_1(k6_relat_1(A_595),A_594),k7_relat_1(k6_relat_1(A_594),k3_xboole_0(A_594,A_595))) ),
    inference(superposition,[status(thm),theory(equality)],[c_44493,c_6953])).

tff(c_45111,plain,(
    ! [A_595,A_594] : r1_tarski(k7_relat_1(k6_relat_1(A_595),A_594),k6_relat_1(k3_xboole_0(A_594,A_595))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8861,c_44855])).

tff(c_74943,plain,(
    ! [A_754,A_755] : k7_relat_1(k6_relat_1(A_754),k3_xboole_0(A_755,A_754)) = k6_relat_1(k3_xboole_0(A_754,A_755)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44493,c_8861])).

tff(c_345,plain,(
    ! [A_78,A_25] :
      ( k5_relat_1(k6_relat_1(A_78),k6_relat_1(A_25)) = k6_relat_1(A_25)
      | ~ r1_tarski(A_25,A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_338])).

tff(c_785,plain,(
    ! [A_101,A_100] :
      ( k6_relat_1(A_101) = k6_relat_1(A_100)
      | ~ r1_tarski(A_101,A_100)
      | ~ r1_tarski(A_100,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_345])).

tff(c_42859,plain,(
    ! [A_587,A_586] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_587),A_586)) = k6_relat_1(k7_relat_1(k6_relat_1(A_586),A_587))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_587),A_586),k7_relat_1(k6_relat_1(A_586),A_587)) ) ),
    inference(resolution,[status(thm)],[c_42852,c_785])).

tff(c_61798,plain,(
    ! [A_699,A_698] : k6_relat_1(k7_relat_1(k6_relat_1(A_699),A_698)) = k6_relat_1(k7_relat_1(k6_relat_1(A_698),A_699)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42807,c_42859])).

tff(c_63086,plain,(
    ! [A_698,A_699] : k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_698),A_699))) = k7_relat_1(k6_relat_1(A_699),A_698) ),
    inference(superposition,[status(thm),theory(equality)],[c_61798,c_22])).

tff(c_74967,plain,(
    ! [A_755,A_754] : k7_relat_1(k6_relat_1(k3_xboole_0(A_755,A_754)),A_754) = k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_754,A_755)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_74943,c_63086])).

tff(c_78736,plain,(
    ! [A_772,A_773] : k7_relat_1(k6_relat_1(k3_xboole_0(A_772,A_773)),A_773) = k6_relat_1(k3_xboole_0(A_773,A_772)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_74967])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_26),B_27),B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_965,plain,(
    ! [B_27,A_26] :
      ( k3_xboole_0(B_27,k5_relat_1(k6_relat_1(A_26),B_27)) = k5_relat_1(k6_relat_1(A_26),B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_26,c_936])).

tff(c_2501,plain,(
    ! [A_166,A_165] :
      ( k3_xboole_0(k6_relat_1(A_166),k7_relat_1(k6_relat_1(A_166),A_165)) = k5_relat_1(k6_relat_1(A_165),k6_relat_1(A_166))
      | ~ v1_relat_1(k6_relat_1(A_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2492,c_965])).

tff(c_2560,plain,(
    ! [A_166,A_165] : k3_xboole_0(k6_relat_1(A_166),k7_relat_1(k6_relat_1(A_166),A_165)) = k7_relat_1(k6_relat_1(A_166),A_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2483,c_2501])).

tff(c_8894,plain,(
    ! [A_267,B_268] : k7_relat_1(k6_relat_1(A_267),k3_xboole_0(A_267,B_268)) = k6_relat_1(k3_xboole_0(A_267,B_268)) ),
    inference(resolution,[status(thm)],[c_8646,c_242])).

tff(c_173,plain,(
    ! [B_63,A_62] :
      ( r1_tarski(k7_relat_1(B_63,A_62),B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_26])).

tff(c_1356,plain,(
    ! [B_122,A_123] :
      ( k3_xboole_0(B_122,k7_relat_1(B_122,A_123)) = k7_relat_1(B_122,A_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_173,c_936])).

tff(c_1365,plain,(
    ! [B_122,A_123] :
      ( k3_xboole_0(k7_relat_1(B_122,A_123),B_122) = k3_xboole_0(B_122,k7_relat_1(B_122,A_123))
      | ~ v1_relat_1(B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1356,c_685])).

tff(c_8959,plain,(
    ! [A_267,B_268] :
      ( k3_xboole_0(k6_relat_1(A_267),k7_relat_1(k6_relat_1(A_267),k3_xboole_0(A_267,B_268))) = k3_xboole_0(k6_relat_1(k3_xboole_0(A_267,B_268)),k6_relat_1(A_267))
      | ~ v1_relat_1(k6_relat_1(A_267)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8894,c_1365])).

tff(c_10921,plain,(
    ! [A_298,B_299] : k3_xboole_0(k6_relat_1(k3_xboole_0(A_298,B_299)),k6_relat_1(A_298)) = k6_relat_1(k3_xboole_0(A_298,B_299)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8861,c_2560,c_8959])).

tff(c_1579,plain,(
    ! [A_132,A_133] : k3_xboole_0(k7_relat_1(k6_relat_1(A_132),A_133),k6_relat_1(A_133)) = k7_relat_1(k6_relat_1(A_132),A_133) ),
    inference(resolution,[status(thm)],[c_204,c_654])).

tff(c_1618,plain,(
    ! [A_88,A_35] :
      ( k3_xboole_0(k6_relat_1(A_88),k6_relat_1(A_35)) = k7_relat_1(k6_relat_1(A_88),A_35)
      | ~ r1_tarski(A_88,A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_1579])).

tff(c_10963,plain,(
    ! [A_298,B_299] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_298,B_299)),A_298) = k6_relat_1(k3_xboole_0(A_298,B_299))
      | ~ r1_tarski(k3_xboole_0(A_298,B_299),A_298) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10921,c_1618])).

tff(c_11741,plain,(
    ! [A_308,B_309] : k7_relat_1(k6_relat_1(k3_xboole_0(A_308,B_309)),A_308) = k6_relat_1(k3_xboole_0(A_308,B_309)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10963])).

tff(c_6932,plain,(
    ! [A_245,A_246,A_35] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_245),A_246),A_35),k7_relat_1(k6_relat_1(A_246),A_35))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_245),A_246)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6839])).

tff(c_6957,plain,(
    ! [A_245,A_246,A_35] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_245),A_246),A_35),k7_relat_1(k6_relat_1(A_246),A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_6932])).

tff(c_11780,plain,(
    ! [A_308,B_309,A_35] : r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_308,B_309)),A_35),k7_relat_1(k6_relat_1(A_308),A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11741,c_6957])).

tff(c_79603,plain,(
    ! [A_774,A_775] : r1_tarski(k6_relat_1(k3_xboole_0(A_774,A_775)),k7_relat_1(k6_relat_1(A_775),A_774)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78736,c_11780])).

tff(c_79615,plain,(
    ! [A_775,A_774] :
      ( k7_relat_1(k6_relat_1(A_775),A_774) = k6_relat_1(k3_xboole_0(A_774,A_775))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_775),A_774),k6_relat_1(k3_xboole_0(A_774,A_775))) ) ),
    inference(resolution,[status(thm)],[c_79603,c_2])).

tff(c_79893,plain,(
    ! [A_775,A_774] : k7_relat_1(k6_relat_1(A_775),A_774) = k6_relat_1(k3_xboole_0(A_774,A_775)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45111,c_79615])).

tff(c_44,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_187,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_44])).

tff(c_210,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_187])).

tff(c_80518,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79893,c_210])).

tff(c_80547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44091,c_80518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.03/12.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.03/12.27  
% 22.03/12.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.03/12.27  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 22.03/12.27  
% 22.03/12.27  %Foreground sorts:
% 22.03/12.27  
% 22.03/12.27  
% 22.03/12.27  %Background operators:
% 22.03/12.27  
% 22.03/12.27  
% 22.03/12.27  %Foreground operators:
% 22.03/12.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.03/12.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.03/12.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 22.03/12.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 22.03/12.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.03/12.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.03/12.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.03/12.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.03/12.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.03/12.27  tff('#skF_2', type, '#skF_2': $i).
% 22.03/12.27  tff('#skF_1', type, '#skF_1': $i).
% 22.03/12.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.03/12.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.03/12.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 22.03/12.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.03/12.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.03/12.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.03/12.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 22.03/12.27  
% 22.24/12.30  tff(f_100, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 22.24/12.30  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 22.24/12.30  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 22.24/12.30  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 22.24/12.30  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 22.24/12.30  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 22.24/12.30  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 22.24/12.30  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 22.24/12.30  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 22.24/12.30  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 22.24/12.30  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 22.24/12.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.24/12.30  tff(f_103, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 22.24/12.30  tff(c_40, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.24/12.30  tff(c_167, plain, (![A_62, B_63]: (k5_relat_1(k6_relat_1(A_62), B_63)=k7_relat_1(B_63, A_62) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_96])).
% 22.24/12.30  tff(c_28, plain, (![B_27, A_26]: (r1_tarski(k5_relat_1(B_27, k6_relat_1(A_26)), B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.24/12.30  tff(c_177, plain, (![A_26, A_62]: (r1_tarski(k7_relat_1(k6_relat_1(A_26), A_62), k6_relat_1(A_62)) | ~v1_relat_1(k6_relat_1(A_62)) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_28])).
% 22.24/12.30  tff(c_204, plain, (![A_26, A_62]: (r1_tarski(k7_relat_1(k6_relat_1(A_26), A_62), k6_relat_1(A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_177])).
% 22.24/12.30  tff(c_22, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.24/12.30  tff(c_38, plain, (![A_35, B_36]: (k5_relat_1(k6_relat_1(A_35), B_36)=k7_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_96])).
% 22.24/12.30  tff(c_329, plain, (![A_78, B_79]: (k5_relat_1(k6_relat_1(A_78), B_79)=B_79 | ~r1_tarski(k1_relat_1(B_79), A_78) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_78])).
% 22.24/12.30  tff(c_338, plain, (![A_78, A_25]: (k5_relat_1(k6_relat_1(A_78), k6_relat_1(A_25))=k6_relat_1(A_25) | ~r1_tarski(A_25, A_78) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_329])).
% 22.24/12.30  tff(c_505, plain, (![A_87, A_88]: (k5_relat_1(k6_relat_1(A_87), k6_relat_1(A_88))=k6_relat_1(A_88) | ~r1_tarski(A_88, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_338])).
% 22.24/12.30  tff(c_546, plain, (![A_88, A_35]: (k7_relat_1(k6_relat_1(A_88), A_35)=k6_relat_1(A_88) | ~r1_tarski(A_88, A_35) | ~v1_relat_1(k6_relat_1(A_88)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_505])).
% 22.24/12.30  tff(c_587, plain, (![A_91, A_92]: (k7_relat_1(k6_relat_1(A_91), A_92)=k6_relat_1(A_91) | ~r1_tarski(A_91, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_546])).
% 22.24/12.30  tff(c_245, plain, (![B_71, A_72]: (k3_xboole_0(k1_relat_1(B_71), A_72)=k1_relat_1(k7_relat_1(B_71, A_72)) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.24/12.30  tff(c_260, plain, (![A_25, A_72]: (k1_relat_1(k7_relat_1(k6_relat_1(A_25), A_72))=k3_xboole_0(A_25, A_72) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_245])).
% 22.24/12.30  tff(c_264, plain, (![A_25, A_72]: (k1_relat_1(k7_relat_1(k6_relat_1(A_25), A_72))=k3_xboole_0(A_25, A_72))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_260])).
% 22.24/12.30  tff(c_607, plain, (![A_91, A_92]: (k3_xboole_0(A_91, A_92)=k1_relat_1(k6_relat_1(A_91)) | ~r1_tarski(A_91, A_92))), inference(superposition, [status(thm), theory('equality')], [c_587, c_264])).
% 22.24/12.30  tff(c_654, plain, (![A_93, A_94]: (k3_xboole_0(A_93, A_94)=A_93 | ~r1_tarski(A_93, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_607])).
% 22.24/12.30  tff(c_682, plain, (![A_26, A_62]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_26), A_62), k6_relat_1(A_62))=k7_relat_1(k6_relat_1(A_26), A_62))), inference(resolution, [status(thm)], [c_204, c_654])).
% 22.24/12.30  tff(c_2389, plain, (![B_163, A_164]: (k3_xboole_0(k5_relat_1(B_163, k6_relat_1(A_164)), B_163)=k5_relat_1(B_163, k6_relat_1(A_164)) | ~v1_relat_1(B_163))), inference(resolution, [status(thm)], [c_28, c_654])).
% 22.24/12.30  tff(c_2448, plain, (![A_164, A_35]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_164), A_35), k6_relat_1(A_35))=k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_164)) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_164)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2389])).
% 22.24/12.30  tff(c_2492, plain, (![A_165, A_166]: (k5_relat_1(k6_relat_1(A_165), k6_relat_1(A_166))=k7_relat_1(k6_relat_1(A_166), A_165))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_682, c_2448])).
% 22.24/12.30  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.24/12.30  tff(c_2529, plain, (![A_166, A_165]: (v1_relat_1(k7_relat_1(k6_relat_1(A_166), A_165)) | ~v1_relat_1(k6_relat_1(A_166)) | ~v1_relat_1(k6_relat_1(A_165)))), inference(superposition, [status(thm), theory('equality')], [c_2492, c_16])).
% 22.24/12.30  tff(c_2579, plain, (![A_166, A_165]: (v1_relat_1(k7_relat_1(k6_relat_1(A_166), A_165)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_2529])).
% 22.24/12.30  tff(c_24, plain, (![A_25]: (k2_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.24/12.30  tff(c_34, plain, (![A_32]: (k5_relat_1(A_32, k6_relat_1(k2_relat_1(A_32)))=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_88])).
% 22.24/12.30  tff(c_201, plain, (![A_62]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_62))), A_62)=k6_relat_1(A_62) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_62)))) | ~v1_relat_1(k6_relat_1(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_167])).
% 22.24/12.30  tff(c_217, plain, (![A_62]: (k7_relat_1(k6_relat_1(A_62), A_62)=k6_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_24, c_201])).
% 22.24/12.30  tff(c_265, plain, (![A_73, A_74]: (k1_relat_1(k7_relat_1(k6_relat_1(A_73), A_74))=k3_xboole_0(A_73, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_260])).
% 22.24/12.30  tff(c_277, plain, (![A_62]: (k3_xboole_0(A_62, A_62)=k1_relat_1(k6_relat_1(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_265])).
% 22.24/12.30  tff(c_280, plain, (![A_62]: (k3_xboole_0(A_62, A_62)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_277])).
% 22.24/12.30  tff(c_2483, plain, (![A_35, A_164]: (k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_164))=k7_relat_1(k6_relat_1(A_164), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_682, c_2448])).
% 22.24/12.30  tff(c_86, plain, (![A_49]: (k5_relat_1(A_49, k6_relat_1(k2_relat_1(A_49)))=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_88])).
% 22.24/12.30  tff(c_95, plain, (![A_25]: (k5_relat_1(k6_relat_1(A_25), k6_relat_1(A_25))=k6_relat_1(A_25) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_86])).
% 22.24/12.30  tff(c_99, plain, (![A_25]: (k5_relat_1(k6_relat_1(A_25), k6_relat_1(A_25))=k6_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95])).
% 22.24/12.30  tff(c_1047, plain, (![A_110, B_111, C_112]: (k5_relat_1(k5_relat_1(A_110, B_111), C_112)=k5_relat_1(A_110, k5_relat_1(B_111, C_112)) | ~v1_relat_1(C_112) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.24/12.30  tff(c_1088, plain, (![A_25, C_112]: (k5_relat_1(k6_relat_1(A_25), k5_relat_1(k6_relat_1(A_25), C_112))=k5_relat_1(k6_relat_1(A_25), C_112) | ~v1_relat_1(C_112) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1047])).
% 22.24/12.30  tff(c_13602, plain, (![A_333, C_334]: (k5_relat_1(k6_relat_1(A_333), k5_relat_1(k6_relat_1(A_333), C_334))=k5_relat_1(k6_relat_1(A_333), C_334) | ~v1_relat_1(C_334))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_1088])).
% 22.24/12.30  tff(c_13753, plain, (![A_35, A_164]: (k5_relat_1(k6_relat_1(A_35), k7_relat_1(k6_relat_1(A_164), A_35))=k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_164)) | ~v1_relat_1(k6_relat_1(A_164)))), inference(superposition, [status(thm), theory('equality')], [c_2483, c_13602])).
% 22.24/12.30  tff(c_13831, plain, (![A_335, A_336]: (k5_relat_1(k6_relat_1(A_335), k7_relat_1(k6_relat_1(A_336), A_335))=k7_relat_1(k6_relat_1(A_336), A_335))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2483, c_13753])).
% 22.24/12.30  tff(c_13889, plain, (![A_336, A_335]: (k7_relat_1(k7_relat_1(k6_relat_1(A_336), A_335), A_335)=k7_relat_1(k6_relat_1(A_336), A_335) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_336), A_335)))), inference(superposition, [status(thm), theory('equality')], [c_13831, c_38])).
% 22.24/12.30  tff(c_14023, plain, (![A_337, A_338]: (k7_relat_1(k7_relat_1(k6_relat_1(A_337), A_338), A_338)=k7_relat_1(k6_relat_1(A_337), A_338))), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_13889])).
% 22.24/12.30  tff(c_36, plain, (![B_34, A_33]: (k3_xboole_0(k1_relat_1(B_34), A_33)=k1_relat_1(k7_relat_1(B_34, A_33)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.24/12.30  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.24/12.30  tff(c_494, plain, (![B_85, A_86]: (k5_relat_1(B_85, k6_relat_1(A_86))=B_85 | ~r1_tarski(k2_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_84])).
% 22.24/12.30  tff(c_497, plain, (![A_25, A_86]: (k5_relat_1(k6_relat_1(A_25), k6_relat_1(A_86))=k6_relat_1(A_25) | ~r1_tarski(A_25, A_86) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_494])).
% 22.24/12.30  tff(c_776, plain, (![A_100, A_101]: (k5_relat_1(k6_relat_1(A_100), k6_relat_1(A_101))=k6_relat_1(A_100) | ~r1_tarski(A_100, A_101))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_497])).
% 22.24/12.30  tff(c_792, plain, (![A_101, A_100]: (k7_relat_1(k6_relat_1(A_101), A_100)=k6_relat_1(A_100) | ~v1_relat_1(k6_relat_1(A_101)) | ~r1_tarski(A_100, A_101))), inference(superposition, [status(thm), theory('equality')], [c_776, c_38])).
% 22.24/12.30  tff(c_864, plain, (![A_102, A_103]: (k7_relat_1(k6_relat_1(A_102), A_103)=k6_relat_1(A_103) | ~r1_tarski(A_103, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_792])).
% 22.24/12.30  tff(c_887, plain, (![A_102, A_103]: (k3_xboole_0(A_102, A_103)=k1_relat_1(k6_relat_1(A_103)) | ~r1_tarski(A_103, A_102))), inference(superposition, [status(thm), theory('equality')], [c_864, c_264])).
% 22.24/12.30  tff(c_936, plain, (![A_104, A_105]: (k3_xboole_0(A_104, A_105)=A_105 | ~r1_tarski(A_105, A_104))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_887])).
% 22.24/12.30  tff(c_971, plain, (![A_106, B_107]: (k3_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k3_xboole_0(A_106, B_107))), inference(resolution, [status(thm)], [c_8, c_936])).
% 22.24/12.30  tff(c_1005, plain, (![B_34, A_33]: (k3_xboole_0(k1_relat_1(B_34), k1_relat_1(k7_relat_1(B_34, A_33)))=k3_xboole_0(k1_relat_1(B_34), A_33) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_36, c_971])).
% 22.24/12.30  tff(c_14029, plain, (![A_337, A_338]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_337), A_338)), k1_relat_1(k7_relat_1(k6_relat_1(A_337), A_338)))=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_337), A_338)), A_338) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_337), A_338)))), inference(superposition, [status(thm), theory('equality')], [c_14023, c_1005])).
% 22.24/12.30  tff(c_14149, plain, (![A_337, A_338]: (k3_xboole_0(k3_xboole_0(A_337, A_338), A_338)=k3_xboole_0(A_337, A_338))), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_280, c_264, c_264, c_264, c_14029])).
% 22.24/12.30  tff(c_254, plain, (![B_71, A_72]: (r1_tarski(k1_relat_1(k7_relat_1(B_71, A_72)), k1_relat_1(B_71)) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_245, c_8])).
% 22.24/12.30  tff(c_42604, plain, (![B_584, A_585]: (k5_relat_1(k6_relat_1(k1_relat_1(B_584)), k7_relat_1(B_584, A_585))=k7_relat_1(B_584, A_585) | ~v1_relat_1(k7_relat_1(B_584, A_585)) | ~v1_relat_1(B_584))), inference(resolution, [status(thm)], [c_254, c_329])).
% 22.24/12.30  tff(c_1060, plain, (![A_110, B_111, A_26]: (r1_tarski(k5_relat_1(A_110, k5_relat_1(B_111, k6_relat_1(A_26))), k5_relat_1(A_110, B_111)) | ~v1_relat_1(k5_relat_1(A_110, B_111)) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_1047, c_28])).
% 22.24/12.30  tff(c_6474, plain, (![A_237, B_238, A_239]: (r1_tarski(k5_relat_1(A_237, k5_relat_1(B_238, k6_relat_1(A_239))), k5_relat_1(A_237, B_238)) | ~v1_relat_1(k5_relat_1(A_237, B_238)) | ~v1_relat_1(B_238) | ~v1_relat_1(A_237))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1060])).
% 22.24/12.30  tff(c_6530, plain, (![A_35, A_164, A_239]: (r1_tarski(k5_relat_1(k6_relat_1(A_35), k5_relat_1(k6_relat_1(A_164), k6_relat_1(A_239))), k7_relat_1(k6_relat_1(A_164), A_35)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_164))) | ~v1_relat_1(k6_relat_1(A_164)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_2483, c_6474])).
% 22.24/12.30  tff(c_6631, plain, (![A_35, A_239, A_164]: (r1_tarski(k5_relat_1(k6_relat_1(A_35), k7_relat_1(k6_relat_1(A_239), A_164)), k7_relat_1(k6_relat_1(A_164), A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_2579, c_2483, c_2483, c_6530])).
% 22.24/12.30  tff(c_42669, plain, (![A_239, A_585]: (r1_tarski(k7_relat_1(k6_relat_1(A_239), A_585), k7_relat_1(k6_relat_1(A_585), k1_relat_1(k6_relat_1(A_239)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_239), A_585)) | ~v1_relat_1(k6_relat_1(A_239)))), inference(superposition, [status(thm), theory('equality')], [c_42604, c_6631])).
% 22.24/12.30  tff(c_42807, plain, (![A_239, A_585]: (r1_tarski(k7_relat_1(k6_relat_1(A_239), A_585), k7_relat_1(k6_relat_1(A_585), A_239)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2579, c_22, c_42669])).
% 22.24/12.30  tff(c_42852, plain, (![A_586, A_587]: (r1_tarski(k7_relat_1(k6_relat_1(A_586), A_587), k7_relat_1(k6_relat_1(A_587), A_586)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2579, c_22, c_42669])).
% 22.24/12.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.24/12.30  tff(c_42867, plain, (![A_587, A_586]: (k7_relat_1(k6_relat_1(A_587), A_586)=k7_relat_1(k6_relat_1(A_586), A_587) | ~r1_tarski(k7_relat_1(k6_relat_1(A_587), A_586), k7_relat_1(k6_relat_1(A_586), A_587)))), inference(resolution, [status(thm)], [c_42852, c_2])).
% 22.24/12.30  tff(c_43051, plain, (![A_589, A_588]: (k7_relat_1(k6_relat_1(A_589), A_588)=k7_relat_1(k6_relat_1(A_588), A_589))), inference(demodulation, [status(thm), theory('equality')], [c_42807, c_42867])).
% 22.24/12.30  tff(c_688, plain, (![A_95, B_96]: (k3_xboole_0(k3_xboole_0(A_95, B_96), A_95)=k3_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_8, c_654])).
% 22.24/12.30  tff(c_712, plain, (![B_34, A_33]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_34, A_33)), k1_relat_1(B_34))=k3_xboole_0(k1_relat_1(B_34), A_33) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_36, c_688])).
% 22.24/12.30  tff(c_43607, plain, (![A_588, A_589]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_588), A_589)), k1_relat_1(k6_relat_1(A_589)))=k3_xboole_0(k1_relat_1(k6_relat_1(A_589)), A_588) | ~v1_relat_1(k6_relat_1(A_589)))), inference(superposition, [status(thm), theory('equality')], [c_43051, c_712])).
% 22.24/12.30  tff(c_44091, plain, (![A_589, A_588]: (k3_xboole_0(A_589, A_588)=k3_xboole_0(A_588, A_589))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14149, c_264, c_22, c_22, c_43607])).
% 22.24/12.30  tff(c_685, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_654])).
% 22.24/12.30  tff(c_576, plain, (![A_88, A_35]: (k7_relat_1(k6_relat_1(A_88), A_35)=k6_relat_1(A_88) | ~r1_tarski(A_88, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_546])).
% 22.24/12.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.24/12.30  tff(c_346, plain, (![B_79]: (k5_relat_1(k6_relat_1(k1_relat_1(B_79)), B_79)=B_79 | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_6, c_329])).
% 22.24/12.30  tff(c_6839, plain, (![A_244, A_245, A_246]: (r1_tarski(k5_relat_1(k6_relat_1(A_244), k7_relat_1(k6_relat_1(A_245), A_246)), k7_relat_1(k6_relat_1(A_246), A_244)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_2579, c_2483, c_2483, c_6530])).
% 22.24/12.30  tff(c_6922, plain, (![A_245, A_246]: (r1_tarski(k7_relat_1(k6_relat_1(A_245), A_246), k7_relat_1(k6_relat_1(A_246), k1_relat_1(k7_relat_1(k6_relat_1(A_245), A_246)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_245), A_246)))), inference(superposition, [status(thm), theory('equality')], [c_346, c_6839])).
% 22.24/12.30  tff(c_7579, plain, (![A_252, A_253]: (r1_tarski(k7_relat_1(k6_relat_1(A_252), A_253), k7_relat_1(k6_relat_1(A_253), k3_xboole_0(A_252, A_253))))), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_264, c_6922])).
% 22.24/12.30  tff(c_8478, plain, (![A_263, A_264]: (r1_tarski(k6_relat_1(A_263), k7_relat_1(k6_relat_1(A_264), k3_xboole_0(A_263, A_264))) | ~r1_tarski(A_263, A_264))), inference(superposition, [status(thm), theory('equality')], [c_576, c_7579])).
% 22.24/12.30  tff(c_8609, plain, (![A_3, B_4]: (r1_tarski(k6_relat_1(k3_xboole_0(A_3, B_4)), k7_relat_1(k6_relat_1(A_3), k3_xboole_0(A_3, B_4))) | ~r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(superposition, [status(thm), theory('equality')], [c_685, c_8478])).
% 22.24/12.30  tff(c_8646, plain, (![A_265, B_266]: (r1_tarski(k6_relat_1(k3_xboole_0(A_265, B_266)), k7_relat_1(k6_relat_1(A_265), k3_xboole_0(A_265, B_266))))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8609])).
% 22.24/12.30  tff(c_236, plain, (![A_67, A_68]: (r1_tarski(k7_relat_1(k6_relat_1(A_67), A_68), k6_relat_1(A_68)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_177])).
% 22.24/12.30  tff(c_242, plain, (![A_67, A_68]: (k7_relat_1(k6_relat_1(A_67), A_68)=k6_relat_1(A_68) | ~r1_tarski(k6_relat_1(A_68), k7_relat_1(k6_relat_1(A_67), A_68)))), inference(resolution, [status(thm)], [c_236, c_2])).
% 22.24/12.30  tff(c_8861, plain, (![A_265, B_266]: (k7_relat_1(k6_relat_1(A_265), k3_xboole_0(A_265, B_266))=k6_relat_1(k3_xboole_0(A_265, B_266)))), inference(resolution, [status(thm)], [c_8646, c_242])).
% 22.24/12.30  tff(c_44493, plain, (![A_595, A_594]: (k3_xboole_0(A_595, A_594)=k3_xboole_0(A_594, A_595))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14149, c_264, c_22, c_22, c_43607])).
% 22.24/12.30  tff(c_6953, plain, (![A_245, A_246]: (r1_tarski(k7_relat_1(k6_relat_1(A_245), A_246), k7_relat_1(k6_relat_1(A_246), k3_xboole_0(A_245, A_246))))), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_264, c_6922])).
% 22.24/12.30  tff(c_44855, plain, (![A_595, A_594]: (r1_tarski(k7_relat_1(k6_relat_1(A_595), A_594), k7_relat_1(k6_relat_1(A_594), k3_xboole_0(A_594, A_595))))), inference(superposition, [status(thm), theory('equality')], [c_44493, c_6953])).
% 22.24/12.30  tff(c_45111, plain, (![A_595, A_594]: (r1_tarski(k7_relat_1(k6_relat_1(A_595), A_594), k6_relat_1(k3_xboole_0(A_594, A_595))))), inference(demodulation, [status(thm), theory('equality')], [c_8861, c_44855])).
% 22.24/12.30  tff(c_74943, plain, (![A_754, A_755]: (k7_relat_1(k6_relat_1(A_754), k3_xboole_0(A_755, A_754))=k6_relat_1(k3_xboole_0(A_754, A_755)))), inference(superposition, [status(thm), theory('equality')], [c_44493, c_8861])).
% 22.24/12.30  tff(c_345, plain, (![A_78, A_25]: (k5_relat_1(k6_relat_1(A_78), k6_relat_1(A_25))=k6_relat_1(A_25) | ~r1_tarski(A_25, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_338])).
% 22.24/12.30  tff(c_785, plain, (![A_101, A_100]: (k6_relat_1(A_101)=k6_relat_1(A_100) | ~r1_tarski(A_101, A_100) | ~r1_tarski(A_100, A_101))), inference(superposition, [status(thm), theory('equality')], [c_776, c_345])).
% 22.24/12.30  tff(c_42859, plain, (![A_587, A_586]: (k6_relat_1(k7_relat_1(k6_relat_1(A_587), A_586))=k6_relat_1(k7_relat_1(k6_relat_1(A_586), A_587)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_587), A_586), k7_relat_1(k6_relat_1(A_586), A_587)))), inference(resolution, [status(thm)], [c_42852, c_785])).
% 22.24/12.30  tff(c_61798, plain, (![A_699, A_698]: (k6_relat_1(k7_relat_1(k6_relat_1(A_699), A_698))=k6_relat_1(k7_relat_1(k6_relat_1(A_698), A_699)))), inference(demodulation, [status(thm), theory('equality')], [c_42807, c_42859])).
% 22.24/12.30  tff(c_63086, plain, (![A_698, A_699]: (k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_698), A_699)))=k7_relat_1(k6_relat_1(A_699), A_698))), inference(superposition, [status(thm), theory('equality')], [c_61798, c_22])).
% 22.24/12.30  tff(c_74967, plain, (![A_755, A_754]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_755, A_754)), A_754)=k1_relat_1(k6_relat_1(k6_relat_1(k3_xboole_0(A_754, A_755)))))), inference(superposition, [status(thm), theory('equality')], [c_74943, c_63086])).
% 22.24/12.30  tff(c_78736, plain, (![A_772, A_773]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_772, A_773)), A_773)=k6_relat_1(k3_xboole_0(A_773, A_772)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_74967])).
% 22.24/12.30  tff(c_26, plain, (![A_26, B_27]: (r1_tarski(k5_relat_1(k6_relat_1(A_26), B_27), B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.24/12.30  tff(c_965, plain, (![B_27, A_26]: (k3_xboole_0(B_27, k5_relat_1(k6_relat_1(A_26), B_27))=k5_relat_1(k6_relat_1(A_26), B_27) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_26, c_936])).
% 22.24/12.30  tff(c_2501, plain, (![A_166, A_165]: (k3_xboole_0(k6_relat_1(A_166), k7_relat_1(k6_relat_1(A_166), A_165))=k5_relat_1(k6_relat_1(A_165), k6_relat_1(A_166)) | ~v1_relat_1(k6_relat_1(A_166)))), inference(superposition, [status(thm), theory('equality')], [c_2492, c_965])).
% 22.24/12.30  tff(c_2560, plain, (![A_166, A_165]: (k3_xboole_0(k6_relat_1(A_166), k7_relat_1(k6_relat_1(A_166), A_165))=k7_relat_1(k6_relat_1(A_166), A_165))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2483, c_2501])).
% 22.24/12.30  tff(c_8894, plain, (![A_267, B_268]: (k7_relat_1(k6_relat_1(A_267), k3_xboole_0(A_267, B_268))=k6_relat_1(k3_xboole_0(A_267, B_268)))), inference(resolution, [status(thm)], [c_8646, c_242])).
% 22.24/12.30  tff(c_173, plain, (![B_63, A_62]: (r1_tarski(k7_relat_1(B_63, A_62), B_63) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_167, c_26])).
% 22.24/12.30  tff(c_1356, plain, (![B_122, A_123]: (k3_xboole_0(B_122, k7_relat_1(B_122, A_123))=k7_relat_1(B_122, A_123) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_173, c_936])).
% 22.24/12.30  tff(c_1365, plain, (![B_122, A_123]: (k3_xboole_0(k7_relat_1(B_122, A_123), B_122)=k3_xboole_0(B_122, k7_relat_1(B_122, A_123)) | ~v1_relat_1(B_122))), inference(superposition, [status(thm), theory('equality')], [c_1356, c_685])).
% 22.24/12.30  tff(c_8959, plain, (![A_267, B_268]: (k3_xboole_0(k6_relat_1(A_267), k7_relat_1(k6_relat_1(A_267), k3_xboole_0(A_267, B_268)))=k3_xboole_0(k6_relat_1(k3_xboole_0(A_267, B_268)), k6_relat_1(A_267)) | ~v1_relat_1(k6_relat_1(A_267)))), inference(superposition, [status(thm), theory('equality')], [c_8894, c_1365])).
% 22.24/12.30  tff(c_10921, plain, (![A_298, B_299]: (k3_xboole_0(k6_relat_1(k3_xboole_0(A_298, B_299)), k6_relat_1(A_298))=k6_relat_1(k3_xboole_0(A_298, B_299)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8861, c_2560, c_8959])).
% 22.24/12.30  tff(c_1579, plain, (![A_132, A_133]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_132), A_133), k6_relat_1(A_133))=k7_relat_1(k6_relat_1(A_132), A_133))), inference(resolution, [status(thm)], [c_204, c_654])).
% 22.24/12.30  tff(c_1618, plain, (![A_88, A_35]: (k3_xboole_0(k6_relat_1(A_88), k6_relat_1(A_35))=k7_relat_1(k6_relat_1(A_88), A_35) | ~r1_tarski(A_88, A_35))), inference(superposition, [status(thm), theory('equality')], [c_576, c_1579])).
% 22.24/12.30  tff(c_10963, plain, (![A_298, B_299]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_298, B_299)), A_298)=k6_relat_1(k3_xboole_0(A_298, B_299)) | ~r1_tarski(k3_xboole_0(A_298, B_299), A_298))), inference(superposition, [status(thm), theory('equality')], [c_10921, c_1618])).
% 22.24/12.30  tff(c_11741, plain, (![A_308, B_309]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_308, B_309)), A_308)=k6_relat_1(k3_xboole_0(A_308, B_309)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10963])).
% 22.24/12.30  tff(c_6932, plain, (![A_245, A_246, A_35]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_245), A_246), A_35), k7_relat_1(k6_relat_1(A_246), A_35)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_245), A_246)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6839])).
% 22.24/12.30  tff(c_6957, plain, (![A_245, A_246, A_35]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_245), A_246), A_35), k7_relat_1(k6_relat_1(A_246), A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_6932])).
% 22.24/12.30  tff(c_11780, plain, (![A_308, B_309, A_35]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_308, B_309)), A_35), k7_relat_1(k6_relat_1(A_308), A_35)))), inference(superposition, [status(thm), theory('equality')], [c_11741, c_6957])).
% 22.24/12.30  tff(c_79603, plain, (![A_774, A_775]: (r1_tarski(k6_relat_1(k3_xboole_0(A_774, A_775)), k7_relat_1(k6_relat_1(A_775), A_774)))), inference(superposition, [status(thm), theory('equality')], [c_78736, c_11780])).
% 22.24/12.30  tff(c_79615, plain, (![A_775, A_774]: (k7_relat_1(k6_relat_1(A_775), A_774)=k6_relat_1(k3_xboole_0(A_774, A_775)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_775), A_774), k6_relat_1(k3_xboole_0(A_774, A_775))))), inference(resolution, [status(thm)], [c_79603, c_2])).
% 22.24/12.30  tff(c_79893, plain, (![A_775, A_774]: (k7_relat_1(k6_relat_1(A_775), A_774)=k6_relat_1(k3_xboole_0(A_774, A_775)))), inference(demodulation, [status(thm), theory('equality')], [c_45111, c_79615])).
% 22.24/12.30  tff(c_44, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 22.24/12.30  tff(c_187, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_44])).
% 22.24/12.30  tff(c_210, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_187])).
% 22.24/12.30  tff(c_80518, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79893, c_210])).
% 22.24/12.30  tff(c_80547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44091, c_80518])).
% 22.24/12.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.24/12.30  
% 22.24/12.30  Inference rules
% 22.24/12.30  ----------------------
% 22.24/12.30  #Ref     : 0
% 22.24/12.30  #Sup     : 21102
% 22.24/12.30  #Fact    : 0
% 22.24/12.30  #Define  : 0
% 22.24/12.30  #Split   : 2
% 22.24/12.30  #Chain   : 0
% 22.24/12.30  #Close   : 0
% 22.24/12.30  
% 22.24/12.30  Ordering : KBO
% 22.24/12.30  
% 22.24/12.30  Simplification rules
% 22.24/12.30  ----------------------
% 22.24/12.30  #Subsume      : 3176
% 22.24/12.30  #Demod        : 19305
% 22.24/12.30  #Tautology    : 5839
% 22.24/12.30  #SimpNegUnit  : 0
% 22.24/12.30  #BackRed      : 108
% 22.24/12.30  
% 22.24/12.30  #Partial instantiations: 0
% 22.24/12.30  #Strategies tried      : 1
% 22.24/12.30  
% 22.24/12.30  Timing (in seconds)
% 22.24/12.30  ----------------------
% 22.24/12.31  Preprocessing        : 0.33
% 22.24/12.31  Parsing              : 0.18
% 22.24/12.31  CNF conversion       : 0.02
% 22.24/12.31  Main loop            : 11.12
% 22.24/12.31  Inferencing          : 1.89
% 22.24/12.31  Reduction            : 4.63
% 22.24/12.31  Demodulation         : 3.97
% 22.24/12.31  BG Simplification    : 0.30
% 22.24/12.31  Subsumption          : 3.72
% 22.24/12.31  Abstraction          : 0.46
% 22.24/12.31  MUC search           : 0.00
% 22.24/12.31  Cooper               : 0.00
% 22.24/12.31  Total                : 11.51
% 22.24/12.31  Index Insertion      : 0.00
% 22.24/12.31  Index Deletion       : 0.00
% 22.24/12.31  Index Matching       : 0.00
% 22.24/12.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
