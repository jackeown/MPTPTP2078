%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:58 EST 2020

% Result     : Theorem 31.05s
% Output     : CNFRefutation 31.16s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 973 expanded)
%              Number of leaves         :   41 ( 337 expanded)
%              Depth                    :   18
%              Number of atoms          :  254 (1419 expanded)
%              Number of equality atoms :  115 ( 687 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_80,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_103,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_108,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_64,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,(
    ! [A_59] : k2_xboole_0(A_59,k1_tarski(A_59)) = k1_ordinal1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_126,plain,(
    ! [A_59] : r1_tarski(A_59,k1_ordinal1(A_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_50])).

tff(c_350,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_367,plain,(
    ! [A_59] : k3_xboole_0(A_59,k1_ordinal1(A_59)) = A_59 ),
    inference(resolution,[status(thm)],[c_126,c_350])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_72,plain,(
    ! [A_47] : r2_hidden(A_47,k1_ordinal1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_230,plain,(
    ! [B_67,A_68] :
      ( ~ r1_tarski(B_67,A_68)
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_238,plain,(
    ! [A_47] : ~ r1_tarski(k1_ordinal1(A_47),A_47) ),
    inference(resolution,[status(thm)],[c_72,c_230])).

tff(c_244,plain,(
    ! [A_72,B_73] :
      ( k2_xboole_0(A_72,B_73) = B_73
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_261,plain,(
    ! [A_59] : k2_xboole_0(A_59,k1_ordinal1(A_59)) = k1_ordinal1(A_59) ),
    inference(resolution,[status(thm)],[c_126,c_244])).

tff(c_38,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_595,plain,(
    ! [A_113,B_114] : k4_xboole_0(A_113,k4_xboole_0(A_113,B_114)) = k3_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_262,plain,(
    ! [A_18,B_19] : k2_xboole_0(k4_xboole_0(A_18,B_19),A_18) = A_18 ),
    inference(resolution,[status(thm)],[c_36,c_244])).

tff(c_607,plain,(
    ! [A_113,B_114] : k2_xboole_0(k3_xboole_0(A_113,B_114),A_113) = A_113 ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_262])).

tff(c_44,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1083,plain,(
    ! [A_131,B_132] : k2_xboole_0(A_131,k4_xboole_0(B_132,A_131)) = k2_xboole_0(A_131,B_132) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1127,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = k2_xboole_0(k3_xboole_0(A_26,B_27),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1083])).

tff(c_11990,plain,(
    ! [A_442,B_443] : k2_xboole_0(k3_xboole_0(A_442,B_443),k4_xboole_0(A_442,B_443)) = A_442 ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_1127])).

tff(c_18491,plain,(
    ! [A_563,B_564] : k2_xboole_0(k3_xboole_0(A_563,B_564),k4_xboole_0(B_564,A_563)) = B_564 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_11990])).

tff(c_23307,plain,(
    ! [A_609] : k2_xboole_0(A_609,k4_xboole_0(k1_ordinal1(A_609),A_609)) = k1_ordinal1(A_609) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_18491])).

tff(c_2206,plain,(
    ! [A_162,B_163,C_164] :
      ( r1_tarski(A_162,B_163)
      | ~ r1_xboole_0(A_162,C_164)
      | ~ r1_tarski(A_162,k2_xboole_0(B_163,C_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2286,plain,(
    ! [B_163,C_164] :
      ( r1_tarski(k2_xboole_0(B_163,C_164),B_163)
      | ~ r1_xboole_0(k2_xboole_0(B_163,C_164),C_164) ) ),
    inference(resolution,[status(thm)],[c_28,c_2206])).

tff(c_23416,plain,(
    ! [A_609] :
      ( r1_tarski(k2_xboole_0(A_609,k4_xboole_0(k1_ordinal1(A_609),A_609)),A_609)
      | ~ r1_xboole_0(k1_ordinal1(A_609),k4_xboole_0(k1_ordinal1(A_609),A_609)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23307,c_2286])).

tff(c_23565,plain,(
    ! [A_609] :
      ( r1_tarski(k1_ordinal1(A_609),A_609)
      | ~ r1_xboole_0(k1_ordinal1(A_609),k4_xboole_0(k1_ordinal1(A_609),A_609)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_38,c_23416])).

tff(c_23582,plain,(
    ! [A_610] : ~ r1_xboole_0(k1_ordinal1(A_610),k4_xboole_0(k1_ordinal1(A_610),A_610)) ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_23565])).

tff(c_23601,plain,(
    ! [A_610] : k4_xboole_0(k1_ordinal1(A_610),k4_xboole_0(k1_ordinal1(A_610),A_610)) != k1_ordinal1(A_610) ),
    inference(resolution,[status(thm)],[c_54,c_23582])).

tff(c_23610,plain,(
    ! [A_610] : k1_ordinal1(A_610) != A_610 ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_4,c_46,c_23601])).

tff(c_34,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_622,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_595])).

tff(c_625,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_622])).

tff(c_7086,plain,(
    ! [B_325,C_326] :
      ( r1_tarski(k2_xboole_0(B_325,C_326),B_325)
      | ~ r1_xboole_0(k2_xboole_0(B_325,C_326),C_326) ) ),
    inference(resolution,[status(thm)],[c_28,c_2206])).

tff(c_7122,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k2_xboole_0(k4_xboole_0(A_18,B_19),A_18),k4_xboole_0(A_18,B_19))
      | ~ r1_xboole_0(A_18,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_7086])).

tff(c_10093,plain,(
    ! [A_418,B_419] :
      ( r1_tarski(A_418,k4_xboole_0(A_418,B_419))
      | ~ r1_xboole_0(A_418,A_418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_7122])).

tff(c_1427,plain,(
    ! [B_140,A_141] :
      ( B_140 = A_141
      | ~ r1_tarski(B_140,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1452,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,k4_xboole_0(A_18,B_19)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1427])).

tff(c_10185,plain,(
    ! [A_420,B_421] :
      ( k4_xboole_0(A_420,B_421) = A_420
      | ~ r1_xboole_0(A_420,A_420) ) ),
    inference(resolution,[status(thm)],[c_10093,c_1452])).

tff(c_10188,plain,(
    ! [B_36,B_421] :
      ( k4_xboole_0(B_36,B_421) = B_36
      | k4_xboole_0(B_36,B_36) != B_36 ) ),
    inference(resolution,[status(thm)],[c_54,c_10185])).

tff(c_10193,plain,(
    ! [B_422,B_423] :
      ( k4_xboole_0(B_422,B_423) = B_422
      | k1_xboole_0 != B_422 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_10188])).

tff(c_10985,plain,(
    ! [A_433,B_434] :
      ( k3_xboole_0(A_433,B_434) = A_433
      | k1_xboole_0 != A_433 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_10193])).

tff(c_958,plain,(
    ! [A_126,B_127] : r1_tarski(k3_xboole_0(A_126,B_127),A_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_36])).

tff(c_997,plain,(
    ! [B_128,A_129] : r1_tarski(k3_xboole_0(B_128,A_129),A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_958])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1029,plain,(
    ! [B_128,A_129] : k2_xboole_0(k3_xboole_0(B_128,A_129),A_129) = A_129 ),
    inference(resolution,[status(thm)],[c_997,c_30])).

tff(c_13190,plain,(
    ! [A_454,B_455] :
      ( k2_xboole_0(A_454,B_455) = B_455
      | k1_xboole_0 != A_454 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10985,c_1029])).

tff(c_78,plain,(
    k1_ordinal1('#skF_3') = k1_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_401,plain,(
    ! [A_88] : k3_xboole_0(A_88,k1_ordinal1(A_88)) = A_88 ),
    inference(resolution,[status(thm)],[c_126,c_350])).

tff(c_418,plain,(
    k3_xboole_0('#skF_3',k1_ordinal1('#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_401])).

tff(c_1133,plain,(
    ! [A_28,B_29] : k2_xboole_0(k4_xboole_0(A_28,B_29),k3_xboole_0(A_28,B_29)) = k2_xboole_0(k4_xboole_0(A_28,B_29),A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1083])).

tff(c_3565,plain,(
    ! [A_220,B_221] : k2_xboole_0(k4_xboole_0(A_220,B_221),k3_xboole_0(A_220,B_221)) = A_220 ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_1133])).

tff(c_4132,plain,(
    ! [B_232,A_233] : k2_xboole_0(k4_xboole_0(B_232,A_233),k3_xboole_0(A_233,B_232)) = B_232 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3565])).

tff(c_4209,plain,(
    k2_xboole_0(k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3'),'#skF_3') = k1_ordinal1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_4132])).

tff(c_13289,plain,
    ( k1_ordinal1('#skF_4') = '#skF_3'
    | k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13190,c_4209])).

tff(c_13949,plain,(
    k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13289])).

tff(c_70,plain,(
    ! [A_46] : k2_xboole_0(A_46,k1_tarski(A_46)) = k1_ordinal1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1674,plain,(
    ! [A_147,B_148,C_149] :
      ( r1_tarski(k4_xboole_0(A_147,B_148),C_149)
      | ~ r1_tarski(A_147,k2_xboole_0(B_148,C_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9718,plain,(
    ! [A_408,B_409,C_410] :
      ( k2_xboole_0(k4_xboole_0(A_408,B_409),C_410) = C_410
      | ~ r1_tarski(A_408,k2_xboole_0(B_409,C_410)) ) ),
    inference(resolution,[status(thm)],[c_1674,c_30])).

tff(c_16300,plain,(
    ! [B_531,C_532] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_531,C_532),B_531),C_532) = C_532 ),
    inference(resolution,[status(thm)],[c_28,c_9718])).

tff(c_16516,plain,(
    ! [B_533,C_534] : r1_tarski(k4_xboole_0(k2_xboole_0(B_533,C_534),B_533),C_534) ),
    inference(superposition,[status(thm),theory(equality)],[c_16300,c_50])).

tff(c_16685,plain,(
    ! [A_535] : r1_tarski(k4_xboole_0(k1_ordinal1(A_535),A_535),k1_tarski(A_535)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_16516])).

tff(c_16727,plain,(
    r1_tarski(k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_16685])).

tff(c_264,plain,(
    ! [B_12] : k2_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_28,c_244])).

tff(c_1130,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = k2_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_1083])).

tff(c_1148,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_1130])).

tff(c_626,plain,(
    ! [A_115] : k4_xboole_0(A_115,A_115) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_622])).

tff(c_648,plain,(
    ! [A_115] : r1_tarski(k1_xboole_0,A_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_36])).

tff(c_1448,plain,(
    ! [A_115] :
      ( k1_xboole_0 = A_115
      | ~ r1_tarski(A_115,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_648,c_1427])).

tff(c_1678,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k1_xboole_0
      | ~ r1_tarski(A_147,k2_xboole_0(B_148,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1674,c_1448])).

tff(c_1721,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k1_xboole_0
      | ~ r1_tarski(A_147,B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_1678])).

tff(c_16950,plain,(
    k4_xboole_0(k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3'),k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16727,c_1721])).

tff(c_68,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,k1_tarski(B_45)) = A_44
      | r2_hidden(B_45,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_17078,plain,
    ( k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16950,c_68])).

tff(c_17140,plain,(
    r2_hidden('#skF_3',k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_13949,c_17078])).

tff(c_62,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k1_tarski(A_40),B_41)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1449,plain,(
    ! [A_40,B_41] :
      ( k1_tarski(A_40) = B_41
      | ~ r1_tarski(B_41,k1_tarski(A_40))
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_62,c_1427])).

tff(c_16949,plain,
    ( k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3') = k1_tarski('#skF_3')
    | ~ r2_hidden('#skF_3',k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_16727,c_1449])).

tff(c_23795,plain,(
    k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17140,c_16949])).

tff(c_18708,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0(k1_ordinal1('#skF_4'),'#skF_3')) = k1_ordinal1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_18491])).

tff(c_23798,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_3')) = k1_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23795,c_18708])).

tff(c_132,plain,(
    ! [A_60] : r1_tarski(A_60,k1_ordinal1(A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_50])).

tff(c_135,plain,(
    r1_tarski('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_132])).

tff(c_9667,plain,(
    ! [A_405,A_406] :
      ( r1_tarski(A_405,A_406)
      | ~ r1_xboole_0(A_405,k1_tarski(A_406))
      | ~ r1_tarski(A_405,k1_ordinal1(A_406)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2206])).

tff(c_66803,plain,(
    ! [A_1129,A_1130] :
      ( r1_tarski(A_1129,A_1130)
      | ~ r1_tarski(A_1129,k1_ordinal1(A_1130))
      | k4_xboole_0(A_1129,k1_tarski(A_1130)) != A_1129 ) ),
    inference(resolution,[status(thm)],[c_54,c_9667])).

tff(c_66906,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_135,c_66803])).

tff(c_66919,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_66906])).

tff(c_66950,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_66919])).

tff(c_23959,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_ordinal1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23795,c_36])).

tff(c_13188,plain,(
    ! [B_434] : k2_xboole_0(k1_xboole_0,B_434) = B_434 ),
    inference(superposition,[status(thm),theory(equality)],[c_10985,c_1029])).

tff(c_58344,plain,(
    ! [B_21] : k4_xboole_0(B_21,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_13190])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_67074,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66950,c_2])).

tff(c_66951,plain,(
    ! [A_1133] :
      ( r1_tarski(A_1133,'#skF_3')
      | ~ r1_tarski(A_1133,k1_ordinal1('#skF_4'))
      | k4_xboole_0(A_1133,k1_tarski('#skF_3')) != A_1133 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_66803])).

tff(c_67055,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_126,c_66951])).

tff(c_67107,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_67055])).

tff(c_67131,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_67107])).

tff(c_67141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67074,c_67131])).

tff(c_67143,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_67055])).

tff(c_69592,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_67143,c_46])).

tff(c_69687,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_69592])).

tff(c_683,plain,(
    ! [A_118,B_119] : k4_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_719,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_683])).

tff(c_69994,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_69687,c_719])).

tff(c_70113,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13188,c_58344,c_69994])).

tff(c_9802,plain,(
    ! [A_408,A_46] :
      ( k2_xboole_0(k4_xboole_0(A_408,A_46),k1_tarski(A_46)) = k1_tarski(A_46)
      | ~ r1_tarski(A_408,k1_ordinal1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_9718])).

tff(c_76144,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_3'),k1_ordinal1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70113,c_9802])).

tff(c_76454,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23959,c_76144])).

tff(c_325,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(A_80,B_81)
      | ~ r1_tarski(k1_tarski(A_80),B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_438,plain,(
    ! [A_92,B_93] : r2_hidden(A_92,k2_xboole_0(k1_tarski(A_92),B_93)) ),
    inference(resolution,[status(thm)],[c_50,c_325])).

tff(c_74,plain,(
    ! [B_49,A_48] :
      ( ~ r1_tarski(B_49,A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_456,plain,(
    ! [A_92,B_93] : ~ r1_tarski(k2_xboole_0(k1_tarski(A_92),B_93),A_92) ),
    inference(resolution,[status(thm)],[c_438,c_74])).

tff(c_79544,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_76454,c_456])).

tff(c_79618,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_79544])).

tff(c_79623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66950,c_79618])).

tff(c_79624,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_66906])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_79650,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_79624,c_32])).

tff(c_80472,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_79650])).

tff(c_76,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79636,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_79624,c_24])).

tff(c_79649,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_79636])).

tff(c_80017,plain,(
    ! [A_1217] :
      ( r1_tarski(A_1217,'#skF_3')
      | ~ r1_tarski(A_1217,k1_ordinal1('#skF_4'))
      | k4_xboole_0(A_1217,k1_tarski('#skF_3')) != A_1217 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_66803])).

tff(c_80091,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_126,c_80017])).

tff(c_80123,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_79649,c_80091])).

tff(c_81581,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_80123])).

tff(c_3640,plain,(
    ! [B_4,A_3] : k2_xboole_0(k4_xboole_0(B_4,A_3),k3_xboole_0(A_3,B_4)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3565])).

tff(c_80408,plain,(
    k2_xboole_0(k4_xboole_0('#skF_4','#skF_3'),'#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_79650,c_3640])).

tff(c_1911,plain,(
    ! [D_154,A_155,B_156] :
      ( r2_hidden(D_154,k4_xboole_0(A_155,B_156))
      | r2_hidden(D_154,B_156)
      | ~ r2_hidden(D_154,A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1985,plain,(
    ! [A_155,B_156,D_154] :
      ( ~ r1_tarski(k4_xboole_0(A_155,B_156),D_154)
      | r2_hidden(D_154,B_156)
      | ~ r2_hidden(D_154,A_155) ) ),
    inference(resolution,[status(thm)],[c_1911,c_74])).

tff(c_16652,plain,(
    ! [C_534,B_533] :
      ( r2_hidden(C_534,B_533)
      | ~ r2_hidden(C_534,k2_xboole_0(B_533,C_534)) ) ),
    inference(resolution,[status(thm)],[c_16516,c_1985])).

tff(c_85944,plain,
    ( r2_hidden('#skF_3',k4_xboole_0('#skF_4','#skF_3'))
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_80408,c_16652])).

tff(c_86131,plain,(
    r2_hidden('#skF_3',k4_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81581,c_85944])).

tff(c_9869,plain,(
    ! [A_412,B_413,C_414] :
      ( r1_tarski(k4_xboole_0(A_412,B_413),C_414)
      | ~ r1_tarski(A_412,k2_xboole_0(k3_xboole_0(A_412,B_413),C_414)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1674])).

tff(c_116678,plain,(
    ! [A_1468,B_1469] :
      ( r1_tarski(k4_xboole_0(A_1468,B_1469),k1_tarski(k3_xboole_0(A_1468,B_1469)))
      | ~ r1_tarski(A_1468,k1_ordinal1(k3_xboole_0(A_1468,B_1469))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_9869])).

tff(c_116743,plain,
    ( r1_tarski(k4_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_3'))
    | ~ r1_tarski('#skF_4',k1_ordinal1(k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_80472,c_116678])).

tff(c_116969,plain,(
    r1_tarski(k4_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_78,c_80472,c_116743])).

tff(c_117053,plain,
    ( k4_xboole_0('#skF_4','#skF_3') = k1_tarski('#skF_3')
    | ~ r2_hidden('#skF_3',k4_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_116969,c_1449])).

tff(c_117092,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86131,c_117053])).

tff(c_12145,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_11990])).

tff(c_117349,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_117092,c_12145])).

tff(c_117561,plain,(
    k1_ordinal1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23798,c_80472,c_4,c_117349])).

tff(c_117563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23610,c_117561])).

tff(c_117564,plain,(
    k1_ordinal1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13289])).

tff(c_85,plain,(
    ! [A_51] : r2_hidden(A_51,k1_ordinal1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_88,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_85])).

tff(c_237,plain,(
    ~ r1_tarski(k1_ordinal1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_230])).

tff(c_117608,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117564,c_237])).

tff(c_117621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_117608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.05/20.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.16/20.81  
% 31.16/20.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.16/20.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 31.16/20.81  
% 31.16/20.81  %Foreground sorts:
% 31.16/20.81  
% 31.16/20.81  
% 31.16/20.81  %Background operators:
% 31.16/20.81  
% 31.16/20.81  
% 31.16/20.81  %Foreground operators:
% 31.16/20.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 31.16/20.81  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 31.16/20.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.16/20.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.16/20.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 31.16/20.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 31.16/20.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.16/20.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.16/20.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 31.16/20.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 31.16/20.81  tff('#skF_3', type, '#skF_3': $i).
% 31.16/20.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 31.16/20.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 31.16/20.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.16/20.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 31.16/20.81  tff('#skF_4', type, '#skF_4': $i).
% 31.16/20.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.16/20.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 31.16/20.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 31.16/20.81  
% 31.16/20.84  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 31.16/20.84  tff(f_101, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 31.16/20.84  tff(f_80, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 31.16/20.84  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 31.16/20.84  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 31.16/20.84  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 31.16/20.84  tff(f_84, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 31.16/20.84  tff(f_103, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 31.16/20.84  tff(f_108, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 31.16/20.84  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 31.16/20.84  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 31.16/20.84  tff(f_60, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 31.16/20.84  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 31.16/20.84  tff(f_78, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 31.16/20.84  tff(f_58, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 31.16/20.84  tff(f_64, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 31.16/20.84  tff(f_113, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 31.16/20.84  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 31.16/20.84  tff(f_99, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 31.16/20.84  tff(f_92, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 31.16/20.84  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 31.16/20.84  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 31.16/20.84  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 31.16/20.84  tff(c_120, plain, (![A_59]: (k2_xboole_0(A_59, k1_tarski(A_59))=k1_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_101])).
% 31.16/20.84  tff(c_50, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 31.16/20.84  tff(c_126, plain, (![A_59]: (r1_tarski(A_59, k1_ordinal1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_50])).
% 31.16/20.84  tff(c_350, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_56])).
% 31.16/20.84  tff(c_367, plain, (![A_59]: (k3_xboole_0(A_59, k1_ordinal1(A_59))=A_59)), inference(resolution, [status(thm)], [c_126, c_350])).
% 31.16/20.84  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.16/20.84  tff(c_46, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_72])).
% 31.16/20.84  tff(c_54, plain, (![A_35, B_36]: (r1_xboole_0(A_35, B_36) | k4_xboole_0(A_35, B_36)!=A_35)), inference(cnfTransformation, [status(thm)], [f_84])).
% 31.16/20.84  tff(c_72, plain, (![A_47]: (r2_hidden(A_47, k1_ordinal1(A_47)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 31.16/20.84  tff(c_230, plain, (![B_67, A_68]: (~r1_tarski(B_67, A_68) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_108])).
% 31.16/20.84  tff(c_238, plain, (![A_47]: (~r1_tarski(k1_ordinal1(A_47), A_47))), inference(resolution, [status(thm)], [c_72, c_230])).
% 31.16/20.84  tff(c_244, plain, (![A_72, B_73]: (k2_xboole_0(A_72, B_73)=B_73 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_52])).
% 31.16/20.84  tff(c_261, plain, (![A_59]: (k2_xboole_0(A_59, k1_ordinal1(A_59))=k1_ordinal1(A_59))), inference(resolution, [status(thm)], [c_126, c_244])).
% 31.16/20.84  tff(c_38, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 31.16/20.84  tff(c_595, plain, (![A_113, B_114]: (k4_xboole_0(A_113, k4_xboole_0(A_113, B_114))=k3_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_72])).
% 31.16/20.84  tff(c_36, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 31.16/20.84  tff(c_262, plain, (![A_18, B_19]: (k2_xboole_0(k4_xboole_0(A_18, B_19), A_18)=A_18)), inference(resolution, [status(thm)], [c_36, c_244])).
% 31.16/20.84  tff(c_607, plain, (![A_113, B_114]: (k2_xboole_0(k3_xboole_0(A_113, B_114), A_113)=A_113)), inference(superposition, [status(thm), theory('equality')], [c_595, c_262])).
% 31.16/20.84  tff(c_44, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 31.16/20.84  tff(c_1083, plain, (![A_131, B_132]: (k2_xboole_0(A_131, k4_xboole_0(B_132, A_131))=k2_xboole_0(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_62])).
% 31.16/20.84  tff(c_1127, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=k2_xboole_0(k3_xboole_0(A_26, B_27), A_26))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1083])).
% 31.16/20.84  tff(c_11990, plain, (![A_442, B_443]: (k2_xboole_0(k3_xboole_0(A_442, B_443), k4_xboole_0(A_442, B_443))=A_442)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_1127])).
% 31.16/20.84  tff(c_18491, plain, (![A_563, B_564]: (k2_xboole_0(k3_xboole_0(A_563, B_564), k4_xboole_0(B_564, A_563))=B_564)), inference(superposition, [status(thm), theory('equality')], [c_4, c_11990])).
% 31.16/20.84  tff(c_23307, plain, (![A_609]: (k2_xboole_0(A_609, k4_xboole_0(k1_ordinal1(A_609), A_609))=k1_ordinal1(A_609))), inference(superposition, [status(thm), theory('equality')], [c_367, c_18491])).
% 31.16/20.84  tff(c_2206, plain, (![A_162, B_163, C_164]: (r1_tarski(A_162, B_163) | ~r1_xboole_0(A_162, C_164) | ~r1_tarski(A_162, k2_xboole_0(B_163, C_164)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 31.16/20.84  tff(c_2286, plain, (![B_163, C_164]: (r1_tarski(k2_xboole_0(B_163, C_164), B_163) | ~r1_xboole_0(k2_xboole_0(B_163, C_164), C_164))), inference(resolution, [status(thm)], [c_28, c_2206])).
% 31.16/20.84  tff(c_23416, plain, (![A_609]: (r1_tarski(k2_xboole_0(A_609, k4_xboole_0(k1_ordinal1(A_609), A_609)), A_609) | ~r1_xboole_0(k1_ordinal1(A_609), k4_xboole_0(k1_ordinal1(A_609), A_609)))), inference(superposition, [status(thm), theory('equality')], [c_23307, c_2286])).
% 31.16/20.84  tff(c_23565, plain, (![A_609]: (r1_tarski(k1_ordinal1(A_609), A_609) | ~r1_xboole_0(k1_ordinal1(A_609), k4_xboole_0(k1_ordinal1(A_609), A_609)))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_38, c_23416])).
% 31.16/20.84  tff(c_23582, plain, (![A_610]: (~r1_xboole_0(k1_ordinal1(A_610), k4_xboole_0(k1_ordinal1(A_610), A_610)))), inference(negUnitSimplification, [status(thm)], [c_238, c_23565])).
% 31.16/20.84  tff(c_23601, plain, (![A_610]: (k4_xboole_0(k1_ordinal1(A_610), k4_xboole_0(k1_ordinal1(A_610), A_610))!=k1_ordinal1(A_610))), inference(resolution, [status(thm)], [c_54, c_23582])).
% 31.16/20.84  tff(c_23610, plain, (![A_610]: (k1_ordinal1(A_610)!=A_610)), inference(demodulation, [status(thm), theory('equality')], [c_367, c_4, c_46, c_23601])).
% 31.16/20.84  tff(c_34, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 31.16/20.84  tff(c_40, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 31.16/20.84  tff(c_622, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_595])).
% 31.16/20.84  tff(c_625, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_622])).
% 31.16/20.84  tff(c_7086, plain, (![B_325, C_326]: (r1_tarski(k2_xboole_0(B_325, C_326), B_325) | ~r1_xboole_0(k2_xboole_0(B_325, C_326), C_326))), inference(resolution, [status(thm)], [c_28, c_2206])).
% 31.16/20.84  tff(c_7122, plain, (![A_18, B_19]: (r1_tarski(k2_xboole_0(k4_xboole_0(A_18, B_19), A_18), k4_xboole_0(A_18, B_19)) | ~r1_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_262, c_7086])).
% 31.16/20.84  tff(c_10093, plain, (![A_418, B_419]: (r1_tarski(A_418, k4_xboole_0(A_418, B_419)) | ~r1_xboole_0(A_418, A_418))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_7122])).
% 31.16/20.84  tff(c_1427, plain, (![B_140, A_141]: (B_140=A_141 | ~r1_tarski(B_140, A_141) | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_48])).
% 31.16/20.84  tff(c_1452, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_36, c_1427])).
% 31.16/20.84  tff(c_10185, plain, (![A_420, B_421]: (k4_xboole_0(A_420, B_421)=A_420 | ~r1_xboole_0(A_420, A_420))), inference(resolution, [status(thm)], [c_10093, c_1452])).
% 31.16/20.84  tff(c_10188, plain, (![B_36, B_421]: (k4_xboole_0(B_36, B_421)=B_36 | k4_xboole_0(B_36, B_36)!=B_36)), inference(resolution, [status(thm)], [c_54, c_10185])).
% 31.16/20.84  tff(c_10193, plain, (![B_422, B_423]: (k4_xboole_0(B_422, B_423)=B_422 | k1_xboole_0!=B_422)), inference(demodulation, [status(thm), theory('equality')], [c_625, c_10188])).
% 31.16/20.84  tff(c_10985, plain, (![A_433, B_434]: (k3_xboole_0(A_433, B_434)=A_433 | k1_xboole_0!=A_433)), inference(superposition, [status(thm), theory('equality')], [c_46, c_10193])).
% 31.16/20.84  tff(c_958, plain, (![A_126, B_127]: (r1_tarski(k3_xboole_0(A_126, B_127), A_126))), inference(superposition, [status(thm), theory('equality')], [c_595, c_36])).
% 31.16/20.84  tff(c_997, plain, (![B_128, A_129]: (r1_tarski(k3_xboole_0(B_128, A_129), A_129))), inference(superposition, [status(thm), theory('equality')], [c_4, c_958])).
% 31.16/20.84  tff(c_30, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 31.16/20.84  tff(c_1029, plain, (![B_128, A_129]: (k2_xboole_0(k3_xboole_0(B_128, A_129), A_129)=A_129)), inference(resolution, [status(thm)], [c_997, c_30])).
% 31.16/20.84  tff(c_13190, plain, (![A_454, B_455]: (k2_xboole_0(A_454, B_455)=B_455 | k1_xboole_0!=A_454)), inference(superposition, [status(thm), theory('equality')], [c_10985, c_1029])).
% 31.16/20.84  tff(c_78, plain, (k1_ordinal1('#skF_3')=k1_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 31.16/20.84  tff(c_401, plain, (![A_88]: (k3_xboole_0(A_88, k1_ordinal1(A_88))=A_88)), inference(resolution, [status(thm)], [c_126, c_350])).
% 31.16/20.84  tff(c_418, plain, (k3_xboole_0('#skF_3', k1_ordinal1('#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_78, c_401])).
% 31.16/20.84  tff(c_1133, plain, (![A_28, B_29]: (k2_xboole_0(k4_xboole_0(A_28, B_29), k3_xboole_0(A_28, B_29))=k2_xboole_0(k4_xboole_0(A_28, B_29), A_28))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1083])).
% 31.16/20.84  tff(c_3565, plain, (![A_220, B_221]: (k2_xboole_0(k4_xboole_0(A_220, B_221), k3_xboole_0(A_220, B_221))=A_220)), inference(demodulation, [status(thm), theory('equality')], [c_262, c_1133])).
% 31.16/20.84  tff(c_4132, plain, (![B_232, A_233]: (k2_xboole_0(k4_xboole_0(B_232, A_233), k3_xboole_0(A_233, B_232))=B_232)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3565])).
% 31.16/20.84  tff(c_4209, plain, (k2_xboole_0(k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'), '#skF_3')=k1_ordinal1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_418, c_4132])).
% 31.16/20.84  tff(c_13289, plain, (k1_ordinal1('#skF_4')='#skF_3' | k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13190, c_4209])).
% 31.16/20.84  tff(c_13949, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13289])).
% 31.16/20.84  tff(c_70, plain, (![A_46]: (k2_xboole_0(A_46, k1_tarski(A_46))=k1_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_101])).
% 31.16/20.84  tff(c_1674, plain, (![A_147, B_148, C_149]: (r1_tarski(k4_xboole_0(A_147, B_148), C_149) | ~r1_tarski(A_147, k2_xboole_0(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 31.16/20.84  tff(c_9718, plain, (![A_408, B_409, C_410]: (k2_xboole_0(k4_xboole_0(A_408, B_409), C_410)=C_410 | ~r1_tarski(A_408, k2_xboole_0(B_409, C_410)))), inference(resolution, [status(thm)], [c_1674, c_30])).
% 31.16/20.84  tff(c_16300, plain, (![B_531, C_532]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_531, C_532), B_531), C_532)=C_532)), inference(resolution, [status(thm)], [c_28, c_9718])).
% 31.16/20.84  tff(c_16516, plain, (![B_533, C_534]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_533, C_534), B_533), C_534))), inference(superposition, [status(thm), theory('equality')], [c_16300, c_50])).
% 31.16/20.84  tff(c_16685, plain, (![A_535]: (r1_tarski(k4_xboole_0(k1_ordinal1(A_535), A_535), k1_tarski(A_535)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_16516])).
% 31.16/20.84  tff(c_16727, plain, (r1_tarski(k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_16685])).
% 31.16/20.84  tff(c_264, plain, (![B_12]: (k2_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_28, c_244])).
% 31.16/20.84  tff(c_1130, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=k2_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_625, c_1083])).
% 31.16/20.84  tff(c_1148, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_1130])).
% 31.16/20.84  tff(c_626, plain, (![A_115]: (k4_xboole_0(A_115, A_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_622])).
% 31.16/20.84  tff(c_648, plain, (![A_115]: (r1_tarski(k1_xboole_0, A_115))), inference(superposition, [status(thm), theory('equality')], [c_626, c_36])).
% 31.16/20.84  tff(c_1448, plain, (![A_115]: (k1_xboole_0=A_115 | ~r1_tarski(A_115, k1_xboole_0))), inference(resolution, [status(thm)], [c_648, c_1427])).
% 31.16/20.84  tff(c_1678, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k1_xboole_0 | ~r1_tarski(A_147, k2_xboole_0(B_148, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1674, c_1448])).
% 31.16/20.84  tff(c_1721, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k1_xboole_0 | ~r1_tarski(A_147, B_148))), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_1678])).
% 31.16/20.84  tff(c_16950, plain, (k4_xboole_0(k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'), k1_tarski('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_16727, c_1721])).
% 31.16/20.84  tff(c_68, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k1_tarski(B_45))=A_44 | r2_hidden(B_45, A_44))), inference(cnfTransformation, [status(thm)], [f_99])).
% 31.16/20.84  tff(c_17078, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16950, c_68])).
% 31.16/20.84  tff(c_17140, plain, (r2_hidden('#skF_3', k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_13949, c_17078])).
% 31.16/20.84  tff(c_62, plain, (![A_40, B_41]: (r1_tarski(k1_tarski(A_40), B_41) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_92])).
% 31.16/20.84  tff(c_1449, plain, (![A_40, B_41]: (k1_tarski(A_40)=B_41 | ~r1_tarski(B_41, k1_tarski(A_40)) | ~r2_hidden(A_40, B_41))), inference(resolution, [status(thm)], [c_62, c_1427])).
% 31.16/20.84  tff(c_16949, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_16727, c_1449])).
% 31.16/20.84  tff(c_23795, plain, (k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17140, c_16949])).
% 31.16/20.84  tff(c_18708, plain, (k2_xboole_0('#skF_3', k4_xboole_0(k1_ordinal1('#skF_4'), '#skF_3'))=k1_ordinal1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_418, c_18491])).
% 31.16/20.84  tff(c_23798, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_3'))=k1_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23795, c_18708])).
% 31.16/20.84  tff(c_132, plain, (![A_60]: (r1_tarski(A_60, k1_ordinal1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_50])).
% 31.16/20.84  tff(c_135, plain, (r1_tarski('#skF_3', k1_ordinal1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_132])).
% 31.16/20.84  tff(c_9667, plain, (![A_405, A_406]: (r1_tarski(A_405, A_406) | ~r1_xboole_0(A_405, k1_tarski(A_406)) | ~r1_tarski(A_405, k1_ordinal1(A_406)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2206])).
% 31.16/20.84  tff(c_66803, plain, (![A_1129, A_1130]: (r1_tarski(A_1129, A_1130) | ~r1_tarski(A_1129, k1_ordinal1(A_1130)) | k4_xboole_0(A_1129, k1_tarski(A_1130))!=A_1129)), inference(resolution, [status(thm)], [c_54, c_9667])).
% 31.16/20.84  tff(c_66906, plain, (r1_tarski('#skF_3', '#skF_4') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_135, c_66803])).
% 31.16/20.84  tff(c_66919, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_66906])).
% 31.16/20.84  tff(c_66950, plain, (r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_68, c_66919])).
% 31.16/20.84  tff(c_23959, plain, (r1_tarski(k1_tarski('#skF_3'), k1_ordinal1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_23795, c_36])).
% 31.16/20.84  tff(c_13188, plain, (![B_434]: (k2_xboole_0(k1_xboole_0, B_434)=B_434)), inference(superposition, [status(thm), theory('equality')], [c_10985, c_1029])).
% 31.16/20.84  tff(c_58344, plain, (![B_21]: (k4_xboole_0(B_21, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_21))), inference(superposition, [status(thm), theory('equality')], [c_38, c_13190])).
% 31.16/20.84  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 31.16/20.84  tff(c_67074, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66950, c_2])).
% 31.16/20.84  tff(c_66951, plain, (![A_1133]: (r1_tarski(A_1133, '#skF_3') | ~r1_tarski(A_1133, k1_ordinal1('#skF_4')) | k4_xboole_0(A_1133, k1_tarski('#skF_3'))!=A_1133)), inference(superposition, [status(thm), theory('equality')], [c_78, c_66803])).
% 31.16/20.84  tff(c_67055, plain, (r1_tarski('#skF_4', '#skF_3') | k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(resolution, [status(thm)], [c_126, c_66951])).
% 31.16/20.84  tff(c_67107, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_67055])).
% 31.16/20.84  tff(c_67131, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_68, c_67107])).
% 31.16/20.84  tff(c_67141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67074, c_67131])).
% 31.16/20.84  tff(c_67143, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(splitRight, [status(thm)], [c_67055])).
% 31.16/20.84  tff(c_69592, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67143, c_46])).
% 31.16/20.84  tff(c_69687, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_625, c_69592])).
% 31.16/20.84  tff(c_683, plain, (![A_118, B_119]: (k4_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_70])).
% 31.16/20.84  tff(c_719, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_683])).
% 31.16/20.84  tff(c_69994, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_69687, c_719])).
% 31.16/20.84  tff(c_70113, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13188, c_58344, c_69994])).
% 31.16/20.84  tff(c_9802, plain, (![A_408, A_46]: (k2_xboole_0(k4_xboole_0(A_408, A_46), k1_tarski(A_46))=k1_tarski(A_46) | ~r1_tarski(A_408, k1_ordinal1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_9718])).
% 31.16/20.84  tff(c_76144, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_3'), k1_ordinal1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70113, c_9802])).
% 31.16/20.84  tff(c_76454, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23959, c_76144])).
% 31.16/20.84  tff(c_325, plain, (![A_80, B_81]: (r2_hidden(A_80, B_81) | ~r1_tarski(k1_tarski(A_80), B_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 31.16/20.84  tff(c_438, plain, (![A_92, B_93]: (r2_hidden(A_92, k2_xboole_0(k1_tarski(A_92), B_93)))), inference(resolution, [status(thm)], [c_50, c_325])).
% 31.16/20.84  tff(c_74, plain, (![B_49, A_48]: (~r1_tarski(B_49, A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_108])).
% 31.16/20.84  tff(c_456, plain, (![A_92, B_93]: (~r1_tarski(k2_xboole_0(k1_tarski(A_92), B_93), A_92))), inference(resolution, [status(thm)], [c_438, c_74])).
% 31.16/20.84  tff(c_79544, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_76454, c_456])).
% 31.16/20.84  tff(c_79618, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_79544])).
% 31.16/20.84  tff(c_79623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66950, c_79618])).
% 31.16/20.84  tff(c_79624, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_66906])).
% 31.16/20.84  tff(c_32, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 31.16/20.84  tff(c_79650, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_79624, c_32])).
% 31.16/20.84  tff(c_80472, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4, c_79650])).
% 31.16/20.84  tff(c_76, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 31.16/20.84  tff(c_24, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 31.16/20.84  tff(c_79636, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_79624, c_24])).
% 31.16/20.84  tff(c_79649, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_79636])).
% 31.16/20.84  tff(c_80017, plain, (![A_1217]: (r1_tarski(A_1217, '#skF_3') | ~r1_tarski(A_1217, k1_ordinal1('#skF_4')) | k4_xboole_0(A_1217, k1_tarski('#skF_3'))!=A_1217)), inference(superposition, [status(thm), theory('equality')], [c_78, c_66803])).
% 31.16/20.84  tff(c_80091, plain, (r1_tarski('#skF_4', '#skF_3') | k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(resolution, [status(thm)], [c_126, c_80017])).
% 31.16/20.84  tff(c_80123, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_79649, c_80091])).
% 31.16/20.84  tff(c_81581, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_68, c_80123])).
% 31.16/20.84  tff(c_3640, plain, (![B_4, A_3]: (k2_xboole_0(k4_xboole_0(B_4, A_3), k3_xboole_0(A_3, B_4))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3565])).
% 31.16/20.84  tff(c_80408, plain, (k2_xboole_0(k4_xboole_0('#skF_4', '#skF_3'), '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_79650, c_3640])).
% 31.16/20.84  tff(c_1911, plain, (![D_154, A_155, B_156]: (r2_hidden(D_154, k4_xboole_0(A_155, B_156)) | r2_hidden(D_154, B_156) | ~r2_hidden(D_154, A_155))), inference(cnfTransformation, [status(thm)], [f_42])).
% 31.16/20.84  tff(c_1985, plain, (![A_155, B_156, D_154]: (~r1_tarski(k4_xboole_0(A_155, B_156), D_154) | r2_hidden(D_154, B_156) | ~r2_hidden(D_154, A_155))), inference(resolution, [status(thm)], [c_1911, c_74])).
% 31.16/20.84  tff(c_16652, plain, (![C_534, B_533]: (r2_hidden(C_534, B_533) | ~r2_hidden(C_534, k2_xboole_0(B_533, C_534)))), inference(resolution, [status(thm)], [c_16516, c_1985])).
% 31.16/20.84  tff(c_85944, plain, (r2_hidden('#skF_3', k4_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_80408, c_16652])).
% 31.16/20.84  tff(c_86131, plain, (r2_hidden('#skF_3', k4_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_81581, c_85944])).
% 31.16/20.84  tff(c_9869, plain, (![A_412, B_413, C_414]: (r1_tarski(k4_xboole_0(A_412, B_413), C_414) | ~r1_tarski(A_412, k2_xboole_0(k3_xboole_0(A_412, B_413), C_414)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1674])).
% 31.16/20.84  tff(c_116678, plain, (![A_1468, B_1469]: (r1_tarski(k4_xboole_0(A_1468, B_1469), k1_tarski(k3_xboole_0(A_1468, B_1469))) | ~r1_tarski(A_1468, k1_ordinal1(k3_xboole_0(A_1468, B_1469))))), inference(superposition, [status(thm), theory('equality')], [c_70, c_9869])).
% 31.16/20.84  tff(c_116743, plain, (r1_tarski(k4_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_3')) | ~r1_tarski('#skF_4', k1_ordinal1(k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_80472, c_116678])).
% 31.16/20.84  tff(c_116969, plain, (r1_tarski(k4_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_78, c_80472, c_116743])).
% 31.16/20.84  tff(c_117053, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', k4_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_116969, c_1449])).
% 31.16/20.84  tff(c_117092, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86131, c_117053])).
% 31.16/20.84  tff(c_12145, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_11990])).
% 31.16/20.84  tff(c_117349, plain, (k2_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_117092, c_12145])).
% 31.16/20.84  tff(c_117561, plain, (k1_ordinal1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23798, c_80472, c_4, c_117349])).
% 31.16/20.84  tff(c_117563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23610, c_117561])).
% 31.16/20.84  tff(c_117564, plain, (k1_ordinal1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_13289])).
% 31.16/20.84  tff(c_85, plain, (![A_51]: (r2_hidden(A_51, k1_ordinal1(A_51)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 31.16/20.84  tff(c_88, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_85])).
% 31.16/20.84  tff(c_237, plain, (~r1_tarski(k1_ordinal1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_88, c_230])).
% 31.16/20.84  tff(c_117608, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_117564, c_237])).
% 31.16/20.84  tff(c_117621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_117608])).
% 31.16/20.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.16/20.84  
% 31.16/20.84  Inference rules
% 31.16/20.84  ----------------------
% 31.16/20.84  #Ref     : 4
% 31.16/20.84  #Sup     : 31046
% 31.16/20.84  #Fact    : 0
% 31.16/20.84  #Define  : 0
% 31.16/20.84  #Split   : 9
% 31.16/20.84  #Chain   : 0
% 31.16/20.84  #Close   : 0
% 31.16/20.84  
% 31.16/20.84  Ordering : KBO
% 31.16/20.84  
% 31.16/20.84  Simplification rules
% 31.16/20.84  ----------------------
% 31.16/20.84  #Subsume      : 16342
% 31.16/20.84  #Demod        : 14698
% 31.16/20.84  #Tautology    : 5938
% 31.16/20.84  #SimpNegUnit  : 1378
% 31.16/20.84  #BackRed      : 113
% 31.16/20.84  
% 31.16/20.84  #Partial instantiations: 0
% 31.16/20.84  #Strategies tried      : 1
% 31.16/20.84  
% 31.16/20.84  Timing (in seconds)
% 31.16/20.84  ----------------------
% 31.16/20.85  Preprocessing        : 0.36
% 31.16/20.85  Parsing              : 0.20
% 31.16/20.85  CNF conversion       : 0.02
% 31.16/20.85  Main loop            : 19.62
% 31.16/20.85  Inferencing          : 2.11
% 31.16/20.85  Reduction            : 9.75
% 31.16/20.85  Demodulation         : 7.01
% 31.16/20.85  BG Simplification    : 0.20
% 31.16/20.85  Subsumption          : 6.52
% 31.16/20.85  Abstraction          : 0.33
% 31.16/20.85  MUC search           : 0.00
% 31.16/20.85  Cooper               : 0.00
% 31.16/20.85  Total                : 20.04
% 31.16/20.85  Index Insertion      : 0.00
% 31.16/20.85  Index Deletion       : 0.00
% 31.16/20.85  Index Matching       : 0.00
% 31.16/20.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
