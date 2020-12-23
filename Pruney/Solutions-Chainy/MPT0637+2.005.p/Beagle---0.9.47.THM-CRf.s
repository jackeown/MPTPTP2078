%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:24 EST 2020

% Result     : Theorem 12.48s
% Output     : CNFRefutation 12.84s
% Verified   : 
% Statistics : Number of formulae       :  123 (1027 expanded)
%              Number of leaves         :   30 ( 371 expanded)
%              Depth                    :   27
%              Number of atoms          :  212 (1758 expanded)
%              Number of equality atoms :   74 ( 618 expanded)
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

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_389,plain,(
    ! [B_81,A_82] :
      ( k7_relat_1(B_81,k3_xboole_0(k1_relat_1(B_81),A_82)) = k7_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_213,plain,(
    ! [A_59,B_60] :
      ( k5_relat_1(k6_relat_1(A_59),B_60) = k7_relat_1(B_60,A_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k5_relat_1(B_28,k6_relat_1(A_27)),B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_220,plain,(
    ! [A_27,A_59] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_27),A_59),k6_relat_1(A_59))
      | ~ v1_relat_1(k6_relat_1(A_59))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_32])).

tff(c_235,plain,(
    ! [A_27,A_59] : r1_tarski(k7_relat_1(k6_relat_1(A_27),A_59),k6_relat_1(A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_220])).

tff(c_403,plain,(
    ! [A_27,A_82] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_27),A_82),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_27)),A_82)))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_235])).

tff(c_429,plain,(
    ! [A_27,A_82] : r1_tarski(k7_relat_1(k6_relat_1(A_27),A_82),k6_relat_1(k3_xboole_0(A_27,A_82))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_26,c_403])).

tff(c_10,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [B_45,A_46] : k1_setfam_1(k2_tarski(B_45,A_46)) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_14,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_124,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_14])).

tff(c_424,plain,(
    ! [A_26,A_82] :
      ( k7_relat_1(k6_relat_1(A_26),k3_xboole_0(A_26,A_82)) = k7_relat_1(k6_relat_1(A_26),A_82)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_389])).

tff(c_560,plain,(
    ! [A_93,A_94] : k7_relat_1(k6_relat_1(A_93),k3_xboole_0(A_93,A_94)) = k7_relat_1(k6_relat_1(A_93),A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_424])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_27),B_28),B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_226,plain,(
    ! [B_60,A_59] :
      ( r1_tarski(k7_relat_1(B_60,A_59),B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_30])).

tff(c_578,plain,(
    ! [A_93,A_94] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_93),A_94),k6_relat_1(A_93))
      | ~ v1_relat_1(k6_relat_1(A_93))
      | ~ v1_relat_1(k6_relat_1(A_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_226])).

tff(c_603,plain,(
    ! [A_93,A_94] : r1_tarski(k7_relat_1(k6_relat_1(A_93),A_94),k6_relat_1(A_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_578])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_257,plain,(
    ! [B_69,A_70] :
      ( k7_relat_1(B_69,A_70) = B_69
      | ~ r1_tarski(k1_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_260,plain,(
    ! [A_26,A_70] :
      ( k7_relat_1(k6_relat_1(A_26),A_70) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_70)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_257])).

tff(c_266,plain,(
    ! [A_26,A_70] :
      ( k7_relat_1(k6_relat_1(A_26),A_70) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_260])).

tff(c_435,plain,(
    ! [A_83,A_84] : r1_tarski(k7_relat_1(k6_relat_1(A_83),A_84),k6_relat_1(k3_xboole_0(A_83,A_84))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_26,c_403])).

tff(c_444,plain,(
    ! [A_26,A_70] :
      ( r1_tarski(k6_relat_1(A_26),k6_relat_1(k3_xboole_0(A_26,A_70)))
      | ~ r1_tarski(A_26,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_435])).

tff(c_318,plain,(
    ! [A_73,A_74] :
      ( k7_relat_1(k6_relat_1(A_73),A_74) = k6_relat_1(A_73)
      | ~ r1_tarski(A_73,A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_260])).

tff(c_371,plain,(
    ! [A_75,A_76] :
      ( r1_tarski(k6_relat_1(A_75),k6_relat_1(A_76))
      | ~ r1_tarski(A_75,A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_235])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1103,plain,(
    ! [A_129,A_128] :
      ( k6_relat_1(A_129) = k6_relat_1(A_128)
      | ~ r1_tarski(k6_relat_1(A_128),k6_relat_1(A_129))
      | ~ r1_tarski(A_129,A_128) ) ),
    inference(resolution,[status(thm)],[c_371,c_2])).

tff(c_1112,plain,(
    ! [A_26,A_70] :
      ( k6_relat_1(k3_xboole_0(A_26,A_70)) = k6_relat_1(A_26)
      | ~ r1_tarski(k3_xboole_0(A_26,A_70),A_26)
      | ~ r1_tarski(A_26,A_70) ) ),
    inference(resolution,[status(thm)],[c_444,c_1103])).

tff(c_1636,plain,(
    ! [A_141,A_142] :
      ( k6_relat_1(k3_xboole_0(A_141,A_142)) = k6_relat_1(A_141)
      | ~ r1_tarski(A_141,A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1112])).

tff(c_1741,plain,(
    ! [A_141,A_142] :
      ( k3_xboole_0(A_141,A_142) = k1_relat_1(k6_relat_1(A_141))
      | ~ r1_tarski(A_141,A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1636,c_26])).

tff(c_1777,plain,(
    ! [A_143,A_144] :
      ( k3_xboole_0(A_143,A_144) = A_143
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1741])).

tff(c_22240,plain,(
    ! [A_394,A_395] : k3_xboole_0(k7_relat_1(k6_relat_1(A_394),A_395),k6_relat_1(A_394)) = k7_relat_1(k6_relat_1(A_394),A_395) ),
    inference(resolution,[status(thm)],[c_603,c_1777])).

tff(c_22620,plain,(
    ! [A_394,A_395] : k3_xboole_0(k6_relat_1(A_394),k7_relat_1(k6_relat_1(A_394),A_395)) = k7_relat_1(k6_relat_1(A_394),A_395) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_22240])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_268,plain,(
    ! [B_71] :
      ( k7_relat_1(B_71,k1_relat_1(B_71)) = B_71
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_287,plain,(
    ! [A_26] :
      ( k7_relat_1(k6_relat_1(A_26),A_26) = k6_relat_1(A_26)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_268])).

tff(c_294,plain,(
    ! [A_26] : k7_relat_1(k6_relat_1(A_26),A_26) = k6_relat_1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_287])).

tff(c_1968,plain,(
    ! [A_147,B_148] : k3_xboole_0(k3_xboole_0(A_147,B_148),A_147) = k3_xboole_0(A_147,B_148) ),
    inference(resolution,[status(thm)],[c_8,c_1777])).

tff(c_434,plain,(
    ! [A_26,A_82] : k7_relat_1(k6_relat_1(A_26),k3_xboole_0(A_26,A_82)) = k7_relat_1(k6_relat_1(A_26),A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_424])).

tff(c_2016,plain,(
    ! [A_147,B_148] : k7_relat_1(k6_relat_1(k3_xboole_0(A_147,B_148)),k3_xboole_0(A_147,B_148)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_147,B_148)),A_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_1968,c_434])).

tff(c_2093,plain,(
    ! [A_147,B_148] : k7_relat_1(k6_relat_1(k3_xboole_0(A_147,B_148)),A_147) = k6_relat_1(k3_xboole_0(A_147,B_148)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_2016])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,k3_xboole_0(k1_relat_1(B_18),A_17)) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1807,plain,(
    ! [B_60,A_59] :
      ( k3_xboole_0(k7_relat_1(B_60,A_59),B_60) = k7_relat_1(B_60,A_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_226,c_1777])).

tff(c_5661,plain,(
    ! [B_212,A_213] :
      ( k3_xboole_0(B_212,k7_relat_1(B_212,A_213)) = k7_relat_1(B_212,A_213)
      | ~ v1_relat_1(B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_1807])).

tff(c_5806,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,k3_xboole_0(k1_relat_1(B_18),A_17)) = k3_xboole_0(B_18,k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5661])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k5_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_223,plain,(
    ! [B_60,A_59] :
      ( v1_relat_1(k7_relat_1(B_60,A_59))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k6_relat_1(A_59))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_16])).

tff(c_237,plain,(
    ! [B_60,A_59] :
      ( v1_relat_1(k7_relat_1(B_60,A_59))
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_223])).

tff(c_584,plain,(
    ! [A_93,A_94] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_93),A_94))
      | ~ v1_relat_1(k6_relat_1(A_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_237])).

tff(c_606,plain,(
    ! [A_93,A_94] : v1_relat_1(k7_relat_1(k6_relat_1(A_93),A_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_584])).

tff(c_23428,plain,(
    ! [A_402,A_403] : k3_xboole_0(k6_relat_1(A_402),k7_relat_1(k6_relat_1(A_402),A_403)) = k7_relat_1(k6_relat_1(A_402),A_403) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_22240])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( k5_relat_1(k6_relat_1(A_29),B_30) = k7_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1131,plain,(
    ! [A_26,A_70] :
      ( k6_relat_1(k3_xboole_0(A_26,A_70)) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1112])).

tff(c_141,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_14])).

tff(c_156,plain,(
    ! [B_47,A_48] : r1_tarski(k3_xboole_0(B_47,A_48),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_2476,plain,(
    ! [B_158,A_159] : k3_xboole_0(k3_xboole_0(B_158,A_159),A_159) = k3_xboole_0(A_159,B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_1968])).

tff(c_2504,plain,(
    ! [B_158,A_159] :
      ( k6_relat_1(k3_xboole_0(B_158,A_159)) = k6_relat_1(k3_xboole_0(A_159,B_158))
      | ~ r1_tarski(k3_xboole_0(B_158,A_159),A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2476,c_1131])).

tff(c_3501,plain,(
    ! [B_177,A_178] : k6_relat_1(k3_xboole_0(B_177,A_178)) = k6_relat_1(k3_xboole_0(A_178,B_177)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_2504])).

tff(c_3821,plain,(
    ! [B_179,A_180] : k1_relat_1(k6_relat_1(k3_xboole_0(B_179,A_180))) = k3_xboole_0(A_180,B_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_3501,c_26])).

tff(c_3878,plain,(
    ! [A_70,A_26] :
      ( k3_xboole_0(A_70,A_26) = k1_relat_1(k6_relat_1(A_26))
      | ~ r1_tarski(A_26,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1131,c_3821])).

tff(c_3917,plain,(
    ! [A_181,A_182] :
      ( k3_xboole_0(A_181,A_182) = A_182
      | ~ r1_tarski(A_182,A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3878])).

tff(c_5050,plain,(
    ! [B_202,A_203] :
      ( k3_xboole_0(B_202,k5_relat_1(k6_relat_1(A_203),B_202)) = k5_relat_1(k6_relat_1(A_203),B_202)
      | ~ v1_relat_1(B_202) ) ),
    inference(resolution,[status(thm)],[c_30,c_3917])).

tff(c_5191,plain,(
    ! [A_29,B_30] :
      ( k5_relat_1(k6_relat_1(A_29),B_30) = k3_xboole_0(B_30,k7_relat_1(B_30,A_29))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5050])).

tff(c_23497,plain,(
    ! [A_403,A_402] :
      ( k5_relat_1(k6_relat_1(A_403),k6_relat_1(A_402)) = k7_relat_1(k6_relat_1(A_402),A_403)
      | ~ v1_relat_1(k6_relat_1(A_402))
      | ~ v1_relat_1(k6_relat_1(A_402)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23428,c_5191])).

tff(c_23815,plain,(
    ! [A_403,A_402] : k5_relat_1(k6_relat_1(A_403),k6_relat_1(A_402)) = k7_relat_1(k6_relat_1(A_402),A_403) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_23497])).

tff(c_597,plain,(
    ! [B_45,A_46] : k7_relat_1(k6_relat_1(B_45),k3_xboole_0(A_46,B_45)) = k7_relat_1(k6_relat_1(B_45),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_560])).

tff(c_468,plain,(
    ! [C_86,A_87,B_88] :
      ( k7_relat_1(k7_relat_1(C_86,A_87),B_88) = k7_relat_1(C_86,k3_xboole_0(A_87,B_88))
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1363,plain,(
    ! [B_132,A_133,B_134] :
      ( k7_relat_1(B_132,k3_xboole_0(k3_xboole_0(k1_relat_1(B_132),A_133),B_134)) = k7_relat_1(k7_relat_1(B_132,A_133),B_134)
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_468])).

tff(c_1441,plain,(
    ! [B_45,A_133] :
      ( k7_relat_1(k6_relat_1(B_45),k3_xboole_0(k1_relat_1(k6_relat_1(B_45)),A_133)) = k7_relat_1(k7_relat_1(k6_relat_1(B_45),A_133),B_45)
      | ~ v1_relat_1(k6_relat_1(B_45))
      | ~ v1_relat_1(k6_relat_1(B_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_1363])).

tff(c_1490,plain,(
    ! [B_45,A_133] : k7_relat_1(k7_relat_1(k6_relat_1(B_45),A_133),B_45) = k7_relat_1(k6_relat_1(B_45),A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_434,c_26,c_1441])).

tff(c_193,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_820,plain,(
    ! [A_110,B_111] :
      ( k5_relat_1(k6_relat_1(A_110),B_111) = B_111
      | ~ r1_tarski(B_111,k5_relat_1(k6_relat_1(A_110),B_111))
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_10099,plain,(
    ! [A_268,B_269] :
      ( k5_relat_1(k6_relat_1(A_268),B_269) = B_269
      | ~ r1_tarski(B_269,k7_relat_1(B_269,A_268))
      | ~ v1_relat_1(B_269)
      | ~ v1_relat_1(B_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_820])).

tff(c_10120,plain,(
    ! [B_45,A_133] :
      ( k5_relat_1(k6_relat_1(B_45),k7_relat_1(k6_relat_1(B_45),A_133)) = k7_relat_1(k6_relat_1(B_45),A_133)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(B_45),A_133),k7_relat_1(k6_relat_1(B_45),A_133))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_45),A_133))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_45),A_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_10099])).

tff(c_10167,plain,(
    ! [B_45,A_133] : k5_relat_1(k6_relat_1(B_45),k7_relat_1(k6_relat_1(B_45),A_133)) = k7_relat_1(k6_relat_1(B_45),A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_606,c_6,c_10120])).

tff(c_608,plain,(
    ! [A_95,B_96,C_97] :
      ( k5_relat_1(k5_relat_1(A_95,B_96),C_97) = k5_relat_1(A_95,k5_relat_1(B_96,C_97))
      | ~ v1_relat_1(C_97)
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_618,plain,(
    ! [A_95,B_96,A_27] :
      ( r1_tarski(k5_relat_1(A_95,k5_relat_1(B_96,k6_relat_1(A_27))),k5_relat_1(A_95,B_96))
      | ~ v1_relat_1(k5_relat_1(A_95,B_96))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_32])).

tff(c_2237,plain,(
    ! [A_151,B_152,A_153] :
      ( r1_tarski(k5_relat_1(A_151,k5_relat_1(B_152,k6_relat_1(A_153))),k5_relat_1(A_151,B_152))
      | ~ v1_relat_1(k5_relat_1(A_151,B_152))
      | ~ v1_relat_1(B_152)
      | ~ v1_relat_1(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_618])).

tff(c_2266,plain,(
    ! [A_151,A_153,A_29] :
      ( r1_tarski(k5_relat_1(A_151,k7_relat_1(k6_relat_1(A_153),A_29)),k5_relat_1(A_151,k6_relat_1(A_29)))
      | ~ v1_relat_1(k5_relat_1(A_151,k6_relat_1(A_29)))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(A_151)
      | ~ v1_relat_1(k6_relat_1(A_153)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2237])).

tff(c_25745,plain,(
    ! [A_415,A_416,A_417] :
      ( r1_tarski(k5_relat_1(A_415,k7_relat_1(k6_relat_1(A_416),A_417)),k5_relat_1(A_415,k6_relat_1(A_417)))
      | ~ v1_relat_1(k5_relat_1(A_415,k6_relat_1(A_417)))
      | ~ v1_relat_1(A_415) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_2266])).

tff(c_25782,plain,(
    ! [B_45,A_133] :
      ( r1_tarski(k7_relat_1(k6_relat_1(B_45),A_133),k5_relat_1(k6_relat_1(B_45),k6_relat_1(A_133)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(B_45),k6_relat_1(A_133)))
      | ~ v1_relat_1(k6_relat_1(B_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10167,c_25745])).

tff(c_26015,plain,(
    ! [B_418,A_419] : r1_tarski(k7_relat_1(k6_relat_1(B_418),A_419),k7_relat_1(k6_relat_1(A_419),B_418)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_606,c_23815,c_23815,c_25782])).

tff(c_26033,plain,(
    ! [A_419,A_17] :
      ( r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_419)),A_17)),A_419),k3_xboole_0(k6_relat_1(A_419),k7_relat_1(k6_relat_1(A_419),A_17)))
      | ~ v1_relat_1(k6_relat_1(A_419))
      | ~ v1_relat_1(k6_relat_1(A_419)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5806,c_26015])).

tff(c_27094,plain,(
    ! [A_422,A_423] : r1_tarski(k6_relat_1(k3_xboole_0(A_422,A_423)),k7_relat_1(k6_relat_1(A_422),A_423)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22620,c_2093,c_26,c_26033])).

tff(c_27104,plain,(
    ! [A_422,A_423] :
      ( k7_relat_1(k6_relat_1(A_422),A_423) = k6_relat_1(k3_xboole_0(A_422,A_423))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_422),A_423),k6_relat_1(k3_xboole_0(A_422,A_423))) ) ),
    inference(resolution,[status(thm)],[c_27094,c_2])).

tff(c_27324,plain,(
    ! [A_422,A_423] : k7_relat_1(k6_relat_1(A_422),A_423) = k6_relat_1(k3_xboole_0(A_422,A_423)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_27104])).

tff(c_38,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_229,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_38])).

tff(c_239,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_229])).

tff(c_27810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27324,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:37:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.48/5.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.48/5.01  
% 12.48/5.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.48/5.01  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 12.48/5.01  
% 12.48/5.01  %Foreground sorts:
% 12.48/5.01  
% 12.48/5.01  
% 12.48/5.01  %Background operators:
% 12.48/5.01  
% 12.48/5.01  
% 12.48/5.01  %Foreground operators:
% 12.48/5.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.48/5.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.48/5.01  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.48/5.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.48/5.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.48/5.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.48/5.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.48/5.01  tff('#skF_2', type, '#skF_2': $i).
% 12.48/5.01  tff('#skF_1', type, '#skF_1': $i).
% 12.48/5.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.48/5.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.48/5.01  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.48/5.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.48/5.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.48/5.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.48/5.01  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.48/5.01  
% 12.84/5.04  tff(f_47, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 12.84/5.04  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 12.84/5.04  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 12.84/5.04  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 12.84/5.04  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 12.84/5.04  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.84/5.04  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 12.84/5.04  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 12.84/5.04  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 12.84/5.04  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.84/5.04  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 12.84/5.04  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 12.84/5.04  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 12.84/5.04  tff(f_88, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 12.84/5.04  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.84/5.04  tff(c_26, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.84/5.04  tff(c_389, plain, (![B_81, A_82]: (k7_relat_1(B_81, k3_xboole_0(k1_relat_1(B_81), A_82))=k7_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.84/5.04  tff(c_213, plain, (![A_59, B_60]: (k5_relat_1(k6_relat_1(A_59), B_60)=k7_relat_1(B_60, A_59) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.84/5.04  tff(c_32, plain, (![B_28, A_27]: (r1_tarski(k5_relat_1(B_28, k6_relat_1(A_27)), B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.84/5.04  tff(c_220, plain, (![A_27, A_59]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_59), k6_relat_1(A_59)) | ~v1_relat_1(k6_relat_1(A_59)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_32])).
% 12.84/5.04  tff(c_235, plain, (![A_27, A_59]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_59), k6_relat_1(A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_220])).
% 12.84/5.04  tff(c_403, plain, (![A_27, A_82]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_82), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_27)), A_82))) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_389, c_235])).
% 12.84/5.04  tff(c_429, plain, (![A_27, A_82]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_82), k6_relat_1(k3_xboole_0(A_27, A_82))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_26, c_403])).
% 12.84/5.04  tff(c_10, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.84/5.04  tff(c_103, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.84/5.04  tff(c_118, plain, (![B_45, A_46]: (k1_setfam_1(k2_tarski(B_45, A_46))=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_10, c_103])).
% 12.84/5.04  tff(c_14, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.84/5.04  tff(c_124, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_118, c_14])).
% 12.84/5.04  tff(c_424, plain, (![A_26, A_82]: (k7_relat_1(k6_relat_1(A_26), k3_xboole_0(A_26, A_82))=k7_relat_1(k6_relat_1(A_26), A_82) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_389])).
% 12.84/5.04  tff(c_560, plain, (![A_93, A_94]: (k7_relat_1(k6_relat_1(A_93), k3_xboole_0(A_93, A_94))=k7_relat_1(k6_relat_1(A_93), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_424])).
% 12.84/5.04  tff(c_30, plain, (![A_27, B_28]: (r1_tarski(k5_relat_1(k6_relat_1(A_27), B_28), B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.84/5.04  tff(c_226, plain, (![B_60, A_59]: (r1_tarski(k7_relat_1(B_60, A_59), B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_213, c_30])).
% 12.84/5.04  tff(c_578, plain, (![A_93, A_94]: (r1_tarski(k7_relat_1(k6_relat_1(A_93), A_94), k6_relat_1(A_93)) | ~v1_relat_1(k6_relat_1(A_93)) | ~v1_relat_1(k6_relat_1(A_93)))), inference(superposition, [status(thm), theory('equality')], [c_560, c_226])).
% 12.84/5.04  tff(c_603, plain, (![A_93, A_94]: (r1_tarski(k7_relat_1(k6_relat_1(A_93), A_94), k6_relat_1(A_93)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_578])).
% 12.84/5.04  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.84/5.04  tff(c_257, plain, (![B_69, A_70]: (k7_relat_1(B_69, A_70)=B_69 | ~r1_tarski(k1_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.84/5.04  tff(c_260, plain, (![A_26, A_70]: (k7_relat_1(k6_relat_1(A_26), A_70)=k6_relat_1(A_26) | ~r1_tarski(A_26, A_70) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_257])).
% 12.84/5.04  tff(c_266, plain, (![A_26, A_70]: (k7_relat_1(k6_relat_1(A_26), A_70)=k6_relat_1(A_26) | ~r1_tarski(A_26, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_260])).
% 12.84/5.04  tff(c_435, plain, (![A_83, A_84]: (r1_tarski(k7_relat_1(k6_relat_1(A_83), A_84), k6_relat_1(k3_xboole_0(A_83, A_84))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_26, c_403])).
% 12.84/5.04  tff(c_444, plain, (![A_26, A_70]: (r1_tarski(k6_relat_1(A_26), k6_relat_1(k3_xboole_0(A_26, A_70))) | ~r1_tarski(A_26, A_70))), inference(superposition, [status(thm), theory('equality')], [c_266, c_435])).
% 12.84/5.04  tff(c_318, plain, (![A_73, A_74]: (k7_relat_1(k6_relat_1(A_73), A_74)=k6_relat_1(A_73) | ~r1_tarski(A_73, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_260])).
% 12.84/5.04  tff(c_371, plain, (![A_75, A_76]: (r1_tarski(k6_relat_1(A_75), k6_relat_1(A_76)) | ~r1_tarski(A_75, A_76))), inference(superposition, [status(thm), theory('equality')], [c_318, c_235])).
% 12.84/5.04  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.84/5.04  tff(c_1103, plain, (![A_129, A_128]: (k6_relat_1(A_129)=k6_relat_1(A_128) | ~r1_tarski(k6_relat_1(A_128), k6_relat_1(A_129)) | ~r1_tarski(A_129, A_128))), inference(resolution, [status(thm)], [c_371, c_2])).
% 12.84/5.04  tff(c_1112, plain, (![A_26, A_70]: (k6_relat_1(k3_xboole_0(A_26, A_70))=k6_relat_1(A_26) | ~r1_tarski(k3_xboole_0(A_26, A_70), A_26) | ~r1_tarski(A_26, A_70))), inference(resolution, [status(thm)], [c_444, c_1103])).
% 12.84/5.04  tff(c_1636, plain, (![A_141, A_142]: (k6_relat_1(k3_xboole_0(A_141, A_142))=k6_relat_1(A_141) | ~r1_tarski(A_141, A_142))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1112])).
% 12.84/5.04  tff(c_1741, plain, (![A_141, A_142]: (k3_xboole_0(A_141, A_142)=k1_relat_1(k6_relat_1(A_141)) | ~r1_tarski(A_141, A_142))), inference(superposition, [status(thm), theory('equality')], [c_1636, c_26])).
% 12.84/5.04  tff(c_1777, plain, (![A_143, A_144]: (k3_xboole_0(A_143, A_144)=A_143 | ~r1_tarski(A_143, A_144))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1741])).
% 12.84/5.04  tff(c_22240, plain, (![A_394, A_395]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_394), A_395), k6_relat_1(A_394))=k7_relat_1(k6_relat_1(A_394), A_395))), inference(resolution, [status(thm)], [c_603, c_1777])).
% 12.84/5.04  tff(c_22620, plain, (![A_394, A_395]: (k3_xboole_0(k6_relat_1(A_394), k7_relat_1(k6_relat_1(A_394), A_395))=k7_relat_1(k6_relat_1(A_394), A_395))), inference(superposition, [status(thm), theory('equality')], [c_124, c_22240])).
% 12.84/5.04  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.84/5.04  tff(c_268, plain, (![B_71]: (k7_relat_1(B_71, k1_relat_1(B_71))=B_71 | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_6, c_257])).
% 12.84/5.04  tff(c_287, plain, (![A_26]: (k7_relat_1(k6_relat_1(A_26), A_26)=k6_relat_1(A_26) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_268])).
% 12.84/5.04  tff(c_294, plain, (![A_26]: (k7_relat_1(k6_relat_1(A_26), A_26)=k6_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_287])).
% 12.84/5.04  tff(c_1968, plain, (![A_147, B_148]: (k3_xboole_0(k3_xboole_0(A_147, B_148), A_147)=k3_xboole_0(A_147, B_148))), inference(resolution, [status(thm)], [c_8, c_1777])).
% 12.84/5.04  tff(c_434, plain, (![A_26, A_82]: (k7_relat_1(k6_relat_1(A_26), k3_xboole_0(A_26, A_82))=k7_relat_1(k6_relat_1(A_26), A_82))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_424])).
% 12.84/5.04  tff(c_2016, plain, (![A_147, B_148]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_147, B_148)), k3_xboole_0(A_147, B_148))=k7_relat_1(k6_relat_1(k3_xboole_0(A_147, B_148)), A_147))), inference(superposition, [status(thm), theory('equality')], [c_1968, c_434])).
% 12.84/5.04  tff(c_2093, plain, (![A_147, B_148]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_147, B_148)), A_147)=k6_relat_1(k3_xboole_0(A_147, B_148)))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_2016])).
% 12.84/5.04  tff(c_22, plain, (![B_18, A_17]: (k7_relat_1(B_18, k3_xboole_0(k1_relat_1(B_18), A_17))=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.84/5.04  tff(c_1807, plain, (![B_60, A_59]: (k3_xboole_0(k7_relat_1(B_60, A_59), B_60)=k7_relat_1(B_60, A_59) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_226, c_1777])).
% 12.84/5.04  tff(c_5661, plain, (![B_212, A_213]: (k3_xboole_0(B_212, k7_relat_1(B_212, A_213))=k7_relat_1(B_212, A_213) | ~v1_relat_1(B_212))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_1807])).
% 12.84/5.04  tff(c_5806, plain, (![B_18, A_17]: (k7_relat_1(B_18, k3_xboole_0(k1_relat_1(B_18), A_17))=k3_xboole_0(B_18, k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5661])).
% 12.84/5.04  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k5_relat_1(A_11, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.84/5.04  tff(c_223, plain, (![B_60, A_59]: (v1_relat_1(k7_relat_1(B_60, A_59)) | ~v1_relat_1(B_60) | ~v1_relat_1(k6_relat_1(A_59)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_213, c_16])).
% 12.84/5.04  tff(c_237, plain, (![B_60, A_59]: (v1_relat_1(k7_relat_1(B_60, A_59)) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_223])).
% 12.84/5.04  tff(c_584, plain, (![A_93, A_94]: (v1_relat_1(k7_relat_1(k6_relat_1(A_93), A_94)) | ~v1_relat_1(k6_relat_1(A_93)))), inference(superposition, [status(thm), theory('equality')], [c_560, c_237])).
% 12.84/5.04  tff(c_606, plain, (![A_93, A_94]: (v1_relat_1(k7_relat_1(k6_relat_1(A_93), A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_584])).
% 12.84/5.04  tff(c_23428, plain, (![A_402, A_403]: (k3_xboole_0(k6_relat_1(A_402), k7_relat_1(k6_relat_1(A_402), A_403))=k7_relat_1(k6_relat_1(A_402), A_403))), inference(superposition, [status(thm), theory('equality')], [c_124, c_22240])).
% 12.84/5.04  tff(c_34, plain, (![A_29, B_30]: (k5_relat_1(k6_relat_1(A_29), B_30)=k7_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.84/5.04  tff(c_1131, plain, (![A_26, A_70]: (k6_relat_1(k3_xboole_0(A_26, A_70))=k6_relat_1(A_26) | ~r1_tarski(A_26, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1112])).
% 12.84/5.04  tff(c_141, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_118, c_14])).
% 12.84/5.04  tff(c_156, plain, (![B_47, A_48]: (r1_tarski(k3_xboole_0(B_47, A_48), A_48))), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 12.84/5.04  tff(c_2476, plain, (![B_158, A_159]: (k3_xboole_0(k3_xboole_0(B_158, A_159), A_159)=k3_xboole_0(A_159, B_158))), inference(superposition, [status(thm), theory('equality')], [c_124, c_1968])).
% 12.84/5.04  tff(c_2504, plain, (![B_158, A_159]: (k6_relat_1(k3_xboole_0(B_158, A_159))=k6_relat_1(k3_xboole_0(A_159, B_158)) | ~r1_tarski(k3_xboole_0(B_158, A_159), A_159))), inference(superposition, [status(thm), theory('equality')], [c_2476, c_1131])).
% 12.84/5.04  tff(c_3501, plain, (![B_177, A_178]: (k6_relat_1(k3_xboole_0(B_177, A_178))=k6_relat_1(k3_xboole_0(A_178, B_177)))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_2504])).
% 12.84/5.04  tff(c_3821, plain, (![B_179, A_180]: (k1_relat_1(k6_relat_1(k3_xboole_0(B_179, A_180)))=k3_xboole_0(A_180, B_179))), inference(superposition, [status(thm), theory('equality')], [c_3501, c_26])).
% 12.84/5.04  tff(c_3878, plain, (![A_70, A_26]: (k3_xboole_0(A_70, A_26)=k1_relat_1(k6_relat_1(A_26)) | ~r1_tarski(A_26, A_70))), inference(superposition, [status(thm), theory('equality')], [c_1131, c_3821])).
% 12.84/5.04  tff(c_3917, plain, (![A_181, A_182]: (k3_xboole_0(A_181, A_182)=A_182 | ~r1_tarski(A_182, A_181))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3878])).
% 12.84/5.04  tff(c_5050, plain, (![B_202, A_203]: (k3_xboole_0(B_202, k5_relat_1(k6_relat_1(A_203), B_202))=k5_relat_1(k6_relat_1(A_203), B_202) | ~v1_relat_1(B_202))), inference(resolution, [status(thm)], [c_30, c_3917])).
% 12.84/5.04  tff(c_5191, plain, (![A_29, B_30]: (k5_relat_1(k6_relat_1(A_29), B_30)=k3_xboole_0(B_30, k7_relat_1(B_30, A_29)) | ~v1_relat_1(B_30) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_34, c_5050])).
% 12.84/5.04  tff(c_23497, plain, (![A_403, A_402]: (k5_relat_1(k6_relat_1(A_403), k6_relat_1(A_402))=k7_relat_1(k6_relat_1(A_402), A_403) | ~v1_relat_1(k6_relat_1(A_402)) | ~v1_relat_1(k6_relat_1(A_402)))), inference(superposition, [status(thm), theory('equality')], [c_23428, c_5191])).
% 12.84/5.04  tff(c_23815, plain, (![A_403, A_402]: (k5_relat_1(k6_relat_1(A_403), k6_relat_1(A_402))=k7_relat_1(k6_relat_1(A_402), A_403))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_23497])).
% 12.84/5.04  tff(c_597, plain, (![B_45, A_46]: (k7_relat_1(k6_relat_1(B_45), k3_xboole_0(A_46, B_45))=k7_relat_1(k6_relat_1(B_45), A_46))), inference(superposition, [status(thm), theory('equality')], [c_124, c_560])).
% 12.84/5.04  tff(c_468, plain, (![C_86, A_87, B_88]: (k7_relat_1(k7_relat_1(C_86, A_87), B_88)=k7_relat_1(C_86, k3_xboole_0(A_87, B_88)) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.84/5.04  tff(c_1363, plain, (![B_132, A_133, B_134]: (k7_relat_1(B_132, k3_xboole_0(k3_xboole_0(k1_relat_1(B_132), A_133), B_134))=k7_relat_1(k7_relat_1(B_132, A_133), B_134) | ~v1_relat_1(B_132) | ~v1_relat_1(B_132))), inference(superposition, [status(thm), theory('equality')], [c_22, c_468])).
% 12.84/5.04  tff(c_1441, plain, (![B_45, A_133]: (k7_relat_1(k6_relat_1(B_45), k3_xboole_0(k1_relat_1(k6_relat_1(B_45)), A_133))=k7_relat_1(k7_relat_1(k6_relat_1(B_45), A_133), B_45) | ~v1_relat_1(k6_relat_1(B_45)) | ~v1_relat_1(k6_relat_1(B_45)))), inference(superposition, [status(thm), theory('equality')], [c_597, c_1363])).
% 12.84/5.04  tff(c_1490, plain, (![B_45, A_133]: (k7_relat_1(k7_relat_1(k6_relat_1(B_45), A_133), B_45)=k7_relat_1(k6_relat_1(B_45), A_133))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_434, c_26, c_1441])).
% 12.84/5.04  tff(c_193, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.84/5.04  tff(c_820, plain, (![A_110, B_111]: (k5_relat_1(k6_relat_1(A_110), B_111)=B_111 | ~r1_tarski(B_111, k5_relat_1(k6_relat_1(A_110), B_111)) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_30, c_193])).
% 12.84/5.04  tff(c_10099, plain, (![A_268, B_269]: (k5_relat_1(k6_relat_1(A_268), B_269)=B_269 | ~r1_tarski(B_269, k7_relat_1(B_269, A_268)) | ~v1_relat_1(B_269) | ~v1_relat_1(B_269))), inference(superposition, [status(thm), theory('equality')], [c_34, c_820])).
% 12.84/5.04  tff(c_10120, plain, (![B_45, A_133]: (k5_relat_1(k6_relat_1(B_45), k7_relat_1(k6_relat_1(B_45), A_133))=k7_relat_1(k6_relat_1(B_45), A_133) | ~r1_tarski(k7_relat_1(k6_relat_1(B_45), A_133), k7_relat_1(k6_relat_1(B_45), A_133)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_45), A_133)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_45), A_133)))), inference(superposition, [status(thm), theory('equality')], [c_1490, c_10099])).
% 12.84/5.04  tff(c_10167, plain, (![B_45, A_133]: (k5_relat_1(k6_relat_1(B_45), k7_relat_1(k6_relat_1(B_45), A_133))=k7_relat_1(k6_relat_1(B_45), A_133))), inference(demodulation, [status(thm), theory('equality')], [c_606, c_606, c_6, c_10120])).
% 12.84/5.04  tff(c_608, plain, (![A_95, B_96, C_97]: (k5_relat_1(k5_relat_1(A_95, B_96), C_97)=k5_relat_1(A_95, k5_relat_1(B_96, C_97)) | ~v1_relat_1(C_97) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.84/5.04  tff(c_618, plain, (![A_95, B_96, A_27]: (r1_tarski(k5_relat_1(A_95, k5_relat_1(B_96, k6_relat_1(A_27))), k5_relat_1(A_95, B_96)) | ~v1_relat_1(k5_relat_1(A_95, B_96)) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(superposition, [status(thm), theory('equality')], [c_608, c_32])).
% 12.84/5.04  tff(c_2237, plain, (![A_151, B_152, A_153]: (r1_tarski(k5_relat_1(A_151, k5_relat_1(B_152, k6_relat_1(A_153))), k5_relat_1(A_151, B_152)) | ~v1_relat_1(k5_relat_1(A_151, B_152)) | ~v1_relat_1(B_152) | ~v1_relat_1(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_618])).
% 12.84/5.04  tff(c_2266, plain, (![A_151, A_153, A_29]: (r1_tarski(k5_relat_1(A_151, k7_relat_1(k6_relat_1(A_153), A_29)), k5_relat_1(A_151, k6_relat_1(A_29))) | ~v1_relat_1(k5_relat_1(A_151, k6_relat_1(A_29))) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(A_151) | ~v1_relat_1(k6_relat_1(A_153)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2237])).
% 12.84/5.04  tff(c_25745, plain, (![A_415, A_416, A_417]: (r1_tarski(k5_relat_1(A_415, k7_relat_1(k6_relat_1(A_416), A_417)), k5_relat_1(A_415, k6_relat_1(A_417))) | ~v1_relat_1(k5_relat_1(A_415, k6_relat_1(A_417))) | ~v1_relat_1(A_415))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_2266])).
% 12.84/5.04  tff(c_25782, plain, (![B_45, A_133]: (r1_tarski(k7_relat_1(k6_relat_1(B_45), A_133), k5_relat_1(k6_relat_1(B_45), k6_relat_1(A_133))) | ~v1_relat_1(k5_relat_1(k6_relat_1(B_45), k6_relat_1(A_133))) | ~v1_relat_1(k6_relat_1(B_45)))), inference(superposition, [status(thm), theory('equality')], [c_10167, c_25745])).
% 12.84/5.04  tff(c_26015, plain, (![B_418, A_419]: (r1_tarski(k7_relat_1(k6_relat_1(B_418), A_419), k7_relat_1(k6_relat_1(A_419), B_418)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_606, c_23815, c_23815, c_25782])).
% 12.84/5.04  tff(c_26033, plain, (![A_419, A_17]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_419)), A_17)), A_419), k3_xboole_0(k6_relat_1(A_419), k7_relat_1(k6_relat_1(A_419), A_17))) | ~v1_relat_1(k6_relat_1(A_419)) | ~v1_relat_1(k6_relat_1(A_419)))), inference(superposition, [status(thm), theory('equality')], [c_5806, c_26015])).
% 12.84/5.04  tff(c_27094, plain, (![A_422, A_423]: (r1_tarski(k6_relat_1(k3_xboole_0(A_422, A_423)), k7_relat_1(k6_relat_1(A_422), A_423)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22620, c_2093, c_26, c_26033])).
% 12.84/5.04  tff(c_27104, plain, (![A_422, A_423]: (k7_relat_1(k6_relat_1(A_422), A_423)=k6_relat_1(k3_xboole_0(A_422, A_423)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_422), A_423), k6_relat_1(k3_xboole_0(A_422, A_423))))), inference(resolution, [status(thm)], [c_27094, c_2])).
% 12.84/5.04  tff(c_27324, plain, (![A_422, A_423]: (k7_relat_1(k6_relat_1(A_422), A_423)=k6_relat_1(k3_xboole_0(A_422, A_423)))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_27104])).
% 12.84/5.04  tff(c_38, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.84/5.04  tff(c_229, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_38])).
% 12.84/5.04  tff(c_239, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_229])).
% 12.84/5.04  tff(c_27810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27324, c_239])).
% 12.84/5.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.84/5.04  
% 12.84/5.04  Inference rules
% 12.84/5.04  ----------------------
% 12.84/5.04  #Ref     : 0
% 12.84/5.04  #Sup     : 6725
% 12.84/5.04  #Fact    : 0
% 12.84/5.04  #Define  : 0
% 12.84/5.04  #Split   : 1
% 12.84/5.04  #Chain   : 0
% 12.84/5.04  #Close   : 0
% 12.84/5.04  
% 12.84/5.04  Ordering : KBO
% 12.84/5.04  
% 12.84/5.04  Simplification rules
% 12.84/5.04  ----------------------
% 12.84/5.04  #Subsume      : 941
% 12.84/5.04  #Demod        : 7679
% 12.84/5.04  #Tautology    : 2260
% 12.84/5.04  #SimpNegUnit  : 0
% 12.84/5.04  #BackRed      : 60
% 12.84/5.04  
% 12.84/5.04  #Partial instantiations: 0
% 12.84/5.04  #Strategies tried      : 1
% 12.84/5.04  
% 12.84/5.04  Timing (in seconds)
% 12.84/5.04  ----------------------
% 12.84/5.04  Preprocessing        : 0.30
% 12.84/5.04  Parsing              : 0.16
% 12.84/5.04  CNF conversion       : 0.02
% 12.84/5.04  Main loop            : 3.92
% 12.84/5.04  Inferencing          : 0.82
% 12.84/5.04  Reduction            : 1.95
% 12.84/5.04  Demodulation         : 1.71
% 12.84/5.04  BG Simplification    : 0.12
% 12.84/5.04  Subsumption          : 0.84
% 12.84/5.04  Abstraction          : 0.19
% 12.84/5.04  MUC search           : 0.00
% 12.84/5.04  Cooper               : 0.00
% 12.84/5.04  Total                : 4.27
% 12.84/5.04  Index Insertion      : 0.00
% 12.84/5.04  Index Deletion       : 0.00
% 12.84/5.04  Index Matching       : 0.00
% 12.84/5.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
