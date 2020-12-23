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
% DateTime   : Thu Dec  3 09:48:09 EST 2020

% Result     : Theorem 12.13s
% Output     : CNFRefutation 12.14s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 829 expanded)
%              Number of leaves         :   29 ( 290 expanded)
%              Depth                    :   19
%              Number of atoms          :   82 ( 966 expanded)
%              Number of equality atoms :   69 ( 656 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_455,plain,(
    ! [A_77,B_78] : k3_xboole_0(k4_xboole_0(A_77,B_78),A_77) = k4_xboole_0(A_77,B_78) ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_125,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_14,B_15] : k3_xboole_0(k4_xboole_0(A_14,B_15),B_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_468,plain,(
    ! [A_77] : k4_xboole_0(A_77,A_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_129])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_166,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_187,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_166])).

tff(c_501,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_187])).

tff(c_22,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_308,plain,(
    ! [A_68,B_69,C_70] : k5_xboole_0(k5_xboole_0(A_68,B_69),C_70) = k5_xboole_0(A_68,k5_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1480,plain,(
    ! [A_110,B_111,C_112] : k5_xboole_0(A_110,k5_xboole_0(k4_xboole_0(B_111,A_110),C_112)) = k5_xboole_0(k2_xboole_0(A_110,B_111),C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_308])).

tff(c_1533,plain,(
    ! [A_110,B_111] : k5_xboole_0(k2_xboole_0(A_110,B_111),k4_xboole_0(B_111,A_110)) = k5_xboole_0(A_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_1480])).

tff(c_2958,plain,(
    ! [A_137,B_138] : k5_xboole_0(k2_xboole_0(A_137,B_138),k4_xboole_0(B_138,A_137)) = A_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1533])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_608,plain,(
    ! [A_88] : k5_xboole_0(A_88,A_88) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_187])).

tff(c_1938,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k5_xboole_0(B_122,k5_xboole_0(A_121,B_122))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_608])).

tff(c_502,plain,(
    ! [A_79] : k4_xboole_0(A_79,A_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_129])).

tff(c_130,plain,(
    ! [A_51,B_52] : k3_xboole_0(k4_xboole_0(A_51,B_52),B_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    ! [B_52,A_51] : k3_xboole_0(B_52,k4_xboole_0(A_51,B_52)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_2])).

tff(c_175,plain,(
    ! [B_52,A_51] : k4_xboole_0(B_52,k4_xboole_0(A_51,B_52)) = k5_xboole_0(B_52,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_166])).

tff(c_190,plain,(
    ! [B_52,A_51] : k4_xboole_0(B_52,k4_xboole_0(A_51,B_52)) = B_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_175])).

tff(c_781,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = A_93 ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_190])).

tff(c_800,plain,(
    ! [A_93] : k5_xboole_0(k1_xboole_0,A_93) = k2_xboole_0(k1_xboole_0,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_22])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_998,plain,(
    ! [A_97,B_98,C_99] : k5_xboole_0(A_97,k5_xboole_0(k3_xboole_0(A_97,B_98),C_99)) = k5_xboole_0(k4_xboole_0(A_97,B_98),C_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_308])).

tff(c_1078,plain,(
    ! [A_5,C_99] : k5_xboole_0(k4_xboole_0(A_5,A_5),C_99) = k5_xboole_0(A_5,k5_xboole_0(A_5,C_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_998])).

tff(c_1094,plain,(
    ! [A_5,C_99] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_99)) = k5_xboole_0(k1_xboole_0,C_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_1078])).

tff(c_1573,plain,(
    ! [A_113,C_114] : k5_xboole_0(A_113,k5_xboole_0(A_113,C_114)) = k2_xboole_0(k1_xboole_0,C_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_1094])).

tff(c_1623,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_1573])).

tff(c_1650,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1623])).

tff(c_1572,plain,(
    ! [A_5,C_99] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_99)) = k2_xboole_0(k1_xboole_0,C_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_1094])).

tff(c_1653,plain,(
    ! [A_5,C_99] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_99)) = C_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_1572])).

tff(c_1946,plain,(
    ! [B_122,A_121] : k5_xboole_0(B_122,k5_xboole_0(A_121,B_122)) = k5_xboole_0(A_121,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1938,c_1653])).

tff(c_2058,plain,(
    ! [B_122,A_121] : k5_xboole_0(B_122,k5_xboole_0(A_121,B_122)) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1946])).

tff(c_2976,plain,(
    ! [B_138,A_137] : k5_xboole_0(k4_xboole_0(B_138,A_137),A_137) = k2_xboole_0(A_137,B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_2958,c_2058])).

tff(c_1038,plain,(
    ! [A_97,B_98] : k5_xboole_0(k4_xboole_0(A_97,B_98),k3_xboole_0(A_97,B_98)) = k5_xboole_0(A_97,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_998])).

tff(c_1860,plain,(
    ! [A_119,B_120] : k5_xboole_0(k4_xboole_0(A_119,B_120),k3_xboole_0(A_119,B_120)) = A_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1038])).

tff(c_3086,plain,(
    ! [B_141,A_142] : k5_xboole_0(k4_xboole_0(B_141,A_142),k3_xboole_0(A_142,B_141)) = B_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1860])).

tff(c_4495,plain,(
    ! [A_169,B_170] : k5_xboole_0(k3_xboole_0(A_169,B_170),B_170) = k4_xboole_0(B_170,A_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_3086,c_2058])).

tff(c_353,plain,(
    ! [A_7,B_8,C_70] : k5_xboole_0(A_7,k5_xboole_0(k3_xboole_0(A_7,B_8),C_70)) = k5_xboole_0(k4_xboole_0(A_7,B_8),C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_308])).

tff(c_4529,plain,(
    ! [A_169,B_170] : k5_xboole_0(k4_xboole_0(A_169,B_170),B_170) = k5_xboole_0(A_169,k4_xboole_0(B_170,A_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4495,c_353])).

tff(c_4596,plain,(
    ! [B_170,A_169] : k2_xboole_0(B_170,A_169) = k2_xboole_0(A_169,B_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_22,c_4529])).

tff(c_115,plain,(
    ! [A_11,B_12] : k3_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_646,plain,(
    ! [A_90] : k3_xboole_0(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_135])).

tff(c_683,plain,(
    ! [B_12] : k4_xboole_0(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_646])).

tff(c_32,plain,(
    ! [A_31,B_32] : r1_tarski(k1_tarski(A_31),k2_tarski(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_114,plain,(
    ! [A_31,B_32] : k3_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)) = k1_tarski(A_31) ),
    inference(resolution,[status(thm)],[c_32,c_102])).

tff(c_1090,plain,(
    ! [A_97,B_98] : k5_xboole_0(k4_xboole_0(A_97,B_98),k3_xboole_0(A_97,B_98)) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1038])).

tff(c_2084,plain,(
    ! [B_123,A_124] : k5_xboole_0(B_123,k5_xboole_0(A_124,B_123)) = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1946])).

tff(c_3868,plain,(
    ! [A_157,B_158] : k5_xboole_0(k3_xboole_0(A_157,B_158),A_157) = k4_xboole_0(A_157,B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_2084])).

tff(c_3931,plain,(
    ! [A_31,B_32] : k5_xboole_0(k1_tarski(A_31),k1_tarski(A_31)) = k4_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_3868])).

tff(c_3968,plain,(
    ! [A_31,B_32] : k4_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_3931])).

tff(c_544,plain,(
    ! [A_84] : r1_tarski(k1_xboole_0,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_14])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_548,plain,(
    ! [A_84] : k3_xboole_0(k1_xboole_0,A_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_544,c_12])).

tff(c_12586,plain,(
    ! [A_267,B_268,B_269] : k5_xboole_0(k2_xboole_0(A_267,B_268),k3_xboole_0(k4_xboole_0(B_268,A_267),B_269)) = k5_xboole_0(A_267,k4_xboole_0(k4_xboole_0(B_268,A_267),B_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1480])).

tff(c_12705,plain,(
    ! [A_31,B_32,B_269] : k5_xboole_0(k2_tarski(A_31,B_32),k4_xboole_0(k4_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)),B_269)) = k5_xboole_0(k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(A_31)),k3_xboole_0(k1_xboole_0,B_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3968,c_12586])).

tff(c_12798,plain,(
    ! [A_31,B_32] : k2_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)) = k2_tarski(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4596,c_16,c_683,c_3968,c_16,c_548,c_12705])).

tff(c_34,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12798,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.13/5.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.14/5.18  
% 12.14/5.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.14/5.18  %$ r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 12.14/5.18  
% 12.14/5.18  %Foreground sorts:
% 12.14/5.18  
% 12.14/5.18  
% 12.14/5.18  %Background operators:
% 12.14/5.18  
% 12.14/5.18  
% 12.14/5.18  %Foreground operators:
% 12.14/5.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.14/5.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.14/5.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.14/5.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.14/5.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.14/5.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.14/5.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.14/5.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.14/5.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.14/5.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.14/5.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.14/5.18  tff('#skF_2', type, '#skF_2': $i).
% 12.14/5.18  tff('#skF_1', type, '#skF_1': $i).
% 12.14/5.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.14/5.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.14/5.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.14/5.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.14/5.18  
% 12.14/5.21  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.14/5.21  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.14/5.21  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.14/5.21  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 12.14/5.21  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.14/5.21  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 12.14/5.21  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.14/5.21  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.14/5.21  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.14/5.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.14/5.21  tff(f_59, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 12.14/5.21  tff(f_62, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 12.14/5.21  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.14/5.21  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.14/5.21  tff(c_102, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.14/5.21  tff(c_455, plain, (![A_77, B_78]: (k3_xboole_0(k4_xboole_0(A_77, B_78), A_77)=k4_xboole_0(A_77, B_78))), inference(resolution, [status(thm)], [c_14, c_102])).
% 12.14/5.21  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.14/5.21  tff(c_125, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.14/5.21  tff(c_129, plain, (![A_14, B_15]: (k3_xboole_0(k4_xboole_0(A_14, B_15), B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_125])).
% 12.14/5.21  tff(c_468, plain, (![A_77]: (k4_xboole_0(A_77, A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_455, c_129])).
% 12.14/5.21  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.14/5.21  tff(c_166, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.14/5.21  tff(c_187, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_166])).
% 12.14/5.21  tff(c_501, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_468, c_187])).
% 12.14/5.21  tff(c_22, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.14/5.21  tff(c_308, plain, (![A_68, B_69, C_70]: (k5_xboole_0(k5_xboole_0(A_68, B_69), C_70)=k5_xboole_0(A_68, k5_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.14/5.21  tff(c_1480, plain, (![A_110, B_111, C_112]: (k5_xboole_0(A_110, k5_xboole_0(k4_xboole_0(B_111, A_110), C_112))=k5_xboole_0(k2_xboole_0(A_110, B_111), C_112))), inference(superposition, [status(thm), theory('equality')], [c_22, c_308])).
% 12.14/5.21  tff(c_1533, plain, (![A_110, B_111]: (k5_xboole_0(k2_xboole_0(A_110, B_111), k4_xboole_0(B_111, A_110))=k5_xboole_0(A_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_501, c_1480])).
% 12.14/5.21  tff(c_2958, plain, (![A_137, B_138]: (k5_xboole_0(k2_xboole_0(A_137, B_138), k4_xboole_0(B_138, A_137))=A_137)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1533])).
% 12.14/5.21  tff(c_20, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.14/5.21  tff(c_608, plain, (![A_88]: (k5_xboole_0(A_88, A_88)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_468, c_187])).
% 12.14/5.21  tff(c_1938, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k5_xboole_0(B_122, k5_xboole_0(A_121, B_122)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_608])).
% 12.14/5.21  tff(c_502, plain, (![A_79]: (k4_xboole_0(A_79, A_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_455, c_129])).
% 12.14/5.21  tff(c_130, plain, (![A_51, B_52]: (k3_xboole_0(k4_xboole_0(A_51, B_52), B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_125])).
% 12.14/5.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.14/5.21  tff(c_135, plain, (![B_52, A_51]: (k3_xboole_0(B_52, k4_xboole_0(A_51, B_52))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_2])).
% 12.14/5.21  tff(c_175, plain, (![B_52, A_51]: (k4_xboole_0(B_52, k4_xboole_0(A_51, B_52))=k5_xboole_0(B_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_166])).
% 12.14/5.21  tff(c_190, plain, (![B_52, A_51]: (k4_xboole_0(B_52, k4_xboole_0(A_51, B_52))=B_52)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_175])).
% 12.14/5.21  tff(c_781, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=A_93)), inference(superposition, [status(thm), theory('equality')], [c_502, c_190])).
% 12.14/5.21  tff(c_800, plain, (![A_93]: (k5_xboole_0(k1_xboole_0, A_93)=k2_xboole_0(k1_xboole_0, A_93))), inference(superposition, [status(thm), theory('equality')], [c_781, c_22])).
% 12.14/5.21  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.14/5.21  tff(c_998, plain, (![A_97, B_98, C_99]: (k5_xboole_0(A_97, k5_xboole_0(k3_xboole_0(A_97, B_98), C_99))=k5_xboole_0(k4_xboole_0(A_97, B_98), C_99))), inference(superposition, [status(thm), theory('equality')], [c_10, c_308])).
% 12.14/5.21  tff(c_1078, plain, (![A_5, C_99]: (k5_xboole_0(k4_xboole_0(A_5, A_5), C_99)=k5_xboole_0(A_5, k5_xboole_0(A_5, C_99)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_998])).
% 12.14/5.21  tff(c_1094, plain, (![A_5, C_99]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_99))=k5_xboole_0(k1_xboole_0, C_99))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_1078])).
% 12.14/5.21  tff(c_1573, plain, (![A_113, C_114]: (k5_xboole_0(A_113, k5_xboole_0(A_113, C_114))=k2_xboole_0(k1_xboole_0, C_114))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_1094])).
% 12.14/5.21  tff(c_1623, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_501, c_1573])).
% 12.14/5.21  tff(c_1650, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1623])).
% 12.14/5.21  tff(c_1572, plain, (![A_5, C_99]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_99))=k2_xboole_0(k1_xboole_0, C_99))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_1094])).
% 12.14/5.21  tff(c_1653, plain, (![A_5, C_99]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_99))=C_99)), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_1572])).
% 12.14/5.21  tff(c_1946, plain, (![B_122, A_121]: (k5_xboole_0(B_122, k5_xboole_0(A_121, B_122))=k5_xboole_0(A_121, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1938, c_1653])).
% 12.14/5.21  tff(c_2058, plain, (![B_122, A_121]: (k5_xboole_0(B_122, k5_xboole_0(A_121, B_122))=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1946])).
% 12.14/5.21  tff(c_2976, plain, (![B_138, A_137]: (k5_xboole_0(k4_xboole_0(B_138, A_137), A_137)=k2_xboole_0(A_137, B_138))), inference(superposition, [status(thm), theory('equality')], [c_2958, c_2058])).
% 12.14/5.21  tff(c_1038, plain, (![A_97, B_98]: (k5_xboole_0(k4_xboole_0(A_97, B_98), k3_xboole_0(A_97, B_98))=k5_xboole_0(A_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_501, c_998])).
% 12.14/5.21  tff(c_1860, plain, (![A_119, B_120]: (k5_xboole_0(k4_xboole_0(A_119, B_120), k3_xboole_0(A_119, B_120))=A_119)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1038])).
% 12.14/5.21  tff(c_3086, plain, (![B_141, A_142]: (k5_xboole_0(k4_xboole_0(B_141, A_142), k3_xboole_0(A_142, B_141))=B_141)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1860])).
% 12.14/5.21  tff(c_4495, plain, (![A_169, B_170]: (k5_xboole_0(k3_xboole_0(A_169, B_170), B_170)=k4_xboole_0(B_170, A_169))), inference(superposition, [status(thm), theory('equality')], [c_3086, c_2058])).
% 12.14/5.21  tff(c_353, plain, (![A_7, B_8, C_70]: (k5_xboole_0(A_7, k5_xboole_0(k3_xboole_0(A_7, B_8), C_70))=k5_xboole_0(k4_xboole_0(A_7, B_8), C_70))), inference(superposition, [status(thm), theory('equality')], [c_10, c_308])).
% 12.14/5.21  tff(c_4529, plain, (![A_169, B_170]: (k5_xboole_0(k4_xboole_0(A_169, B_170), B_170)=k5_xboole_0(A_169, k4_xboole_0(B_170, A_169)))), inference(superposition, [status(thm), theory('equality')], [c_4495, c_353])).
% 12.14/5.21  tff(c_4596, plain, (![B_170, A_169]: (k2_xboole_0(B_170, A_169)=k2_xboole_0(A_169, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_22, c_4529])).
% 12.14/5.21  tff(c_115, plain, (![A_11, B_12]: (k3_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_102])).
% 12.14/5.21  tff(c_646, plain, (![A_90]: (k3_xboole_0(A_90, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_502, c_135])).
% 12.14/5.21  tff(c_683, plain, (![B_12]: (k4_xboole_0(k1_xboole_0, B_12)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_115, c_646])).
% 12.14/5.21  tff(c_32, plain, (![A_31, B_32]: (r1_tarski(k1_tarski(A_31), k2_tarski(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.14/5.21  tff(c_114, plain, (![A_31, B_32]: (k3_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32))=k1_tarski(A_31))), inference(resolution, [status(thm)], [c_32, c_102])).
% 12.14/5.21  tff(c_1090, plain, (![A_97, B_98]: (k5_xboole_0(k4_xboole_0(A_97, B_98), k3_xboole_0(A_97, B_98))=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1038])).
% 12.14/5.21  tff(c_2084, plain, (![B_123, A_124]: (k5_xboole_0(B_123, k5_xboole_0(A_124, B_123))=A_124)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1946])).
% 12.14/5.21  tff(c_3868, plain, (![A_157, B_158]: (k5_xboole_0(k3_xboole_0(A_157, B_158), A_157)=k4_xboole_0(A_157, B_158))), inference(superposition, [status(thm), theory('equality')], [c_1090, c_2084])).
% 12.14/5.21  tff(c_3931, plain, (![A_31, B_32]: (k5_xboole_0(k1_tarski(A_31), k1_tarski(A_31))=k4_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_3868])).
% 12.14/5.21  tff(c_3968, plain, (![A_31, B_32]: (k4_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_501, c_3931])).
% 12.14/5.21  tff(c_544, plain, (![A_84]: (r1_tarski(k1_xboole_0, A_84))), inference(superposition, [status(thm), theory('equality')], [c_502, c_14])).
% 12.14/5.21  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.14/5.21  tff(c_548, plain, (![A_84]: (k3_xboole_0(k1_xboole_0, A_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_544, c_12])).
% 12.14/5.21  tff(c_12586, plain, (![A_267, B_268, B_269]: (k5_xboole_0(k2_xboole_0(A_267, B_268), k3_xboole_0(k4_xboole_0(B_268, A_267), B_269))=k5_xboole_0(A_267, k4_xboole_0(k4_xboole_0(B_268, A_267), B_269)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1480])).
% 12.14/5.21  tff(c_12705, plain, (![A_31, B_32, B_269]: (k5_xboole_0(k2_tarski(A_31, B_32), k4_xboole_0(k4_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32)), B_269))=k5_xboole_0(k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(A_31)), k3_xboole_0(k1_xboole_0, B_269)))), inference(superposition, [status(thm), theory('equality')], [c_3968, c_12586])).
% 12.14/5.21  tff(c_12798, plain, (![A_31, B_32]: (k2_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32))=k2_tarski(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_4596, c_16, c_683, c_3968, c_16, c_548, c_12705])).
% 12.14/5.21  tff(c_34, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.14/5.21  tff(c_16023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12798, c_34])).
% 12.14/5.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.14/5.21  
% 12.14/5.21  Inference rules
% 12.14/5.21  ----------------------
% 12.14/5.21  #Ref     : 0
% 12.14/5.21  #Sup     : 3919
% 12.14/5.21  #Fact    : 0
% 12.14/5.21  #Define  : 0
% 12.14/5.21  #Split   : 0
% 12.14/5.21  #Chain   : 0
% 12.14/5.21  #Close   : 0
% 12.14/5.21  
% 12.14/5.21  Ordering : KBO
% 12.14/5.21  
% 12.14/5.21  Simplification rules
% 12.14/5.21  ----------------------
% 12.14/5.21  #Subsume      : 83
% 12.14/5.21  #Demod        : 6003
% 12.14/5.21  #Tautology    : 2922
% 12.14/5.21  #SimpNegUnit  : 0
% 12.14/5.21  #BackRed      : 8
% 12.14/5.21  
% 12.14/5.21  #Partial instantiations: 0
% 12.14/5.21  #Strategies tried      : 1
% 12.14/5.21  
% 12.14/5.21  Timing (in seconds)
% 12.14/5.21  ----------------------
% 12.33/5.22  Preprocessing        : 0.48
% 12.33/5.22  Parsing              : 0.25
% 12.33/5.22  CNF conversion       : 0.03
% 12.33/5.22  Main loop            : 3.85
% 12.33/5.22  Inferencing          : 0.89
% 12.33/5.22  Reduction            : 2.17
% 12.33/5.22  Demodulation         : 1.93
% 12.33/5.22  BG Simplification    : 0.11
% 12.33/5.22  Subsumption          : 0.49
% 12.33/5.22  Abstraction          : 0.19
% 12.33/5.22  MUC search           : 0.00
% 12.33/5.22  Cooper               : 0.00
% 12.33/5.22  Total                : 4.38
% 12.33/5.22  Index Insertion      : 0.00
% 12.33/5.22  Index Deletion       : 0.00
% 12.33/5.22  Index Matching       : 0.00
% 12.33/5.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
