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
% DateTime   : Thu Dec  3 09:45:39 EST 2020

% Result     : Theorem 33.23s
% Output     : CNFRefutation 33.34s
% Verified   : 
% Statistics : Number of formulae       :  102 (5030 expanded)
%              Number of leaves         :   27 (1766 expanded)
%              Depth                    :   17
%              Number of atoms          :  101 (6609 expanded)
%              Number of equality atoms :   89 (4536 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k2_xboole_0(A,C),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(c_32,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k1_enumset1(B_25,C_26,D_27)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [A_13] : k2_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(resolution,[status(thm)],[c_22,c_102])).

tff(c_424,plain,(
    ! [A_77,C_78,B_79] : k2_xboole_0(k2_xboole_0(A_77,C_78),k2_xboole_0(B_79,C_78)) = k2_xboole_0(k2_xboole_0(A_77,B_79),C_78) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_493,plain,(
    ! [B_79,A_13] : k2_xboole_0(k2_xboole_0(k1_xboole_0,B_79),A_13) = k2_xboole_0(A_13,k2_xboole_0(B_79,A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_424])).

tff(c_513,plain,(
    ! [A_13,B_79] : k2_xboole_0(A_13,k2_xboole_0(B_79,A_13)) = k2_xboole_0(B_79,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_493])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_499,plain,(
    ! [A_1,B_79] : k2_xboole_0(k2_xboole_0(A_1,B_79),A_1) = k2_xboole_0(A_1,k2_xboole_0(B_79,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_424])).

tff(c_873,plain,(
    ! [A_97,B_98] : k2_xboole_0(k2_xboole_0(A_97,B_98),A_97) = k2_xboole_0(B_98,A_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_499])).

tff(c_24,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_910,plain,(
    ! [A_97,B_98] : k4_xboole_0(k2_xboole_0(A_97,B_98),k2_xboole_0(B_98,A_97)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_24])).

tff(c_994,plain,(
    ! [A_102,B_103] : k4_xboole_0(k2_xboole_0(A_102,B_103),k2_xboole_0(B_103,A_102)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_24])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_334,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | k4_xboole_0(A_64,B_63) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_180])).

tff(c_344,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | k4_xboole_0(B_6,A_5) != k1_xboole_0
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_334])).

tff(c_998,plain,(
    ! [B_103,A_102] :
      ( k2_xboole_0(B_103,A_102) = k2_xboole_0(A_102,B_103)
      | k4_xboole_0(k2_xboole_0(B_103,A_102),k2_xboole_0(A_102,B_103)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_344])).

tff(c_1102,plain,(
    ! [B_104,A_105] : k2_xboole_0(B_104,A_105) = k2_xboole_0(A_105,B_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_998])).

tff(c_1261,plain,(
    ! [C_23,A_21,B_22] : k2_xboole_0(k1_tarski(C_23),k2_tarski(A_21,B_22)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1102])).

tff(c_224,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | k4_xboole_0(A_51,B_52) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_242,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k2_xboole_0(A_14,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_224])).

tff(c_28,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1079,plain,(
    ! [B_103,A_102] : k2_xboole_0(B_103,A_102) = k2_xboole_0(A_102,B_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_998])).

tff(c_26,plain,(
    ! [A_16,C_18,B_17] : k2_xboole_0(k2_xboole_0(A_16,C_18),k2_xboole_0(B_17,C_18)) = k2_xboole_0(k2_xboole_0(A_16,B_17),C_18) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5876,plain,(
    ! [A_194,B_195,C_196,A_197] : k2_xboole_0(k2_xboole_0(A_194,k2_xboole_0(B_195,C_196)),k2_xboole_0(k2_xboole_0(A_197,B_195),C_196)) = k2_xboole_0(k2_xboole_0(A_194,k2_xboole_0(A_197,C_196)),k2_xboole_0(B_195,C_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_424])).

tff(c_6325,plain,(
    ! [A_194,A_197,B_195] : k2_xboole_0(k2_xboole_0(A_194,k2_xboole_0(A_197,k2_xboole_0(A_197,B_195))),k2_xboole_0(B_195,k2_xboole_0(A_197,B_195))) = k2_xboole_0(k2_xboole_0(A_194,k2_xboole_0(B_195,k2_xboole_0(A_197,B_195))),k2_xboole_0(A_197,B_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5876])).

tff(c_7621,plain,(
    ! [A_206,A_207,B_208] : k2_xboole_0(k2_xboole_0(A_206,A_207),B_208) = k2_xboole_0(A_206,k2_xboole_0(A_207,B_208)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_1079,c_513,c_26,c_26,c_242,c_6325])).

tff(c_7849,plain,(
    ! [A_19,B_20,B_208] : k2_xboole_0(k1_tarski(A_19),k2_xboole_0(k1_tarski(B_20),B_208)) = k2_xboole_0(k2_tarski(A_19,B_20),B_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7621])).

tff(c_6408,plain,(
    ! [A_194,A_197,B_195] : k2_xboole_0(k2_xboole_0(A_194,A_197),B_195) = k2_xboole_0(A_194,k2_xboole_0(A_197,B_195)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_1079,c_513,c_26,c_26,c_242,c_6325])).

tff(c_7682,plain,(
    ! [B_208,A_206,A_207] : k2_xboole_0(B_208,k2_xboole_0(A_206,A_207)) = k2_xboole_0(A_206,k2_xboole_0(A_207,B_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7621,c_1079])).

tff(c_487,plain,(
    ! [A_19,B_79,B_20] : k2_xboole_0(k2_xboole_0(k1_tarski(A_19),B_79),k1_tarski(B_20)) = k2_xboole_0(k2_tarski(A_19,B_20),k2_xboole_0(B_79,k1_tarski(B_20))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_424])).

tff(c_2696,plain,(
    ! [A_136,B_137,B_138] : k2_xboole_0(k2_xboole_0(k1_tarski(A_136),B_137),k1_tarski(B_138)) = k2_xboole_0(k2_tarski(A_136,B_138),k2_xboole_0(B_137,k1_tarski(B_138))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_424])).

tff(c_2849,plain,(
    ! [A_136,A_19,B_79,B_20] : k2_xboole_0(k2_xboole_0(k1_tarski(A_136),k2_xboole_0(k1_tarski(A_19),B_79)),k1_tarski(B_20)) = k2_xboole_0(k2_tarski(A_136,B_20),k2_xboole_0(k2_tarski(A_19,B_20),k2_xboole_0(B_79,k1_tarski(B_20)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_2696])).

tff(c_81385,plain,(
    ! [B_20,A_19,B_79,A_136] : k2_xboole_0(k1_tarski(B_20),k2_xboole_0(k2_tarski(A_19,B_20),k2_xboole_0(B_79,k2_tarski(A_136,B_20)))) = k2_xboole_0(k2_tarski(A_136,A_19),k2_xboole_0(B_79,k1_tarski(B_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7849,c_6408,c_7682,c_7682,c_6408,c_6408,c_2849])).

tff(c_3020,plain,(
    ! [A_139,B_140,A_141] : k2_xboole_0(k2_xboole_0(A_139,k1_tarski(B_140)),k2_tarski(A_141,B_140)) = k2_xboole_0(k2_xboole_0(A_139,k1_tarski(A_141)),k1_tarski(B_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_424])).

tff(c_3184,plain,(
    ! [A_19,B_79,A_141,B_20] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(A_19),B_79),k1_tarski(A_141)),k1_tarski(B_20)) = k2_xboole_0(k2_xboole_0(k2_tarski(A_19,B_20),k2_xboole_0(B_79,k1_tarski(B_20))),k2_tarski(A_141,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_3020])).

tff(c_88373,plain,(
    ! [A_141,A_19,B_79,B_20] : k2_xboole_0(k2_tarski(A_141,A_19),k2_xboole_0(B_79,k1_tarski(B_20))) = k2_xboole_0(k1_tarski(A_19),k2_xboole_0(B_79,k2_tarski(A_141,B_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81385,c_6408,c_6408,c_7682,c_28,c_6408,c_6408,c_6408,c_3184])).

tff(c_516,plain,(
    ! [A_80,B_81] : k2_xboole_0(A_80,k2_xboole_0(B_81,A_80)) = k2_xboole_0(B_81,A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_493])).

tff(c_570,plain,(
    ! [B_20,A_19] : k2_xboole_0(k1_tarski(B_20),k2_tarski(A_19,B_20)) = k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_516])).

tff(c_596,plain,(
    ! [B_20,A_19] : k2_xboole_0(k1_tarski(B_20),k2_tarski(A_19,B_20)) = k2_tarski(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_570])).

tff(c_3187,plain,(
    ! [A_19,B_79,B_140,B_20] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(A_19),B_79),k1_tarski(B_140)),k2_tarski(B_20,B_140)) = k2_xboole_0(k2_xboole_0(k2_tarski(A_19,B_20),k2_xboole_0(B_79,k1_tarski(B_20))),k1_tarski(B_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_3020])).

tff(c_91204,plain,(
    ! [B_907,B_908,A_909,B_910] : k2_xboole_0(k1_tarski(B_907),k2_xboole_0(B_908,k2_tarski(A_909,B_910))) = k2_xboole_0(k1_tarski(A_909),k2_xboole_0(B_908,k2_tarski(B_907,B_910))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_88373,c_6408,c_6408,c_7682,c_596,c_6408,c_6408,c_6408,c_3187])).

tff(c_92347,plain,(
    ! [A_21,C_23,B_907,B_22] : k2_xboole_0(k1_tarski(A_21),k2_xboole_0(k1_tarski(C_23),k2_tarski(B_907,B_22))) = k2_xboole_0(k1_tarski(B_907),k1_enumset1(A_21,B_22,C_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1261,c_91204])).

tff(c_92677,plain,(
    ! [B_907,A_21,B_22,C_23] : k2_enumset1(B_907,A_21,B_22,C_23) = k2_enumset1(A_21,B_907,B_22,C_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1261,c_32,c_92347])).

tff(c_3294,plain,(
    ! [A_19,B_140,B_20] : k2_xboole_0(k2_xboole_0(k1_tarski(A_19),k1_tarski(B_140)),k2_tarski(B_20,B_140)) = k2_xboole_0(k2_tarski(A_19,B_20),k1_tarski(B_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3020])).

tff(c_3333,plain,(
    ! [A_19,B_140,B_20] : k2_xboole_0(k2_tarski(A_19,B_140),k2_tarski(B_20,B_140)) = k1_enumset1(A_19,B_20,B_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_3294])).

tff(c_92315,plain,(
    ! [B_20,A_19,B_140,B_907] : k2_xboole_0(k1_tarski(B_20),k2_xboole_0(k2_tarski(A_19,B_140),k2_tarski(B_907,B_140))) = k2_xboole_0(k1_tarski(B_907),k1_enumset1(A_19,B_20,B_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3333,c_91204])).

tff(c_92667,plain,(
    ! [B_907,A_19,B_20,B_140] : k2_enumset1(B_907,A_19,B_20,B_140) = k2_enumset1(B_20,A_19,B_907,B_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3333,c_32,c_92315])).

tff(c_1057,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_tarski(A_19,B_20),k2_xboole_0(k1_tarski(B_20),k1_tarski(A_19))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_994])).

tff(c_1094,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_tarski(A_19,B_20),k2_tarski(B_20,A_19)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1057])).

tff(c_1731,plain,(
    ! [A_120,B_121] : k4_xboole_0(k2_tarski(A_120,B_121),k2_tarski(B_121,A_120)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1057])).

tff(c_1738,plain,(
    ! [B_121,A_120] :
      ( k2_tarski(B_121,A_120) = k2_tarski(A_120,B_121)
      | k4_xboole_0(k2_tarski(B_121,A_120),k2_tarski(A_120,B_121)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1731,c_344])).

tff(c_1782,plain,(
    ! [B_124,A_125] : k2_tarski(B_124,A_125) = k2_tarski(A_125,B_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1738])).

tff(c_10279,plain,(
    ! [B_249,A_250,C_251] : k2_xboole_0(k2_tarski(B_249,A_250),k1_tarski(C_251)) = k1_enumset1(A_250,B_249,C_251) ),
    inference(superposition,[status(thm),theory(equality)],[c_1782,c_30])).

tff(c_10447,plain,(
    ! [B_252,A_253,C_254] : k1_enumset1(B_252,A_253,C_254) = k1_enumset1(A_253,B_252,C_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_10279,c_30])).

tff(c_69468,plain,(
    ! [A_773,B_774,A_775,C_776] : k2_xboole_0(k1_tarski(A_773),k1_enumset1(B_774,A_775,C_776)) = k2_enumset1(A_773,A_775,B_774,C_776) ),
    inference(superposition,[status(thm),theory(equality)],[c_10447,c_32])).

tff(c_69826,plain,(
    ! [A_24,C_26,B_25,D_27] : k2_enumset1(A_24,C_26,B_25,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_69468])).

tff(c_1193,plain,(
    ! [B_25,C_26,D_27,A_24] : k2_xboole_0(k1_enumset1(B_25,C_26,D_27),k1_tarski(A_24)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_1102,c_32])).

tff(c_2961,plain,(
    ! [A_136,A_21,B_22,C_23] : k2_xboole_0(k2_xboole_0(k1_tarski(A_136),k2_tarski(A_21,B_22)),k1_tarski(C_23)) = k2_xboole_0(k2_tarski(A_136,C_23),k1_enumset1(A_21,B_22,C_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2696])).

tff(c_40524,plain,(
    ! [A_136,C_23,A_21,B_22] : k2_xboole_0(k2_tarski(A_136,C_23),k1_enumset1(A_21,B_22,C_23)) = k2_enumset1(C_23,A_21,B_22,A_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_1261,c_2961])).

tff(c_5461,plain,(
    ! [A_190,A_191,B_192,C_193] : k2_xboole_0(k2_xboole_0(A_190,k2_tarski(A_191,B_192)),k1_tarski(C_193)) = k2_xboole_0(k2_xboole_0(A_190,k1_tarski(C_193)),k1_enumset1(A_191,B_192,C_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_424])).

tff(c_5820,plain,(
    ! [A_191,B_192,C_193] : k2_xboole_0(k2_xboole_0(k1_xboole_0,k2_tarski(A_191,B_192)),k1_tarski(C_193)) = k2_xboole_0(k1_tarski(C_193),k1_enumset1(A_191,B_192,C_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_5461])).

tff(c_5864,plain,(
    ! [C_193,A_191,B_192] : k2_xboole_0(k1_tarski(C_193),k1_enumset1(A_191,B_192,C_193)) = k1_enumset1(A_191,B_192,C_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_115,c_5820])).

tff(c_43424,plain,(
    ! [A_577,B_578,B_579] : k2_xboole_0(k1_tarski(A_577),k2_xboole_0(k1_tarski(B_578),B_579)) = k2_xboole_0(k2_tarski(A_577,B_578),B_579) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7621])).

tff(c_43866,plain,(
    ! [A_577,C_193,A_191,B_192] : k2_xboole_0(k2_tarski(A_577,C_193),k1_enumset1(A_191,B_192,C_193)) = k2_xboole_0(k1_tarski(A_577),k1_enumset1(A_191,B_192,C_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5864,c_43424])).

tff(c_44039,plain,(
    ! [C_193,A_191,B_192,A_577] : k2_enumset1(C_193,A_191,B_192,A_577) = k2_enumset1(A_577,A_191,B_192,C_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40524,c_32,c_43866])).

tff(c_34,plain,(
    k2_xboole_0(k1_enumset1('#skF_2','#skF_3','#skF_4'),k1_tarski('#skF_5')) != k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1100,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_enumset1('#skF_2','#skF_3','#skF_4')) != k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_34])).

tff(c_1101,plain,(
    k2_enumset1('#skF_5','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1100])).

tff(c_44056,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_5') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44039,c_1101])).

tff(c_71224,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_5') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69826,c_69826,c_44056])).

tff(c_92703,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_5') != k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92667,c_71224])).

tff(c_94579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92677,c_92703])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 09:30:52 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.23/25.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.23/25.10  
% 33.23/25.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.23/25.10  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 33.23/25.10  
% 33.23/25.10  %Foreground sorts:
% 33.23/25.10  
% 33.23/25.10  
% 33.23/25.10  %Background operators:
% 33.23/25.10  
% 33.23/25.10  
% 33.23/25.10  %Foreground operators:
% 33.23/25.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 33.23/25.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.23/25.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 33.23/25.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 33.23/25.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 33.23/25.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.23/25.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 33.23/25.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 33.23/25.10  tff('#skF_5', type, '#skF_5': $i).
% 33.23/25.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 33.23/25.10  tff('#skF_2', type, '#skF_2': $i).
% 33.23/25.10  tff('#skF_3', type, '#skF_3': $i).
% 33.23/25.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.23/25.10  tff('#skF_4', type, '#skF_4': $i).
% 33.23/25.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.23/25.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 33.23/25.10  
% 33.34/25.12  tff(f_66, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 33.34/25.12  tff(f_64, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 33.34/25.12  tff(f_56, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 33.34/25.12  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 33.34/25.12  tff(f_60, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_1)).
% 33.34/25.12  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 33.34/25.12  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 33.34/25.12  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 33.34/25.12  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 33.34/25.12  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 33.34/25.12  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 33.34/25.12  tff(c_32, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k1_enumset1(B_25, C_26, D_27))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 33.34/25.12  tff(c_30, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(C_23))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 33.34/25.12  tff(c_22, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 33.34/25.12  tff(c_102, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 33.34/25.12  tff(c_115, plain, (![A_13]: (k2_xboole_0(k1_xboole_0, A_13)=A_13)), inference(resolution, [status(thm)], [c_22, c_102])).
% 33.34/25.12  tff(c_424, plain, (![A_77, C_78, B_79]: (k2_xboole_0(k2_xboole_0(A_77, C_78), k2_xboole_0(B_79, C_78))=k2_xboole_0(k2_xboole_0(A_77, B_79), C_78))), inference(cnfTransformation, [status(thm)], [f_60])).
% 33.34/25.12  tff(c_493, plain, (![B_79, A_13]: (k2_xboole_0(k2_xboole_0(k1_xboole_0, B_79), A_13)=k2_xboole_0(A_13, k2_xboole_0(B_79, A_13)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_424])).
% 33.34/25.12  tff(c_513, plain, (![A_13, B_79]: (k2_xboole_0(A_13, k2_xboole_0(B_79, A_13))=k2_xboole_0(B_79, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_493])).
% 33.34/25.12  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 33.34/25.12  tff(c_499, plain, (![A_1, B_79]: (k2_xboole_0(k2_xboole_0(A_1, B_79), A_1)=k2_xboole_0(A_1, k2_xboole_0(B_79, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_424])).
% 33.34/25.12  tff(c_873, plain, (![A_97, B_98]: (k2_xboole_0(k2_xboole_0(A_97, B_98), A_97)=k2_xboole_0(B_98, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_499])).
% 33.34/25.12  tff(c_24, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 33.34/25.12  tff(c_910, plain, (![A_97, B_98]: (k4_xboole_0(k2_xboole_0(A_97, B_98), k2_xboole_0(B_98, A_97))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_873, c_24])).
% 33.34/25.12  tff(c_994, plain, (![A_102, B_103]: (k4_xboole_0(k2_xboole_0(A_102, B_103), k2_xboole_0(B_103, A_102))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_873, c_24])).
% 33.34/25.12  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 33.34/25.12  tff(c_180, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 33.34/25.12  tff(c_334, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | k4_xboole_0(A_64, B_63)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_180])).
% 33.34/25.12  tff(c_344, plain, (![B_6, A_5]: (B_6=A_5 | k4_xboole_0(B_6, A_5)!=k1_xboole_0 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_334])).
% 33.34/25.12  tff(c_998, plain, (![B_103, A_102]: (k2_xboole_0(B_103, A_102)=k2_xboole_0(A_102, B_103) | k4_xboole_0(k2_xboole_0(B_103, A_102), k2_xboole_0(A_102, B_103))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_994, c_344])).
% 33.34/25.12  tff(c_1102, plain, (![B_104, A_105]: (k2_xboole_0(B_104, A_105)=k2_xboole_0(A_105, B_104))), inference(demodulation, [status(thm), theory('equality')], [c_910, c_998])).
% 33.34/25.12  tff(c_1261, plain, (![C_23, A_21, B_22]: (k2_xboole_0(k1_tarski(C_23), k2_tarski(A_21, B_22))=k1_enumset1(A_21, B_22, C_23))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1102])).
% 33.34/25.12  tff(c_224, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | k4_xboole_0(A_51, B_52)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_102])).
% 33.34/25.12  tff(c_242, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k2_xboole_0(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_24, c_224])).
% 33.34/25.12  tff(c_28, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 33.34/25.12  tff(c_1079, plain, (![B_103, A_102]: (k2_xboole_0(B_103, A_102)=k2_xboole_0(A_102, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_910, c_998])).
% 33.34/25.12  tff(c_26, plain, (![A_16, C_18, B_17]: (k2_xboole_0(k2_xboole_0(A_16, C_18), k2_xboole_0(B_17, C_18))=k2_xboole_0(k2_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 33.34/25.12  tff(c_5876, plain, (![A_194, B_195, C_196, A_197]: (k2_xboole_0(k2_xboole_0(A_194, k2_xboole_0(B_195, C_196)), k2_xboole_0(k2_xboole_0(A_197, B_195), C_196))=k2_xboole_0(k2_xboole_0(A_194, k2_xboole_0(A_197, C_196)), k2_xboole_0(B_195, C_196)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_424])).
% 33.34/25.12  tff(c_6325, plain, (![A_194, A_197, B_195]: (k2_xboole_0(k2_xboole_0(A_194, k2_xboole_0(A_197, k2_xboole_0(A_197, B_195))), k2_xboole_0(B_195, k2_xboole_0(A_197, B_195)))=k2_xboole_0(k2_xboole_0(A_194, k2_xboole_0(B_195, k2_xboole_0(A_197, B_195))), k2_xboole_0(A_197, B_195)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5876])).
% 33.34/25.12  tff(c_7621, plain, (![A_206, A_207, B_208]: (k2_xboole_0(k2_xboole_0(A_206, A_207), B_208)=k2_xboole_0(A_206, k2_xboole_0(A_207, B_208)))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_1079, c_513, c_26, c_26, c_242, c_6325])).
% 33.34/25.12  tff(c_7849, plain, (![A_19, B_20, B_208]: (k2_xboole_0(k1_tarski(A_19), k2_xboole_0(k1_tarski(B_20), B_208))=k2_xboole_0(k2_tarski(A_19, B_20), B_208))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7621])).
% 33.34/25.12  tff(c_6408, plain, (![A_194, A_197, B_195]: (k2_xboole_0(k2_xboole_0(A_194, A_197), B_195)=k2_xboole_0(A_194, k2_xboole_0(A_197, B_195)))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_1079, c_513, c_26, c_26, c_242, c_6325])).
% 33.34/25.12  tff(c_7682, plain, (![B_208, A_206, A_207]: (k2_xboole_0(B_208, k2_xboole_0(A_206, A_207))=k2_xboole_0(A_206, k2_xboole_0(A_207, B_208)))), inference(superposition, [status(thm), theory('equality')], [c_7621, c_1079])).
% 33.34/25.12  tff(c_487, plain, (![A_19, B_79, B_20]: (k2_xboole_0(k2_xboole_0(k1_tarski(A_19), B_79), k1_tarski(B_20))=k2_xboole_0(k2_tarski(A_19, B_20), k2_xboole_0(B_79, k1_tarski(B_20))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_424])).
% 33.34/25.12  tff(c_2696, plain, (![A_136, B_137, B_138]: (k2_xboole_0(k2_xboole_0(k1_tarski(A_136), B_137), k1_tarski(B_138))=k2_xboole_0(k2_tarski(A_136, B_138), k2_xboole_0(B_137, k1_tarski(B_138))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_424])).
% 33.34/25.12  tff(c_2849, plain, (![A_136, A_19, B_79, B_20]: (k2_xboole_0(k2_xboole_0(k1_tarski(A_136), k2_xboole_0(k1_tarski(A_19), B_79)), k1_tarski(B_20))=k2_xboole_0(k2_tarski(A_136, B_20), k2_xboole_0(k2_tarski(A_19, B_20), k2_xboole_0(B_79, k1_tarski(B_20)))))), inference(superposition, [status(thm), theory('equality')], [c_487, c_2696])).
% 33.34/25.12  tff(c_81385, plain, (![B_20, A_19, B_79, A_136]: (k2_xboole_0(k1_tarski(B_20), k2_xboole_0(k2_tarski(A_19, B_20), k2_xboole_0(B_79, k2_tarski(A_136, B_20))))=k2_xboole_0(k2_tarski(A_136, A_19), k2_xboole_0(B_79, k1_tarski(B_20))))), inference(demodulation, [status(thm), theory('equality')], [c_7849, c_6408, c_7682, c_7682, c_6408, c_6408, c_2849])).
% 33.34/25.12  tff(c_3020, plain, (![A_139, B_140, A_141]: (k2_xboole_0(k2_xboole_0(A_139, k1_tarski(B_140)), k2_tarski(A_141, B_140))=k2_xboole_0(k2_xboole_0(A_139, k1_tarski(A_141)), k1_tarski(B_140)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_424])).
% 33.34/25.12  tff(c_3184, plain, (![A_19, B_79, A_141, B_20]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(A_19), B_79), k1_tarski(A_141)), k1_tarski(B_20))=k2_xboole_0(k2_xboole_0(k2_tarski(A_19, B_20), k2_xboole_0(B_79, k1_tarski(B_20))), k2_tarski(A_141, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_487, c_3020])).
% 33.34/25.12  tff(c_88373, plain, (![A_141, A_19, B_79, B_20]: (k2_xboole_0(k2_tarski(A_141, A_19), k2_xboole_0(B_79, k1_tarski(B_20)))=k2_xboole_0(k1_tarski(A_19), k2_xboole_0(B_79, k2_tarski(A_141, B_20))))), inference(demodulation, [status(thm), theory('equality')], [c_81385, c_6408, c_6408, c_7682, c_28, c_6408, c_6408, c_6408, c_3184])).
% 33.34/25.12  tff(c_516, plain, (![A_80, B_81]: (k2_xboole_0(A_80, k2_xboole_0(B_81, A_80))=k2_xboole_0(B_81, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_493])).
% 33.34/25.12  tff(c_570, plain, (![B_20, A_19]: (k2_xboole_0(k1_tarski(B_20), k2_tarski(A_19, B_20))=k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_516])).
% 33.34/25.12  tff(c_596, plain, (![B_20, A_19]: (k2_xboole_0(k1_tarski(B_20), k2_tarski(A_19, B_20))=k2_tarski(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_570])).
% 33.34/25.12  tff(c_3187, plain, (![A_19, B_79, B_140, B_20]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(A_19), B_79), k1_tarski(B_140)), k2_tarski(B_20, B_140))=k2_xboole_0(k2_xboole_0(k2_tarski(A_19, B_20), k2_xboole_0(B_79, k1_tarski(B_20))), k1_tarski(B_140)))), inference(superposition, [status(thm), theory('equality')], [c_487, c_3020])).
% 33.34/25.12  tff(c_91204, plain, (![B_907, B_908, A_909, B_910]: (k2_xboole_0(k1_tarski(B_907), k2_xboole_0(B_908, k2_tarski(A_909, B_910)))=k2_xboole_0(k1_tarski(A_909), k2_xboole_0(B_908, k2_tarski(B_907, B_910))))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_88373, c_6408, c_6408, c_7682, c_596, c_6408, c_6408, c_6408, c_3187])).
% 33.34/25.12  tff(c_92347, plain, (![A_21, C_23, B_907, B_22]: (k2_xboole_0(k1_tarski(A_21), k2_xboole_0(k1_tarski(C_23), k2_tarski(B_907, B_22)))=k2_xboole_0(k1_tarski(B_907), k1_enumset1(A_21, B_22, C_23)))), inference(superposition, [status(thm), theory('equality')], [c_1261, c_91204])).
% 33.34/25.12  tff(c_92677, plain, (![B_907, A_21, B_22, C_23]: (k2_enumset1(B_907, A_21, B_22, C_23)=k2_enumset1(A_21, B_907, B_22, C_23))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1261, c_32, c_92347])).
% 33.34/25.12  tff(c_3294, plain, (![A_19, B_140, B_20]: (k2_xboole_0(k2_xboole_0(k1_tarski(A_19), k1_tarski(B_140)), k2_tarski(B_20, B_140))=k2_xboole_0(k2_tarski(A_19, B_20), k1_tarski(B_140)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3020])).
% 33.34/25.12  tff(c_3333, plain, (![A_19, B_140, B_20]: (k2_xboole_0(k2_tarski(A_19, B_140), k2_tarski(B_20, B_140))=k1_enumset1(A_19, B_20, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_3294])).
% 33.34/25.12  tff(c_92315, plain, (![B_20, A_19, B_140, B_907]: (k2_xboole_0(k1_tarski(B_20), k2_xboole_0(k2_tarski(A_19, B_140), k2_tarski(B_907, B_140)))=k2_xboole_0(k1_tarski(B_907), k1_enumset1(A_19, B_20, B_140)))), inference(superposition, [status(thm), theory('equality')], [c_3333, c_91204])).
% 33.34/25.12  tff(c_92667, plain, (![B_907, A_19, B_20, B_140]: (k2_enumset1(B_907, A_19, B_20, B_140)=k2_enumset1(B_20, A_19, B_907, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3333, c_32, c_92315])).
% 33.34/25.12  tff(c_1057, plain, (![A_19, B_20]: (k4_xboole_0(k2_tarski(A_19, B_20), k2_xboole_0(k1_tarski(B_20), k1_tarski(A_19)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_994])).
% 33.34/25.12  tff(c_1094, plain, (![A_19, B_20]: (k4_xboole_0(k2_tarski(A_19, B_20), k2_tarski(B_20, A_19))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1057])).
% 33.34/25.12  tff(c_1731, plain, (![A_120, B_121]: (k4_xboole_0(k2_tarski(A_120, B_121), k2_tarski(B_121, A_120))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1057])).
% 33.34/25.12  tff(c_1738, plain, (![B_121, A_120]: (k2_tarski(B_121, A_120)=k2_tarski(A_120, B_121) | k4_xboole_0(k2_tarski(B_121, A_120), k2_tarski(A_120, B_121))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1731, c_344])).
% 33.34/25.12  tff(c_1782, plain, (![B_124, A_125]: (k2_tarski(B_124, A_125)=k2_tarski(A_125, B_124))), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1738])).
% 33.34/25.12  tff(c_10279, plain, (![B_249, A_250, C_251]: (k2_xboole_0(k2_tarski(B_249, A_250), k1_tarski(C_251))=k1_enumset1(A_250, B_249, C_251))), inference(superposition, [status(thm), theory('equality')], [c_1782, c_30])).
% 33.34/25.12  tff(c_10447, plain, (![B_252, A_253, C_254]: (k1_enumset1(B_252, A_253, C_254)=k1_enumset1(A_253, B_252, C_254))), inference(superposition, [status(thm), theory('equality')], [c_10279, c_30])).
% 33.34/25.12  tff(c_69468, plain, (![A_773, B_774, A_775, C_776]: (k2_xboole_0(k1_tarski(A_773), k1_enumset1(B_774, A_775, C_776))=k2_enumset1(A_773, A_775, B_774, C_776))), inference(superposition, [status(thm), theory('equality')], [c_10447, c_32])).
% 33.34/25.12  tff(c_69826, plain, (![A_24, C_26, B_25, D_27]: (k2_enumset1(A_24, C_26, B_25, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(superposition, [status(thm), theory('equality')], [c_32, c_69468])).
% 33.34/25.12  tff(c_1193, plain, (![B_25, C_26, D_27, A_24]: (k2_xboole_0(k1_enumset1(B_25, C_26, D_27), k1_tarski(A_24))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(superposition, [status(thm), theory('equality')], [c_1102, c_32])).
% 33.34/25.12  tff(c_2961, plain, (![A_136, A_21, B_22, C_23]: (k2_xboole_0(k2_xboole_0(k1_tarski(A_136), k2_tarski(A_21, B_22)), k1_tarski(C_23))=k2_xboole_0(k2_tarski(A_136, C_23), k1_enumset1(A_21, B_22, C_23)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2696])).
% 33.34/25.12  tff(c_40524, plain, (![A_136, C_23, A_21, B_22]: (k2_xboole_0(k2_tarski(A_136, C_23), k1_enumset1(A_21, B_22, C_23))=k2_enumset1(C_23, A_21, B_22, A_136))), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_1261, c_2961])).
% 33.34/25.12  tff(c_5461, plain, (![A_190, A_191, B_192, C_193]: (k2_xboole_0(k2_xboole_0(A_190, k2_tarski(A_191, B_192)), k1_tarski(C_193))=k2_xboole_0(k2_xboole_0(A_190, k1_tarski(C_193)), k1_enumset1(A_191, B_192, C_193)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_424])).
% 33.34/25.12  tff(c_5820, plain, (![A_191, B_192, C_193]: (k2_xboole_0(k2_xboole_0(k1_xboole_0, k2_tarski(A_191, B_192)), k1_tarski(C_193))=k2_xboole_0(k1_tarski(C_193), k1_enumset1(A_191, B_192, C_193)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_5461])).
% 33.34/25.12  tff(c_5864, plain, (![C_193, A_191, B_192]: (k2_xboole_0(k1_tarski(C_193), k1_enumset1(A_191, B_192, C_193))=k1_enumset1(A_191, B_192, C_193))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_115, c_5820])).
% 33.34/25.12  tff(c_43424, plain, (![A_577, B_578, B_579]: (k2_xboole_0(k1_tarski(A_577), k2_xboole_0(k1_tarski(B_578), B_579))=k2_xboole_0(k2_tarski(A_577, B_578), B_579))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7621])).
% 33.34/25.12  tff(c_43866, plain, (![A_577, C_193, A_191, B_192]: (k2_xboole_0(k2_tarski(A_577, C_193), k1_enumset1(A_191, B_192, C_193))=k2_xboole_0(k1_tarski(A_577), k1_enumset1(A_191, B_192, C_193)))), inference(superposition, [status(thm), theory('equality')], [c_5864, c_43424])).
% 33.34/25.12  tff(c_44039, plain, (![C_193, A_191, B_192, A_577]: (k2_enumset1(C_193, A_191, B_192, A_577)=k2_enumset1(A_577, A_191, B_192, C_193))), inference(demodulation, [status(thm), theory('equality')], [c_40524, c_32, c_43866])).
% 33.34/25.12  tff(c_34, plain, (k2_xboole_0(k1_enumset1('#skF_2', '#skF_3', '#skF_4'), k1_tarski('#skF_5'))!=k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 33.34/25.12  tff(c_1100, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_enumset1('#skF_2', '#skF_3', '#skF_4'))!=k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_34])).
% 33.34/25.12  tff(c_1101, plain, (k2_enumset1('#skF_5', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1100])).
% 33.34/25.12  tff(c_44056, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44039, c_1101])).
% 33.34/25.12  tff(c_71224, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_5')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_69826, c_69826, c_44056])).
% 33.34/25.12  tff(c_92703, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_5')!=k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92667, c_71224])).
% 33.34/25.12  tff(c_94579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92677, c_92703])).
% 33.34/25.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.34/25.12  
% 33.34/25.12  Inference rules
% 33.34/25.12  ----------------------
% 33.34/25.12  #Ref     : 0
% 33.34/25.12  #Sup     : 23245
% 33.34/25.12  #Fact    : 0
% 33.34/25.12  #Define  : 0
% 33.34/25.12  #Split   : 0
% 33.34/25.12  #Chain   : 0
% 33.34/25.12  #Close   : 0
% 33.34/25.12  
% 33.34/25.12  Ordering : KBO
% 33.34/25.12  
% 33.34/25.12  Simplification rules
% 33.34/25.12  ----------------------
% 33.34/25.12  #Subsume      : 1881
% 33.34/25.12  #Demod        : 26004
% 33.34/25.12  #Tautology    : 9517
% 33.34/25.12  #SimpNegUnit  : 0
% 33.34/25.12  #BackRed      : 27
% 33.34/25.12  
% 33.34/25.12  #Partial instantiations: 0
% 33.34/25.12  #Strategies tried      : 1
% 33.34/25.12  
% 33.34/25.12  Timing (in seconds)
% 33.34/25.12  ----------------------
% 33.34/25.13  Preprocessing        : 0.28
% 33.34/25.13  Parsing              : 0.15
% 33.34/25.13  CNF conversion       : 0.02
% 33.34/25.13  Main loop            : 24.06
% 33.34/25.13  Inferencing          : 1.97
% 33.34/25.13  Reduction            : 18.29
% 33.34/25.13  Demodulation         : 17.59
% 33.34/25.13  BG Simplification    : 0.31
% 33.34/25.13  Subsumption          : 2.83
% 33.34/25.13  Abstraction          : 0.52
% 33.34/25.13  MUC search           : 0.00
% 33.34/25.13  Cooper               : 0.00
% 33.34/25.13  Total                : 24.38
% 33.34/25.13  Index Insertion      : 0.00
% 33.34/25.13  Index Deletion       : 0.00
% 33.34/25.13  Index Matching       : 0.00
% 33.34/25.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
