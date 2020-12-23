%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:04 EST 2020

% Result     : Theorem 8.05s
% Output     : CNFRefutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :  112 (1695 expanded)
%              Number of leaves         :   34 ( 584 expanded)
%              Depth                    :   27
%              Number of atoms          :  106 (2012 expanded)
%              Number of equality atoms :   80 (1503 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_158,plain,(
    ! [B_14] : k3_xboole_0(B_14,B_14) = B_14 ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_34,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_272,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_293,plain,(
    ! [A_79] : k4_xboole_0(A_79,A_79) = k3_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_272])).

tff(c_40,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_553,plain,(
    ! [A_97] : k5_xboole_0(A_97,k3_xboole_0(A_97,k1_xboole_0)) = k2_xboole_0(A_97,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_40])).

tff(c_30,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_563,plain,(
    ! [A_97] : k4_xboole_0(A_97,k1_xboole_0) = k2_xboole_0(A_97,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_30])).

tff(c_597,plain,(
    ! [A_97] : k2_xboole_0(A_97,A_97) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_563])).

tff(c_302,plain,(
    ! [A_79] : k5_xboole_0(A_79,k3_xboole_0(A_79,k1_xboole_0)) = k2_xboole_0(A_79,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_40])).

tff(c_620,plain,(
    ! [A_102] : k5_xboole_0(A_102,k3_xboole_0(A_102,k1_xboole_0)) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_302])).

tff(c_653,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_620])).

tff(c_1518,plain,(
    ! [A_130,C_131,B_132] :
      ( ~ r2_hidden(A_130,C_131)
      | ~ r2_hidden(A_130,B_132)
      | ~ r2_hidden(A_130,k5_xboole_0(B_132,C_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1807,plain,(
    ! [A_141] :
      ( ~ r2_hidden(A_141,k1_xboole_0)
      | ~ r2_hidden(A_141,k1_xboole_0)
      | ~ r2_hidden(A_141,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_1518])).

tff(c_1821,plain,(
    ! [B_148] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_148),k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_148) ) ),
    inference(resolution,[status(thm)],[c_10,c_1807])).

tff(c_1828,plain,(
    ! [B_149] : r1_tarski(k1_xboole_0,B_149) ),
    inference(resolution,[status(thm)],[c_10,c_1821])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1835,plain,(
    ! [B_149] : k3_xboole_0(k1_xboole_0,B_149) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1828,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_657,plain,(
    ! [A_1] : k5_xboole_0(A_1,k3_xboole_0(k1_xboole_0,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_620])).

tff(c_1844,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_657])).

tff(c_177,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_189,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = k2_xboole_0(k1_xboole_0,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_177])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_199,plain,(
    ! [A_73] : k5_xboole_0(A_73,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_4])).

tff(c_1969,plain,(
    ! [A_73] : k2_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_199])).

tff(c_186,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,A_19) = k2_xboole_0(k1_xboole_0,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_177])).

tff(c_2049,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1969,c_186])).

tff(c_319,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_326,plain,(
    ! [B_81] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_81)) = k4_xboole_0(k1_xboole_0,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_186])).

tff(c_36,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_461,plain,(
    ! [B_89,A_90] : k5_xboole_0(B_89,k3_xboole_0(A_90,B_89)) = k4_xboole_0(B_89,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_472,plain,(
    ! [A_90] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_90,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_186])).

tff(c_796,plain,(
    ! [A_105,B_106,C_107] : k5_xboole_0(k5_xboole_0(A_105,B_106),C_107) = k5_xboole_0(A_105,k5_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_852,plain,(
    ! [C_107] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,C_107)) = k5_xboole_0(k1_xboole_0,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_796])).

tff(c_1102,plain,(
    ! [C_117] : k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,C_117)) = k2_xboole_0(k1_xboole_0,C_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_186,c_186,c_852])).

tff(c_1117,plain,(
    ! [A_90] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_90)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_90,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_1102])).

tff(c_1132,plain,(
    ! [A_118] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_118)) = k4_xboole_0(k1_xboole_0,A_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_1117])).

tff(c_1157,plain,(
    ! [B_21] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_21)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1132])).

tff(c_1168,plain,(
    ! [B_21] : k4_xboole_0(k1_xboole_0,B_21) = k3_xboole_0(k1_xboole_0,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_36,c_1157])).

tff(c_1842,plain,(
    ! [B_21] : k4_xboole_0(k1_xboole_0,B_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_1168])).

tff(c_342,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_2079,plain,(
    ! [A_161] : k5_xboole_0(k1_xboole_0,A_161) = A_161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1969,c_186])).

tff(c_2142,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k3_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_2079])).

tff(c_2176,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1842,c_2142])).

tff(c_290,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_272])).

tff(c_336,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k4_xboole_0(B_14,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_319])).

tff(c_345,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k3_xboole_0(B_14,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_336])).

tff(c_2186,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_345])).

tff(c_56,plain,(
    ! [A_55,B_56] : r1_tarski(k1_tarski(A_55),k2_tarski(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_157,plain,(
    ! [A_55,B_56] : k3_xboole_0(k1_tarski(A_55),k2_tarski(A_55,B_56)) = k1_tarski(A_55) ),
    inference(resolution,[status(thm)],[c_56,c_150])).

tff(c_2278,plain,(
    ! [A_165,B_166,A_164] : k5_xboole_0(A_165,k5_xboole_0(B_166,A_164)) = k5_xboole_0(A_164,k5_xboole_0(A_165,B_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_796])).

tff(c_3369,plain,(
    ! [A_180,A_181] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_180,A_181)) = k5_xboole_0(A_181,A_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_2049,c_2278])).

tff(c_3492,plain,(
    ! [A_15,B_16] : k5_xboole_0(k3_xboole_0(A_15,B_16),A_15) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3369])).

tff(c_3695,plain,(
    ! [A_186,B_187] : k5_xboole_0(k3_xboole_0(A_186,B_187),A_186) = k4_xboole_0(A_186,B_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_3492])).

tff(c_3779,plain,(
    ! [A_55,B_56] : k5_xboole_0(k1_tarski(A_55),k1_tarski(A_55)) = k4_xboole_0(k1_tarski(A_55),k2_tarski(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_3695])).

tff(c_3808,plain,(
    ! [A_55,B_56] : k4_xboole_0(k1_tarski(A_55),k2_tarski(A_55,B_56)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_3779])).

tff(c_2489,plain,(
    ! [B_167] : k5_xboole_0(B_167,B_167) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_345])).

tff(c_38,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2528,plain,(
    ! [B_167,C_24] : k5_xboole_0(B_167,k5_xboole_0(B_167,C_24)) = k5_xboole_0(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_2489,c_38])).

tff(c_2587,plain,(
    ! [B_169,C_170] : k5_xboole_0(B_169,k5_xboole_0(B_169,C_170)) = C_170 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_2528])).

tff(c_4153,plain,(
    ! [B_196,A_197] : k5_xboole_0(B_196,k4_xboole_0(B_196,A_197)) = k3_xboole_0(A_197,B_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_2587])).

tff(c_4217,plain,(
    ! [A_55,B_56] : k3_xboole_0(k2_tarski(A_55,B_56),k1_tarski(A_55)) = k5_xboole_0(k1_tarski(A_55),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3808,c_4153])).

tff(c_6926,plain,(
    ! [A_248,B_249] : k3_xboole_0(k2_tarski(A_248,B_249),k1_tarski(A_248)) = k1_tarski(A_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_4,c_4217])).

tff(c_2561,plain,(
    ! [B_167,C_24] : k5_xboole_0(B_167,k5_xboole_0(B_167,C_24)) = C_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_2528])).

tff(c_3716,plain,(
    ! [A_186,B_187] : k5_xboole_0(k3_xboole_0(A_186,B_187),k4_xboole_0(A_186,B_187)) = A_186 ),
    inference(superposition,[status(thm),theory(equality)],[c_3695,c_2561])).

tff(c_4241,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k3_xboole_0(k4_xboole_0(A_20,B_21),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4153])).

tff(c_4262,plain,(
    ! [A_20,B_21] : k3_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2,c_4241])).

tff(c_284,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,k4_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_272])).

tff(c_5564,plain,(
    ! [A_218,B_219] : k4_xboole_0(A_218,k3_xboole_0(A_218,B_219)) = k4_xboole_0(A_218,B_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4262,c_284])).

tff(c_5610,plain,(
    ! [A_218,B_219] : k5_xboole_0(k3_xboole_0(A_218,B_219),k4_xboole_0(A_218,B_219)) = k2_xboole_0(k3_xboole_0(A_218,B_219),A_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_5564,c_40])).

tff(c_5649,plain,(
    ! [A_218,B_219] : k2_xboole_0(k3_xboole_0(A_218,B_219),A_218) = A_218 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3716,c_5610])).

tff(c_6953,plain,(
    ! [A_248,B_249] : k2_xboole_0(k1_tarski(A_248),k2_tarski(A_248,B_249)) = k2_tarski(A_248,B_249) ),
    inference(superposition,[status(thm),theory(equality)],[c_6926,c_5649])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k2_tarski('#skF_2','#skF_3')) != k2_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6953,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.05/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.85  
% 8.05/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.85  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.05/2.85  
% 8.05/2.85  %Foreground sorts:
% 8.05/2.85  
% 8.05/2.85  
% 8.05/2.85  %Background operators:
% 8.05/2.85  
% 8.05/2.85  
% 8.05/2.85  %Foreground operators:
% 8.05/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.05/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.05/2.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.05/2.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.05/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.05/2.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.05/2.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.05/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.05/2.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.05/2.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.05/2.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.05/2.85  tff('#skF_2', type, '#skF_2': $i).
% 8.05/2.85  tff('#skF_3', type, '#skF_3': $i).
% 8.05/2.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.05/2.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.05/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.05/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.05/2.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.05/2.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.05/2.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.05/2.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.05/2.85  
% 8.05/2.87  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.05/2.87  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.05/2.87  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.05/2.87  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.05/2.87  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.05/2.87  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.05/2.87  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.05/2.87  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.05/2.87  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.05/2.87  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.05/2.87  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.05/2.87  tff(f_79, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.05/2.87  tff(f_82, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 8.05/2.87  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.05/2.87  tff(c_28, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.05/2.87  tff(c_150, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.05/2.87  tff(c_158, plain, (![B_14]: (k3_xboole_0(B_14, B_14)=B_14)), inference(resolution, [status(thm)], [c_28, c_150])).
% 8.05/2.87  tff(c_34, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.87  tff(c_272, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.05/2.87  tff(c_293, plain, (![A_79]: (k4_xboole_0(A_79, A_79)=k3_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_272])).
% 8.05/2.87  tff(c_40, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.05/2.87  tff(c_553, plain, (![A_97]: (k5_xboole_0(A_97, k3_xboole_0(A_97, k1_xboole_0))=k2_xboole_0(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_293, c_40])).
% 8.05/2.87  tff(c_30, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.05/2.87  tff(c_563, plain, (![A_97]: (k4_xboole_0(A_97, k1_xboole_0)=k2_xboole_0(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_553, c_30])).
% 8.05/2.87  tff(c_597, plain, (![A_97]: (k2_xboole_0(A_97, A_97)=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_563])).
% 8.05/2.87  tff(c_302, plain, (![A_79]: (k5_xboole_0(A_79, k3_xboole_0(A_79, k1_xboole_0))=k2_xboole_0(A_79, A_79))), inference(superposition, [status(thm), theory('equality')], [c_293, c_40])).
% 8.05/2.87  tff(c_620, plain, (![A_102]: (k5_xboole_0(A_102, k3_xboole_0(A_102, k1_xboole_0))=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_597, c_302])).
% 8.05/2.87  tff(c_653, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_158, c_620])).
% 8.05/2.87  tff(c_1518, plain, (![A_130, C_131, B_132]: (~r2_hidden(A_130, C_131) | ~r2_hidden(A_130, B_132) | ~r2_hidden(A_130, k5_xboole_0(B_132, C_131)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.05/2.87  tff(c_1807, plain, (![A_141]: (~r2_hidden(A_141, k1_xboole_0) | ~r2_hidden(A_141, k1_xboole_0) | ~r2_hidden(A_141, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_653, c_1518])).
% 8.05/2.87  tff(c_1821, plain, (![B_148]: (~r2_hidden('#skF_1'(k1_xboole_0, B_148), k1_xboole_0) | r1_tarski(k1_xboole_0, B_148))), inference(resolution, [status(thm)], [c_10, c_1807])).
% 8.05/2.87  tff(c_1828, plain, (![B_149]: (r1_tarski(k1_xboole_0, B_149))), inference(resolution, [status(thm)], [c_10, c_1821])).
% 8.05/2.87  tff(c_32, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.05/2.87  tff(c_1835, plain, (![B_149]: (k3_xboole_0(k1_xboole_0, B_149)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1828, c_32])).
% 8.05/2.87  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.05/2.87  tff(c_657, plain, (![A_1]: (k5_xboole_0(A_1, k3_xboole_0(k1_xboole_0, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_620])).
% 8.05/2.87  tff(c_1844, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_657])).
% 8.05/2.87  tff(c_177, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.05/2.87  tff(c_189, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=k2_xboole_0(k1_xboole_0, A_73))), inference(superposition, [status(thm), theory('equality')], [c_34, c_177])).
% 8.05/2.87  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.05/2.87  tff(c_199, plain, (![A_73]: (k5_xboole_0(A_73, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_73))), inference(superposition, [status(thm), theory('equality')], [c_189, c_4])).
% 8.05/2.87  tff(c_1969, plain, (![A_73]: (k2_xboole_0(k1_xboole_0, A_73)=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_1844, c_199])).
% 8.05/2.87  tff(c_186, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, A_19)=k2_xboole_0(k1_xboole_0, A_19))), inference(superposition, [status(thm), theory('equality')], [c_34, c_177])).
% 8.05/2.87  tff(c_2049, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_1969, c_186])).
% 8.05/2.87  tff(c_319, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.05/2.87  tff(c_326, plain, (![B_81]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_81))=k4_xboole_0(k1_xboole_0, B_81))), inference(superposition, [status(thm), theory('equality')], [c_319, c_186])).
% 8.05/2.87  tff(c_36, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.05/2.87  tff(c_461, plain, (![B_89, A_90]: (k5_xboole_0(B_89, k3_xboole_0(A_90, B_89))=k4_xboole_0(B_89, A_90))), inference(superposition, [status(thm), theory('equality')], [c_2, c_319])).
% 8.05/2.87  tff(c_472, plain, (![A_90]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_90, k1_xboole_0))=k4_xboole_0(k1_xboole_0, A_90))), inference(superposition, [status(thm), theory('equality')], [c_461, c_186])).
% 8.05/2.87  tff(c_796, plain, (![A_105, B_106, C_107]: (k5_xboole_0(k5_xboole_0(A_105, B_106), C_107)=k5_xboole_0(A_105, k5_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.05/2.87  tff(c_852, plain, (![C_107]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(k1_xboole_0, C_107))=k5_xboole_0(k1_xboole_0, C_107))), inference(superposition, [status(thm), theory('equality')], [c_653, c_796])).
% 8.05/2.87  tff(c_1102, plain, (![C_117]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(k1_xboole_0, C_117))=k2_xboole_0(k1_xboole_0, C_117))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_186, c_186, c_852])).
% 8.05/2.87  tff(c_1117, plain, (![A_90]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_90))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_90, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_472, c_1102])).
% 8.05/2.87  tff(c_1132, plain, (![A_118]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_118))=k4_xboole_0(k1_xboole_0, A_118))), inference(demodulation, [status(thm), theory('equality')], [c_472, c_1117])).
% 8.05/2.87  tff(c_1157, plain, (![B_21]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_21))=k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1132])).
% 8.05/2.87  tff(c_1168, plain, (![B_21]: (k4_xboole_0(k1_xboole_0, B_21)=k3_xboole_0(k1_xboole_0, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_36, c_1157])).
% 8.05/2.87  tff(c_1842, plain, (![B_21]: (k4_xboole_0(k1_xboole_0, B_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_1168])).
% 8.05/2.87  tff(c_342, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_319])).
% 8.05/2.87  tff(c_2079, plain, (![A_161]: (k5_xboole_0(k1_xboole_0, A_161)=A_161)), inference(demodulation, [status(thm), theory('equality')], [c_1969, c_186])).
% 8.05/2.87  tff(c_2142, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k3_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_342, c_2079])).
% 8.05/2.87  tff(c_2176, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1842, c_2142])).
% 8.05/2.87  tff(c_290, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_272])).
% 8.05/2.87  tff(c_336, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k4_xboole_0(B_14, B_14))), inference(superposition, [status(thm), theory('equality')], [c_158, c_319])).
% 8.05/2.87  tff(c_345, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k3_xboole_0(B_14, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_336])).
% 8.05/2.87  tff(c_2186, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_345])).
% 8.05/2.87  tff(c_56, plain, (![A_55, B_56]: (r1_tarski(k1_tarski(A_55), k2_tarski(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.05/2.87  tff(c_157, plain, (![A_55, B_56]: (k3_xboole_0(k1_tarski(A_55), k2_tarski(A_55, B_56))=k1_tarski(A_55))), inference(resolution, [status(thm)], [c_56, c_150])).
% 8.05/2.87  tff(c_2278, plain, (![A_165, B_166, A_164]: (k5_xboole_0(A_165, k5_xboole_0(B_166, A_164))=k5_xboole_0(A_164, k5_xboole_0(A_165, B_166)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_796])).
% 8.05/2.87  tff(c_3369, plain, (![A_180, A_181]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_180, A_181))=k5_xboole_0(A_181, A_180))), inference(superposition, [status(thm), theory('equality')], [c_2049, c_2278])).
% 8.05/2.87  tff(c_3492, plain, (![A_15, B_16]: (k5_xboole_0(k3_xboole_0(A_15, B_16), A_15)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3369])).
% 8.05/2.87  tff(c_3695, plain, (![A_186, B_187]: (k5_xboole_0(k3_xboole_0(A_186, B_187), A_186)=k4_xboole_0(A_186, B_187))), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_3492])).
% 8.05/2.87  tff(c_3779, plain, (![A_55, B_56]: (k5_xboole_0(k1_tarski(A_55), k1_tarski(A_55))=k4_xboole_0(k1_tarski(A_55), k2_tarski(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_3695])).
% 8.05/2.87  tff(c_3808, plain, (![A_55, B_56]: (k4_xboole_0(k1_tarski(A_55), k2_tarski(A_55, B_56))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_3779])).
% 8.05/2.87  tff(c_2489, plain, (![B_167]: (k5_xboole_0(B_167, B_167)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_345])).
% 8.05/2.87  tff(c_38, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.05/2.87  tff(c_2528, plain, (![B_167, C_24]: (k5_xboole_0(B_167, k5_xboole_0(B_167, C_24))=k5_xboole_0(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_2489, c_38])).
% 8.05/2.87  tff(c_2587, plain, (![B_169, C_170]: (k5_xboole_0(B_169, k5_xboole_0(B_169, C_170))=C_170)), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_2528])).
% 8.05/2.87  tff(c_4153, plain, (![B_196, A_197]: (k5_xboole_0(B_196, k4_xboole_0(B_196, A_197))=k3_xboole_0(A_197, B_196))), inference(superposition, [status(thm), theory('equality')], [c_342, c_2587])).
% 8.05/2.87  tff(c_4217, plain, (![A_55, B_56]: (k3_xboole_0(k2_tarski(A_55, B_56), k1_tarski(A_55))=k5_xboole_0(k1_tarski(A_55), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3808, c_4153])).
% 8.05/2.87  tff(c_6926, plain, (![A_248, B_249]: (k3_xboole_0(k2_tarski(A_248, B_249), k1_tarski(A_248))=k1_tarski(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_4, c_4217])).
% 8.05/2.87  tff(c_2561, plain, (![B_167, C_24]: (k5_xboole_0(B_167, k5_xboole_0(B_167, C_24))=C_24)), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_2528])).
% 8.05/2.87  tff(c_3716, plain, (![A_186, B_187]: (k5_xboole_0(k3_xboole_0(A_186, B_187), k4_xboole_0(A_186, B_187))=A_186)), inference(superposition, [status(thm), theory('equality')], [c_3695, c_2561])).
% 8.05/2.87  tff(c_4241, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k3_xboole_0(k4_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4153])).
% 8.05/2.87  tff(c_4262, plain, (![A_20, B_21]: (k3_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2, c_4241])).
% 8.05/2.87  tff(c_284, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k3_xboole_0(A_20, k4_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_272])).
% 8.05/2.87  tff(c_5564, plain, (![A_218, B_219]: (k4_xboole_0(A_218, k3_xboole_0(A_218, B_219))=k4_xboole_0(A_218, B_219))), inference(demodulation, [status(thm), theory('equality')], [c_4262, c_284])).
% 8.05/2.87  tff(c_5610, plain, (![A_218, B_219]: (k5_xboole_0(k3_xboole_0(A_218, B_219), k4_xboole_0(A_218, B_219))=k2_xboole_0(k3_xboole_0(A_218, B_219), A_218))), inference(superposition, [status(thm), theory('equality')], [c_5564, c_40])).
% 8.05/2.87  tff(c_5649, plain, (![A_218, B_219]: (k2_xboole_0(k3_xboole_0(A_218, B_219), A_218)=A_218)), inference(demodulation, [status(thm), theory('equality')], [c_3716, c_5610])).
% 8.05/2.87  tff(c_6953, plain, (![A_248, B_249]: (k2_xboole_0(k1_tarski(A_248), k2_tarski(A_248, B_249))=k2_tarski(A_248, B_249))), inference(superposition, [status(thm), theory('equality')], [c_6926, c_5649])).
% 8.05/2.87  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_2'), k2_tarski('#skF_2', '#skF_3'))!=k2_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.05/2.87  tff(c_12549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6953, c_58])).
% 8.05/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.87  
% 8.05/2.87  Inference rules
% 8.05/2.87  ----------------------
% 8.05/2.87  #Ref     : 0
% 8.05/2.87  #Sup     : 3106
% 8.05/2.87  #Fact    : 0
% 8.05/2.87  #Define  : 0
% 8.05/2.87  #Split   : 0
% 8.05/2.87  #Chain   : 0
% 8.05/2.87  #Close   : 0
% 8.05/2.87  
% 8.05/2.87  Ordering : KBO
% 8.05/2.87  
% 8.05/2.87  Simplification rules
% 8.05/2.87  ----------------------
% 8.05/2.87  #Subsume      : 179
% 8.05/2.87  #Demod        : 3349
% 8.05/2.87  #Tautology    : 2002
% 8.05/2.87  #SimpNegUnit  : 0
% 8.05/2.87  #BackRed      : 19
% 8.05/2.87  
% 8.05/2.87  #Partial instantiations: 0
% 8.05/2.87  #Strategies tried      : 1
% 8.05/2.87  
% 8.05/2.87  Timing (in seconds)
% 8.05/2.87  ----------------------
% 8.05/2.87  Preprocessing        : 0.36
% 8.05/2.87  Parsing              : 0.19
% 8.05/2.87  CNF conversion       : 0.02
% 8.05/2.87  Main loop            : 1.67
% 8.05/2.87  Inferencing          : 0.44
% 8.05/2.87  Reduction            : 0.86
% 8.05/2.87  Demodulation         : 0.75
% 8.05/2.87  BG Simplification    : 0.06
% 8.05/2.87  Subsumption          : 0.23
% 8.05/2.87  Abstraction          : 0.08
% 8.05/2.87  MUC search           : 0.00
% 8.05/2.87  Cooper               : 0.00
% 8.05/2.87  Total                : 2.07
% 8.05/2.87  Index Insertion      : 0.00
% 8.05/2.87  Index Deletion       : 0.00
% 8.05/2.87  Index Matching       : 0.00
% 8.05/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
