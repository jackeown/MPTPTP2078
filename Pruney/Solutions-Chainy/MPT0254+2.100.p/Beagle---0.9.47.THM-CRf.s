%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:32 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  137 (2618 expanded)
%              Number of leaves         :   46 ( 912 expanded)
%              Depth                    :   15
%              Number of atoms          :  131 (2698 expanded)
%              Number of equality atoms :   94 (2483 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_94,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_93,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_790,plain,(
    ! [A_120,B_121] : k5_xboole_0(k5_xboole_0(A_120,B_121),k3_xboole_0(A_120,B_121)) = k2_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_847,plain,(
    ! [A_16] : k5_xboole_0(k5_xboole_0(A_16,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_790])).

tff(c_862,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_847])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_438,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_458,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_438])).

tff(c_30,plain,(
    ! [A_26,B_27] : k5_xboole_0(k5_xboole_0(A_26,B_27),k3_xboole_0(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_894,plain,(
    ! [A_124,B_125,C_126] : k5_xboole_0(k5_xboole_0(A_124,B_125),C_126) = k5_xboole_0(A_124,k5_xboole_0(B_125,C_126)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_941,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k5_xboole_0(B_27,k3_xboole_0(A_26,B_27))) = k2_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_894])).

tff(c_993,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_941])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2569,plain,(
    ! [A_206,B_207,C_208] : k5_xboole_0(k5_xboole_0(A_206,B_207),C_208) = k5_xboole_0(B_207,k5_xboole_0(A_206,C_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_894])).

tff(c_2620,plain,(
    ! [B_207,A_206] : k5_xboole_0(B_207,k5_xboole_0(A_206,k3_xboole_0(A_206,B_207))) = k2_xboole_0(A_206,B_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_2569,c_30])).

tff(c_2765,plain,(
    ! [B_209,A_210] : k2_xboole_0(B_209,A_210) = k2_xboole_0(A_210,B_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_10,c_2620])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2820,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2765,c_64])).

tff(c_1502,plain,(
    ! [A_150,B_151] : k5_xboole_0(A_150,k4_xboole_0(B_151,A_150)) = k2_xboole_0(A_150,B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_941])).

tff(c_248,plain,(
    ! [B_78,A_79] : k5_xboole_0(B_78,A_79) = k5_xboole_0(A_79,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_264,plain,(
    ! [A_79] : k5_xboole_0(k1_xboole_0,A_79) = A_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_22])).

tff(c_28,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_982,plain,(
    ! [A_25,C_126] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_126)) = k5_xboole_0(k1_xboole_0,C_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_894])).

tff(c_997,plain,(
    ! [A_25,C_126] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_126)) = C_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_982])).

tff(c_3033,plain,(
    ! [A_213,B_214] : k5_xboole_0(A_213,k2_xboole_0(A_213,B_214)) = k4_xboole_0(B_214,A_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_1502,c_997])).

tff(c_3075,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2820,c_3033])).

tff(c_3128,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3075])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_373,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_387,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),A_17) = k4_xboole_0(A_17,B_18) ),
    inference(resolution,[status(thm)],[c_18,c_373])).

tff(c_1039,plain,(
    ! [A_129,C_130] : k5_xboole_0(A_129,k5_xboole_0(A_129,C_130)) = C_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_982])).

tff(c_1148,plain,(
    ! [A_134,B_135] : k5_xboole_0(A_134,k5_xboole_0(B_135,A_134)) = B_135 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1039])).

tff(c_1091,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1039])).

tff(c_1151,plain,(
    ! [B_135,A_134] : k5_xboole_0(k5_xboole_0(B_135,A_134),B_135) = A_134 ),
    inference(superposition,[status(thm),theory(equality)],[c_1148,c_1091])).

tff(c_173,plain,(
    ! [B_76,A_77] : k3_xboole_0(B_76,A_77) = k3_xboole_0(A_77,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_199,plain,(
    ! [A_77,B_76] : r1_tarski(k3_xboole_0(A_77,B_76),B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_12])).

tff(c_2087,plain,(
    ! [A_181,B_182] : k3_xboole_0(k3_xboole_0(A_181,B_182),B_182) = k3_xboole_0(A_181,B_182) ),
    inference(resolution,[status(thm)],[c_199,c_373])).

tff(c_2118,plain,(
    ! [A_181,B_182] : k5_xboole_0(k5_xboole_0(k3_xboole_0(A_181,B_182),B_182),k3_xboole_0(A_181,B_182)) = k2_xboole_0(k3_xboole_0(A_181,B_182),B_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_2087,c_30])).

tff(c_2222,plain,(
    ! [A_189,B_190] : k2_xboole_0(k3_xboole_0(A_189,B_190),B_190) = B_190 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_2118])).

tff(c_2245,plain,(
    ! [A_17,B_18] : k2_xboole_0(k4_xboole_0(A_17,B_18),A_17) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_2222])).

tff(c_3144,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_2245])).

tff(c_3163,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2820,c_3144])).

tff(c_3349,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3163,c_2820])).

tff(c_3351,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_3349])).

tff(c_62,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3385,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3351,c_3351,c_62])).

tff(c_464,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = k4_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_438])).

tff(c_471,plain,(
    ! [A_97] : k4_xboole_0(A_97,k1_xboole_0) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_464])).

tff(c_493,plain,(
    ! [A_98] : r1_tarski(A_98,A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_18])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_501,plain,(
    ! [A_98] : k3_xboole_0(A_98,A_98) = A_98 ),
    inference(resolution,[status(thm)],[c_493,c_14])).

tff(c_853,plain,(
    ! [A_25] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_25,A_25)) = k2_xboole_0(A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_790])).

tff(c_864,plain,(
    ! [A_25] : k2_xboole_0(A_25,A_25) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_501,c_853])).

tff(c_32,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_408,plain,(
    ! [A_91,B_92] : k3_tarski(k2_tarski(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_417,plain,(
    ! [A_28] : k3_tarski(k1_tarski(A_28)) = k2_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_408])).

tff(c_999,plain,(
    ! [A_28] : k3_tarski(k1_tarski(A_28)) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_417])).

tff(c_3356,plain,(
    k3_tarski(k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3163,c_999])).

tff(c_3632,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3385,c_3351,c_3356])).

tff(c_612,plain,(
    ! [A_111,B_112] : k3_xboole_0(k4_xboole_0(A_111,B_112),A_111) = k4_xboole_0(A_111,B_112) ),
    inference(resolution,[status(thm)],[c_18,c_373])).

tff(c_621,plain,(
    ! [A_111,B_112] : k5_xboole_0(k4_xboole_0(A_111,B_112),k4_xboole_0(A_111,B_112)) = k4_xboole_0(k4_xboole_0(A_111,B_112),A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_10])).

tff(c_663,plain,(
    ! [A_111,B_112] : k4_xboole_0(k4_xboole_0(A_111,B_112),A_111) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_621])).

tff(c_1541,plain,(
    ! [A_111,B_112] : k2_xboole_0(A_111,k4_xboole_0(A_111,B_112)) = k5_xboole_0(A_111,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_1502])).

tff(c_1558,plain,(
    ! [A_111,B_112] : k2_xboole_0(A_111,k4_xboole_0(A_111,B_112)) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1541])).

tff(c_3147,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_1558])).

tff(c_3164,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3147])).

tff(c_3416,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3351,c_3164])).

tff(c_3639,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3632,c_3416])).

tff(c_481,plain,(
    ! [A_97] : r1_tarski(A_97,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_18])).

tff(c_24,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_579,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | ~ r2_hidden(C_104,k3_xboole_0(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_594,plain,(
    ! [A_16,C_104] :
      ( ~ r1_xboole_0(A_16,k1_xboole_0)
      | ~ r2_hidden(C_104,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_579])).

tff(c_596,plain,(
    ! [C_104] : ~ r2_hidden(C_104,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_594])).

tff(c_60,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1690,plain,(
    ! [A_156,B_157] :
      ( r1_tarski('#skF_2'(A_156,B_157),A_156)
      | r2_hidden('#skF_3'(A_156,B_157),B_157)
      | k1_zfmisc_1(A_156) = B_157 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2000,plain,(
    ! [A_173] :
      ( r1_tarski('#skF_2'(A_173,k1_xboole_0),A_173)
      | k1_zfmisc_1(A_173) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1690,c_596])).

tff(c_20,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2007,plain,
    ( '#skF_2'(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2000,c_20])).

tff(c_2011,plain,
    ( '#skF_2'(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2007])).

tff(c_2012,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2011])).

tff(c_400,plain,(
    ! [C_89,A_90] :
      ( r2_hidden(C_89,k1_zfmisc_1(A_90))
      | ~ r1_tarski(C_89,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_406,plain,(
    ! [C_89] :
      ( r2_hidden(C_89,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_89,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_400])).

tff(c_2013,plain,(
    ! [C_89] :
      ( r2_hidden(C_89,k1_xboole_0)
      | ~ r1_tarski(C_89,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_406])).

tff(c_2045,plain,(
    ! [C_180] : ~ r1_tarski(C_180,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_596,c_2013])).

tff(c_2070,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_481,c_2045])).

tff(c_2072,plain,(
    k1_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2011])).

tff(c_3362,plain,(
    k1_tarski('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3351,c_3351,c_2072])).

tff(c_3633,plain,(
    k1_tarski('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3632,c_3632,c_3362])).

tff(c_3854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3639,c_3633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:31:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.85  
% 4.62/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 4.62/1.85  
% 4.62/1.85  %Foreground sorts:
% 4.62/1.85  
% 4.62/1.85  
% 4.62/1.85  %Background operators:
% 4.62/1.85  
% 4.62/1.85  
% 4.62/1.85  %Foreground operators:
% 4.62/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.62/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.62/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.62/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.62/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.62/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.62/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.62/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.62/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.62/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.62/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.62/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.62/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.62/1.85  
% 4.62/1.87  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.62/1.87  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.62/1.87  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.62/1.87  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.62/1.87  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.62/1.87  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.62/1.87  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.62/1.87  tff(f_98, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.62/1.87  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.62/1.87  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.62/1.87  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.62/1.87  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.62/1.87  tff(f_94, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 4.62/1.87  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.62/1.87  tff(f_92, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.62/1.87  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.62/1.87  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.62/1.87  tff(f_93, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 4.62/1.87  tff(f_90, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.62/1.87  tff(f_59, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.62/1.87  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.62/1.87  tff(c_16, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.62/1.87  tff(c_790, plain, (![A_120, B_121]: (k5_xboole_0(k5_xboole_0(A_120, B_121), k3_xboole_0(A_120, B_121))=k2_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.62/1.87  tff(c_847, plain, (![A_16]: (k5_xboole_0(k5_xboole_0(A_16, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_790])).
% 4.62/1.87  tff(c_862, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_847])).
% 4.62/1.87  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.62/1.87  tff(c_438, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.62/1.87  tff(c_458, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_438])).
% 4.62/1.87  tff(c_30, plain, (![A_26, B_27]: (k5_xboole_0(k5_xboole_0(A_26, B_27), k3_xboole_0(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.62/1.87  tff(c_894, plain, (![A_124, B_125, C_126]: (k5_xboole_0(k5_xboole_0(A_124, B_125), C_126)=k5_xboole_0(A_124, k5_xboole_0(B_125, C_126)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.62/1.87  tff(c_941, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k5_xboole_0(B_27, k3_xboole_0(A_26, B_27)))=k2_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_30, c_894])).
% 4.62/1.87  tff(c_993, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_941])).
% 4.62/1.87  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.62/1.87  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.62/1.87  tff(c_2569, plain, (![A_206, B_207, C_208]: (k5_xboole_0(k5_xboole_0(A_206, B_207), C_208)=k5_xboole_0(B_207, k5_xboole_0(A_206, C_208)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_894])).
% 4.62/1.87  tff(c_2620, plain, (![B_207, A_206]: (k5_xboole_0(B_207, k5_xboole_0(A_206, k3_xboole_0(A_206, B_207)))=k2_xboole_0(A_206, B_207))), inference(superposition, [status(thm), theory('equality')], [c_2569, c_30])).
% 4.62/1.87  tff(c_2765, plain, (![B_209, A_210]: (k2_xboole_0(B_209, A_210)=k2_xboole_0(A_210, B_209))), inference(demodulation, [status(thm), theory('equality')], [c_993, c_10, c_2620])).
% 4.62/1.87  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.62/1.87  tff(c_2820, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2765, c_64])).
% 4.62/1.87  tff(c_1502, plain, (![A_150, B_151]: (k5_xboole_0(A_150, k4_xboole_0(B_151, A_150))=k2_xboole_0(A_150, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_941])).
% 4.62/1.87  tff(c_248, plain, (![B_78, A_79]: (k5_xboole_0(B_78, A_79)=k5_xboole_0(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.62/1.87  tff(c_264, plain, (![A_79]: (k5_xboole_0(k1_xboole_0, A_79)=A_79)), inference(superposition, [status(thm), theory('equality')], [c_248, c_22])).
% 4.62/1.87  tff(c_28, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.62/1.87  tff(c_982, plain, (![A_25, C_126]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_126))=k5_xboole_0(k1_xboole_0, C_126))), inference(superposition, [status(thm), theory('equality')], [c_28, c_894])).
% 4.62/1.87  tff(c_997, plain, (![A_25, C_126]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_126))=C_126)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_982])).
% 4.62/1.87  tff(c_3033, plain, (![A_213, B_214]: (k5_xboole_0(A_213, k2_xboole_0(A_213, B_214))=k4_xboole_0(B_214, A_213))), inference(superposition, [status(thm), theory('equality')], [c_1502, c_997])).
% 4.62/1.87  tff(c_3075, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2820, c_3033])).
% 4.62/1.87  tff(c_3128, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3075])).
% 4.62/1.87  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.62/1.87  tff(c_373, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.62/1.87  tff(c_387, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), A_17)=k4_xboole_0(A_17, B_18))), inference(resolution, [status(thm)], [c_18, c_373])).
% 4.62/1.87  tff(c_1039, plain, (![A_129, C_130]: (k5_xboole_0(A_129, k5_xboole_0(A_129, C_130))=C_130)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_982])).
% 4.62/1.87  tff(c_1148, plain, (![A_134, B_135]: (k5_xboole_0(A_134, k5_xboole_0(B_135, A_134))=B_135)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1039])).
% 4.62/1.87  tff(c_1091, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1039])).
% 4.62/1.87  tff(c_1151, plain, (![B_135, A_134]: (k5_xboole_0(k5_xboole_0(B_135, A_134), B_135)=A_134)), inference(superposition, [status(thm), theory('equality')], [c_1148, c_1091])).
% 4.62/1.87  tff(c_173, plain, (![B_76, A_77]: (k3_xboole_0(B_76, A_77)=k3_xboole_0(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.62/1.87  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.62/1.87  tff(c_199, plain, (![A_77, B_76]: (r1_tarski(k3_xboole_0(A_77, B_76), B_76))), inference(superposition, [status(thm), theory('equality')], [c_173, c_12])).
% 4.62/1.87  tff(c_2087, plain, (![A_181, B_182]: (k3_xboole_0(k3_xboole_0(A_181, B_182), B_182)=k3_xboole_0(A_181, B_182))), inference(resolution, [status(thm)], [c_199, c_373])).
% 4.62/1.87  tff(c_2118, plain, (![A_181, B_182]: (k5_xboole_0(k5_xboole_0(k3_xboole_0(A_181, B_182), B_182), k3_xboole_0(A_181, B_182))=k2_xboole_0(k3_xboole_0(A_181, B_182), B_182))), inference(superposition, [status(thm), theory('equality')], [c_2087, c_30])).
% 4.62/1.87  tff(c_2222, plain, (![A_189, B_190]: (k2_xboole_0(k3_xboole_0(A_189, B_190), B_190)=B_190)), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_2118])).
% 4.62/1.87  tff(c_2245, plain, (![A_17, B_18]: (k2_xboole_0(k4_xboole_0(A_17, B_18), A_17)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_387, c_2222])).
% 4.62/1.87  tff(c_3144, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3128, c_2245])).
% 4.62/1.87  tff(c_3163, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2820, c_3144])).
% 4.62/1.87  tff(c_3349, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3163, c_2820])).
% 4.62/1.87  tff(c_3351, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_862, c_3349])).
% 4.62/1.87  tff(c_62, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.62/1.87  tff(c_3385, plain, (k3_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3351, c_3351, c_62])).
% 4.62/1.87  tff(c_464, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=k4_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_438])).
% 4.62/1.87  tff(c_471, plain, (![A_97]: (k4_xboole_0(A_97, k1_xboole_0)=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_464])).
% 4.62/1.87  tff(c_493, plain, (![A_98]: (r1_tarski(A_98, A_98))), inference(superposition, [status(thm), theory('equality')], [c_471, c_18])).
% 4.62/1.87  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.62/1.87  tff(c_501, plain, (![A_98]: (k3_xboole_0(A_98, A_98)=A_98)), inference(resolution, [status(thm)], [c_493, c_14])).
% 4.62/1.87  tff(c_853, plain, (![A_25]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_25, A_25))=k2_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_28, c_790])).
% 4.62/1.87  tff(c_864, plain, (![A_25]: (k2_xboole_0(A_25, A_25)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_501, c_853])).
% 4.62/1.87  tff(c_32, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.62/1.87  tff(c_408, plain, (![A_91, B_92]: (k3_tarski(k2_tarski(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.62/1.87  tff(c_417, plain, (![A_28]: (k3_tarski(k1_tarski(A_28))=k2_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_32, c_408])).
% 4.62/1.87  tff(c_999, plain, (![A_28]: (k3_tarski(k1_tarski(A_28))=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_864, c_417])).
% 4.62/1.87  tff(c_3356, plain, (k3_tarski(k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3163, c_999])).
% 4.62/1.87  tff(c_3632, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3385, c_3351, c_3356])).
% 4.62/1.87  tff(c_612, plain, (![A_111, B_112]: (k3_xboole_0(k4_xboole_0(A_111, B_112), A_111)=k4_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_18, c_373])).
% 4.62/1.87  tff(c_621, plain, (![A_111, B_112]: (k5_xboole_0(k4_xboole_0(A_111, B_112), k4_xboole_0(A_111, B_112))=k4_xboole_0(k4_xboole_0(A_111, B_112), A_111))), inference(superposition, [status(thm), theory('equality')], [c_612, c_10])).
% 4.62/1.87  tff(c_663, plain, (![A_111, B_112]: (k4_xboole_0(k4_xboole_0(A_111, B_112), A_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_621])).
% 4.62/1.87  tff(c_1541, plain, (![A_111, B_112]: (k2_xboole_0(A_111, k4_xboole_0(A_111, B_112))=k5_xboole_0(A_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_663, c_1502])).
% 4.62/1.87  tff(c_1558, plain, (![A_111, B_112]: (k2_xboole_0(A_111, k4_xboole_0(A_111, B_112))=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1541])).
% 4.62/1.87  tff(c_3147, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3128, c_1558])).
% 4.62/1.87  tff(c_3164, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3147])).
% 4.62/1.87  tff(c_3416, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3351, c_3164])).
% 4.62/1.87  tff(c_3639, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3632, c_3416])).
% 4.62/1.87  tff(c_481, plain, (![A_97]: (r1_tarski(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_471, c_18])).
% 4.62/1.87  tff(c_24, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.62/1.87  tff(c_579, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | ~r2_hidden(C_104, k3_xboole_0(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.62/1.87  tff(c_594, plain, (![A_16, C_104]: (~r1_xboole_0(A_16, k1_xboole_0) | ~r2_hidden(C_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_579])).
% 4.62/1.87  tff(c_596, plain, (![C_104]: (~r2_hidden(C_104, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_594])).
% 4.62/1.87  tff(c_60, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.62/1.87  tff(c_1690, plain, (![A_156, B_157]: (r1_tarski('#skF_2'(A_156, B_157), A_156) | r2_hidden('#skF_3'(A_156, B_157), B_157) | k1_zfmisc_1(A_156)=B_157)), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.62/1.87  tff(c_2000, plain, (![A_173]: (r1_tarski('#skF_2'(A_173, k1_xboole_0), A_173) | k1_zfmisc_1(A_173)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1690, c_596])).
% 4.62/1.87  tff(c_20, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.62/1.87  tff(c_2007, plain, ('#skF_2'(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2000, c_20])).
% 4.62/1.87  tff(c_2011, plain, ('#skF_2'(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k1_tarski(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2007])).
% 4.62/1.87  tff(c_2012, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2011])).
% 4.62/1.87  tff(c_400, plain, (![C_89, A_90]: (r2_hidden(C_89, k1_zfmisc_1(A_90)) | ~r1_tarski(C_89, A_90))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.62/1.87  tff(c_406, plain, (![C_89]: (r2_hidden(C_89, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_400])).
% 4.62/1.87  tff(c_2013, plain, (![C_89]: (r2_hidden(C_89, k1_xboole_0) | ~r1_tarski(C_89, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_406])).
% 4.62/1.87  tff(c_2045, plain, (![C_180]: (~r1_tarski(C_180, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_596, c_2013])).
% 4.62/1.87  tff(c_2070, plain, $false, inference(resolution, [status(thm)], [c_481, c_2045])).
% 4.62/1.87  tff(c_2072, plain, (k1_tarski(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2011])).
% 4.62/1.87  tff(c_3362, plain, (k1_tarski('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3351, c_3351, c_2072])).
% 4.62/1.87  tff(c_3633, plain, (k1_tarski('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3632, c_3632, c_3362])).
% 4.62/1.87  tff(c_3854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3639, c_3633])).
% 4.62/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.87  
% 4.62/1.87  Inference rules
% 4.62/1.87  ----------------------
% 4.62/1.87  #Ref     : 0
% 4.62/1.87  #Sup     : 939
% 4.62/1.87  #Fact    : 0
% 4.62/1.87  #Define  : 0
% 4.62/1.87  #Split   : 1
% 4.62/1.87  #Chain   : 0
% 4.62/1.87  #Close   : 0
% 4.62/1.88  
% 4.62/1.88  Ordering : KBO
% 4.62/1.88  
% 4.62/1.88  Simplification rules
% 4.62/1.88  ----------------------
% 4.62/1.88  #Subsume      : 34
% 4.62/1.88  #Demod        : 728
% 4.62/1.88  #Tautology    : 591
% 4.62/1.88  #SimpNegUnit  : 6
% 4.62/1.88  #BackRed      : 42
% 4.62/1.88  
% 4.62/1.88  #Partial instantiations: 0
% 4.62/1.88  #Strategies tried      : 1
% 4.62/1.88  
% 4.62/1.88  Timing (in seconds)
% 4.62/1.88  ----------------------
% 4.62/1.88  Preprocessing        : 0.34
% 4.62/1.88  Parsing              : 0.19
% 4.62/1.88  CNF conversion       : 0.02
% 4.62/1.88  Main loop            : 0.74
% 4.62/1.88  Inferencing          : 0.23
% 4.62/1.88  Reduction            : 0.33
% 4.62/1.88  Demodulation         : 0.28
% 4.62/1.88  BG Simplification    : 0.03
% 4.62/1.88  Subsumption          : 0.10
% 4.62/1.88  Abstraction          : 0.04
% 4.62/1.88  MUC search           : 0.00
% 4.62/1.88  Cooper               : 0.00
% 4.62/1.88  Total                : 1.13
% 4.62/1.88  Index Insertion      : 0.00
% 4.62/1.88  Index Deletion       : 0.00
% 4.62/1.88  Index Matching       : 0.00
% 4.62/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
