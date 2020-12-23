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
% DateTime   : Thu Dec  3 09:54:35 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  107 (1136 expanded)
%              Number of leaves         :   32 ( 394 expanded)
%              Depth                    :   17
%              Number of atoms          :  101 (1374 expanded)
%              Number of equality atoms :   80 ( 981 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_69,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_120])).

tff(c_302,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_323,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_302])).

tff(c_352,plain,(
    ! [A_72] : k3_xboole_0(A_72,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_323])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_357,plain,(
    ! [A_72] : k5_xboole_0(A_72,k1_xboole_0) = k4_xboole_0(A_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_14])).

tff(c_383,plain,(
    ! [A_72] : k5_xboole_0(A_72,k1_xboole_0) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_357])).

tff(c_170,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k1_tarski(A_55),B_56)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(k1_tarski(A_55),B_56) = k1_xboole_0
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_170,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_329,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_344,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_329])).

tff(c_811,plain,(
    ! [A_96,B_97] : k5_xboole_0(k5_xboole_0(A_96,B_97),k3_xboole_0(A_96,B_97)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] : k5_xboole_0(k5_xboole_0(A_17,B_18),C_19) = k5_xboole_0(A_17,k5_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_823,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k5_xboole_0(B_97,k3_xboole_0(A_96,B_97))) = k2_xboole_0(A_96,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_24])).

tff(c_1034,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k4_xboole_0(B_107,A_106)) = k2_xboole_0(A_106,B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_823])).

tff(c_1057,plain,(
    ! [B_56,A_55] :
      ( k2_xboole_0(B_56,k1_tarski(A_55)) = k5_xboole_0(B_56,k1_xboole_0)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1034])).

tff(c_1083,plain,(
    ! [B_56,A_55] :
      ( k2_xboole_0(B_56,k1_tarski(A_55)) = B_56
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_1057])).

tff(c_869,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k4_xboole_0(B_97,A_96)) = k2_xboole_0(A_96,B_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_823])).

tff(c_1076,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1034])).

tff(c_1086,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_1076])).

tff(c_42,plain,(
    ! [A_36] : r1_tarski(A_36,k1_zfmisc_1(k3_tarski(A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_131,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_zfmisc_1(k3_tarski(A_36))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_120])).

tff(c_157,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_168,plain,(
    ! [A_36] : k3_xboole_0(A_36,k1_zfmisc_1(k3_tarski(A_36))) = A_36 ),
    inference(resolution,[status(thm)],[c_42,c_157])).

tff(c_338,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_zfmisc_1(k3_tarski(A_36))) = k5_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_329])).

tff(c_350,plain,(
    ! [A_36] : k5_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_338])).

tff(c_169,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_860,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_811])).

tff(c_876,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_860])).

tff(c_1087,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_876])).

tff(c_483,plain,(
    ! [A_79,B_80,C_81] : k5_xboole_0(k5_xboole_0(A_79,B_80),C_81) = k5_xboole_0(A_79,k5_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_517,plain,(
    ! [A_36,C_81] : k5_xboole_0(A_36,k5_xboole_0(A_36,C_81)) = k5_xboole_0(k1_xboole_0,C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_483])).

tff(c_2698,plain,(
    ! [A_152,C_153] : k5_xboole_0(A_152,k5_xboole_0(A_152,C_153)) = C_153 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_517])).

tff(c_6083,plain,(
    ! [A_205,B_206] : k5_xboole_0(A_205,k2_xboole_0(A_205,B_206)) = k4_xboole_0(B_206,A_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_2698])).

tff(c_2769,plain,(
    ! [A_154,B_155] : k5_xboole_0(A_154,k5_xboole_0(B_155,k5_xboole_0(A_154,B_155))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_483])).

tff(c_2697,plain,(
    ! [A_36,C_81] : k5_xboole_0(A_36,k5_xboole_0(A_36,C_81)) = C_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_517])).

tff(c_2777,plain,(
    ! [B_155,A_154] : k5_xboole_0(B_155,k5_xboole_0(A_154,B_155)) = k5_xboole_0(A_154,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2769,c_2697])).

tff(c_2854,plain,(
    ! [B_155,A_154] : k5_xboole_0(B_155,k5_xboole_0(A_154,B_155)) = A_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_2777])).

tff(c_6187,plain,(
    ! [A_207,B_208] : k5_xboole_0(k2_xboole_0(A_207,B_208),k4_xboole_0(B_208,A_207)) = A_207 ),
    inference(superposition,[status(thm),theory(equality)],[c_6083,c_2854])).

tff(c_6202,plain,(
    ! [B_208,A_207] : k5_xboole_0(k4_xboole_0(B_208,A_207),A_207) = k2_xboole_0(A_207,B_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_6187,c_2854])).

tff(c_656,plain,(
    ! [A_87,B_88,C_89] : k4_xboole_0(k3_xboole_0(A_87,B_88),C_89) = k3_xboole_0(A_87,k4_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1572,plain,(
    ! [B_126,C_127] : k3_xboole_0(B_126,k4_xboole_0(B_126,C_127)) = k4_xboole_0(B_126,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_656])).

tff(c_1591,plain,(
    ! [B_126,C_127] : k5_xboole_0(k4_xboole_0(B_126,C_127),k4_xboole_0(B_126,C_127)) = k4_xboole_0(k4_xboole_0(B_126,C_127),B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_1572,c_344])).

tff(c_1764,plain,(
    ! [B_130,C_131] : k4_xboole_0(k4_xboole_0(B_130,C_131),B_130) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_1591])).

tff(c_1778,plain,(
    ! [B_130,C_131] : k2_xboole_0(B_130,k4_xboole_0(B_130,C_131)) = k5_xboole_0(B_130,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1764,c_869])).

tff(c_1829,plain,(
    ! [B_130,C_131] : k2_xboole_0(B_130,k4_xboole_0(B_130,C_131)) = B_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_1778])).

tff(c_697,plain,(
    ! [B_4,C_89] : k3_xboole_0(B_4,k4_xboole_0(B_4,C_89)) = k4_xboole_0(B_4,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_656])).

tff(c_20,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1598,plain,(
    ! [B_126,C_127] : k5_xboole_0(B_126,k4_xboole_0(B_126,C_127)) = k4_xboole_0(B_126,k4_xboole_0(B_126,C_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1572,c_14])).

tff(c_3809,plain,(
    ! [B_172,C_173] : k5_xboole_0(B_172,k4_xboole_0(B_172,C_173)) = k3_xboole_0(B_172,C_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1598])).

tff(c_26,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k3_xboole_0(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3835,plain,(
    ! [B_172,C_173] : k5_xboole_0(k3_xboole_0(B_172,C_173),k3_xboole_0(B_172,k4_xboole_0(B_172,C_173))) = k2_xboole_0(B_172,k4_xboole_0(B_172,C_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3809,c_26])).

tff(c_5909,plain,(
    ! [B_203,C_204] : k5_xboole_0(k3_xboole_0(B_203,C_204),k4_xboole_0(B_203,C_204)) = B_203 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1829,c_697,c_3835])).

tff(c_6335,plain,(
    ! [A_209,B_210] : k5_xboole_0(k3_xboole_0(A_209,B_210),k4_xboole_0(B_210,A_209)) = B_210 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5909])).

tff(c_13901,plain,(
    ! [A_289,B_290] : k5_xboole_0(k3_xboole_0(A_289,B_290),B_290) = k4_xboole_0(B_290,A_289) ),
    inference(superposition,[status(thm),theory(equality)],[c_6335,c_2697])).

tff(c_524,plain,(
    ! [A_7,B_8,C_81] : k5_xboole_0(A_7,k5_xboole_0(k3_xboole_0(A_7,B_8),C_81)) = k5_xboole_0(k4_xboole_0(A_7,B_8),C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_483])).

tff(c_13918,plain,(
    ! [A_289,B_290] : k5_xboole_0(k4_xboole_0(A_289,B_290),B_290) = k5_xboole_0(A_289,k4_xboole_0(B_290,A_289)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13901,c_524])).

tff(c_14049,plain,(
    ! [B_290,A_289] : k2_xboole_0(B_290,A_289) = k2_xboole_0(A_289,B_290) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6202,c_869,c_13918])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1907,plain,(
    ! [A_134,B_135] : k4_xboole_0(k3_xboole_0(A_134,B_135),A_134) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1764])).

tff(c_1952,plain,(
    ! [C_16,B_15] : k3_xboole_0(C_16,k4_xboole_0(B_15,C_16)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1907])).

tff(c_5223,plain,(
    ! [A_192,B_193] : k5_xboole_0(k5_xboole_0(A_192,B_193),k3_xboole_0(B_193,A_192)) = k2_xboole_0(A_192,B_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_811])).

tff(c_5335,plain,(
    ! [A_96,B_97] : k5_xboole_0(k2_xboole_0(A_96,B_97),k3_xboole_0(k4_xboole_0(B_97,A_96),A_96)) = k2_xboole_0(A_96,k4_xboole_0(B_97,A_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_5223])).

tff(c_5401,plain,(
    ! [A_96,B_97] : k2_xboole_0(A_96,k4_xboole_0(B_97,A_96)) = k2_xboole_0(A_96,B_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_1952,c_2,c_5335])).

tff(c_44,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14085,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14049,c_44])).

tff(c_14086,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14049,c_5401,c_14085])).

tff(c_14302,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_14086])).

tff(c_14306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.91/2.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/2.95  
% 7.91/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/2.96  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.91/2.96  
% 7.91/2.96  %Foreground sorts:
% 7.91/2.96  
% 7.91/2.96  
% 7.91/2.96  %Background operators:
% 7.91/2.96  
% 7.91/2.96  
% 7.91/2.96  %Foreground operators:
% 7.91/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.91/2.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.91/2.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.91/2.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.91/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.91/2.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.91/2.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.91/2.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.91/2.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.91/2.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.91/2.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.91/2.96  tff('#skF_2', type, '#skF_2': $i).
% 7.91/2.96  tff('#skF_1', type, '#skF_1': $i).
% 7.91/2.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.91/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.91/2.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.91/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.91/2.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.91/2.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.91/2.96  
% 7.91/2.98  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 7.91/2.98  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.91/2.98  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.91/2.98  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.91/2.98  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.91/2.98  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.91/2.98  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.91/2.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.91/2.98  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 7.91/2.98  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.91/2.98  tff(f_69, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 7.91/2.98  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.91/2.98  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.91/2.98  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.91/2.98  tff(c_18, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.91/2.98  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.91/2.98  tff(c_120, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.91/2.98  tff(c_132, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_120])).
% 7.91/2.98  tff(c_302, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.91/2.98  tff(c_323, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_302])).
% 7.91/2.98  tff(c_352, plain, (![A_72]: (k3_xboole_0(A_72, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_323])).
% 7.91/2.98  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.91/2.98  tff(c_357, plain, (![A_72]: (k5_xboole_0(A_72, k1_xboole_0)=k4_xboole_0(A_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_352, c_14])).
% 7.91/2.98  tff(c_383, plain, (![A_72]: (k5_xboole_0(A_72, k1_xboole_0)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_357])).
% 7.91/2.98  tff(c_170, plain, (![A_55, B_56]: (r1_tarski(k1_tarski(A_55), B_56) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.91/2.98  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.91/2.98  tff(c_181, plain, (![A_55, B_56]: (k4_xboole_0(k1_tarski(A_55), B_56)=k1_xboole_0 | ~r2_hidden(A_55, B_56))), inference(resolution, [status(thm)], [c_170, c_12])).
% 7.91/2.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.91/2.98  tff(c_329, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.91/2.98  tff(c_344, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_329])).
% 7.91/2.98  tff(c_811, plain, (![A_96, B_97]: (k5_xboole_0(k5_xboole_0(A_96, B_97), k3_xboole_0(A_96, B_97))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.91/2.98  tff(c_24, plain, (![A_17, B_18, C_19]: (k5_xboole_0(k5_xboole_0(A_17, B_18), C_19)=k5_xboole_0(A_17, k5_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.91/2.98  tff(c_823, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k5_xboole_0(B_97, k3_xboole_0(A_96, B_97)))=k2_xboole_0(A_96, B_97))), inference(superposition, [status(thm), theory('equality')], [c_811, c_24])).
% 7.91/2.98  tff(c_1034, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k4_xboole_0(B_107, A_106))=k2_xboole_0(A_106, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_823])).
% 7.91/2.98  tff(c_1057, plain, (![B_56, A_55]: (k2_xboole_0(B_56, k1_tarski(A_55))=k5_xboole_0(B_56, k1_xboole_0) | ~r2_hidden(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_181, c_1034])).
% 7.91/2.98  tff(c_1083, plain, (![B_56, A_55]: (k2_xboole_0(B_56, k1_tarski(A_55))=B_56 | ~r2_hidden(A_55, B_56))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_1057])).
% 7.91/2.98  tff(c_869, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k4_xboole_0(B_97, A_96))=k2_xboole_0(A_96, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_823])).
% 7.91/2.98  tff(c_1076, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1034])).
% 7.91/2.98  tff(c_1086, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_383, c_1076])).
% 7.91/2.98  tff(c_42, plain, (![A_36]: (r1_tarski(A_36, k1_zfmisc_1(k3_tarski(A_36))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.91/2.98  tff(c_131, plain, (![A_36]: (k4_xboole_0(A_36, k1_zfmisc_1(k3_tarski(A_36)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_120])).
% 7.91/2.98  tff(c_157, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.91/2.98  tff(c_168, plain, (![A_36]: (k3_xboole_0(A_36, k1_zfmisc_1(k3_tarski(A_36)))=A_36)), inference(resolution, [status(thm)], [c_42, c_157])).
% 7.91/2.98  tff(c_338, plain, (![A_36]: (k4_xboole_0(A_36, k1_zfmisc_1(k3_tarski(A_36)))=k5_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_168, c_329])).
% 7.91/2.98  tff(c_350, plain, (![A_36]: (k5_xboole_0(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_338])).
% 7.91/2.98  tff(c_169, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_157])).
% 7.91/2.98  tff(c_860, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_169, c_811])).
% 7.91/2.98  tff(c_876, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_860])).
% 7.91/2.98  tff(c_1087, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_876])).
% 7.91/2.98  tff(c_483, plain, (![A_79, B_80, C_81]: (k5_xboole_0(k5_xboole_0(A_79, B_80), C_81)=k5_xboole_0(A_79, k5_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.91/2.98  tff(c_517, plain, (![A_36, C_81]: (k5_xboole_0(A_36, k5_xboole_0(A_36, C_81))=k5_xboole_0(k1_xboole_0, C_81))), inference(superposition, [status(thm), theory('equality')], [c_350, c_483])).
% 7.91/2.98  tff(c_2698, plain, (![A_152, C_153]: (k5_xboole_0(A_152, k5_xboole_0(A_152, C_153))=C_153)), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_517])).
% 7.91/2.98  tff(c_6083, plain, (![A_205, B_206]: (k5_xboole_0(A_205, k2_xboole_0(A_205, B_206))=k4_xboole_0(B_206, A_205))), inference(superposition, [status(thm), theory('equality')], [c_869, c_2698])).
% 7.91/2.98  tff(c_2769, plain, (![A_154, B_155]: (k5_xboole_0(A_154, k5_xboole_0(B_155, k5_xboole_0(A_154, B_155)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_350, c_483])).
% 7.91/2.98  tff(c_2697, plain, (![A_36, C_81]: (k5_xboole_0(A_36, k5_xboole_0(A_36, C_81))=C_81)), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_517])).
% 7.91/2.98  tff(c_2777, plain, (![B_155, A_154]: (k5_xboole_0(B_155, k5_xboole_0(A_154, B_155))=k5_xboole_0(A_154, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2769, c_2697])).
% 7.91/2.98  tff(c_2854, plain, (![B_155, A_154]: (k5_xboole_0(B_155, k5_xboole_0(A_154, B_155))=A_154)), inference(demodulation, [status(thm), theory('equality')], [c_383, c_2777])).
% 7.91/2.98  tff(c_6187, plain, (![A_207, B_208]: (k5_xboole_0(k2_xboole_0(A_207, B_208), k4_xboole_0(B_208, A_207))=A_207)), inference(superposition, [status(thm), theory('equality')], [c_6083, c_2854])).
% 7.91/2.98  tff(c_6202, plain, (![B_208, A_207]: (k5_xboole_0(k4_xboole_0(B_208, A_207), A_207)=k2_xboole_0(A_207, B_208))), inference(superposition, [status(thm), theory('equality')], [c_6187, c_2854])).
% 7.91/2.98  tff(c_656, plain, (![A_87, B_88, C_89]: (k4_xboole_0(k3_xboole_0(A_87, B_88), C_89)=k3_xboole_0(A_87, k4_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.91/2.98  tff(c_1572, plain, (![B_126, C_127]: (k3_xboole_0(B_126, k4_xboole_0(B_126, C_127))=k4_xboole_0(B_126, C_127))), inference(superposition, [status(thm), theory('equality')], [c_169, c_656])).
% 7.91/2.98  tff(c_1591, plain, (![B_126, C_127]: (k5_xboole_0(k4_xboole_0(B_126, C_127), k4_xboole_0(B_126, C_127))=k4_xboole_0(k4_xboole_0(B_126, C_127), B_126))), inference(superposition, [status(thm), theory('equality')], [c_1572, c_344])).
% 7.91/2.98  tff(c_1764, plain, (![B_130, C_131]: (k4_xboole_0(k4_xboole_0(B_130, C_131), B_130)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_350, c_1591])).
% 7.91/2.98  tff(c_1778, plain, (![B_130, C_131]: (k2_xboole_0(B_130, k4_xboole_0(B_130, C_131))=k5_xboole_0(B_130, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1764, c_869])).
% 7.91/2.98  tff(c_1829, plain, (![B_130, C_131]: (k2_xboole_0(B_130, k4_xboole_0(B_130, C_131))=B_130)), inference(demodulation, [status(thm), theory('equality')], [c_383, c_1778])).
% 7.91/2.98  tff(c_697, plain, (![B_4, C_89]: (k3_xboole_0(B_4, k4_xboole_0(B_4, C_89))=k4_xboole_0(B_4, C_89))), inference(superposition, [status(thm), theory('equality')], [c_169, c_656])).
% 7.91/2.98  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.91/2.98  tff(c_1598, plain, (![B_126, C_127]: (k5_xboole_0(B_126, k4_xboole_0(B_126, C_127))=k4_xboole_0(B_126, k4_xboole_0(B_126, C_127)))), inference(superposition, [status(thm), theory('equality')], [c_1572, c_14])).
% 7.91/2.98  tff(c_3809, plain, (![B_172, C_173]: (k5_xboole_0(B_172, k4_xboole_0(B_172, C_173))=k3_xboole_0(B_172, C_173))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1598])).
% 7.91/2.98  tff(c_26, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k3_xboole_0(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.91/2.98  tff(c_3835, plain, (![B_172, C_173]: (k5_xboole_0(k3_xboole_0(B_172, C_173), k3_xboole_0(B_172, k4_xboole_0(B_172, C_173)))=k2_xboole_0(B_172, k4_xboole_0(B_172, C_173)))), inference(superposition, [status(thm), theory('equality')], [c_3809, c_26])).
% 7.91/2.98  tff(c_5909, plain, (![B_203, C_204]: (k5_xboole_0(k3_xboole_0(B_203, C_204), k4_xboole_0(B_203, C_204))=B_203)), inference(demodulation, [status(thm), theory('equality')], [c_1829, c_697, c_3835])).
% 7.91/2.98  tff(c_6335, plain, (![A_209, B_210]: (k5_xboole_0(k3_xboole_0(A_209, B_210), k4_xboole_0(B_210, A_209))=B_210)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5909])).
% 7.91/2.98  tff(c_13901, plain, (![A_289, B_290]: (k5_xboole_0(k3_xboole_0(A_289, B_290), B_290)=k4_xboole_0(B_290, A_289))), inference(superposition, [status(thm), theory('equality')], [c_6335, c_2697])).
% 7.91/2.98  tff(c_524, plain, (![A_7, B_8, C_81]: (k5_xboole_0(A_7, k5_xboole_0(k3_xboole_0(A_7, B_8), C_81))=k5_xboole_0(k4_xboole_0(A_7, B_8), C_81))), inference(superposition, [status(thm), theory('equality')], [c_14, c_483])).
% 7.91/2.98  tff(c_13918, plain, (![A_289, B_290]: (k5_xboole_0(k4_xboole_0(A_289, B_290), B_290)=k5_xboole_0(A_289, k4_xboole_0(B_290, A_289)))), inference(superposition, [status(thm), theory('equality')], [c_13901, c_524])).
% 7.91/2.98  tff(c_14049, plain, (![B_290, A_289]: (k2_xboole_0(B_290, A_289)=k2_xboole_0(A_289, B_290))), inference(demodulation, [status(thm), theory('equality')], [c_6202, c_869, c_13918])).
% 7.91/2.98  tff(c_22, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.91/2.98  tff(c_1907, plain, (![A_134, B_135]: (k4_xboole_0(k3_xboole_0(A_134, B_135), A_134)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_1764])).
% 7.91/2.98  tff(c_1952, plain, (![C_16, B_15]: (k3_xboole_0(C_16, k4_xboole_0(B_15, C_16))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_1907])).
% 7.91/2.98  tff(c_5223, plain, (![A_192, B_193]: (k5_xboole_0(k5_xboole_0(A_192, B_193), k3_xboole_0(B_193, A_192))=k2_xboole_0(A_192, B_193))), inference(superposition, [status(thm), theory('equality')], [c_2, c_811])).
% 7.91/2.98  tff(c_5335, plain, (![A_96, B_97]: (k5_xboole_0(k2_xboole_0(A_96, B_97), k3_xboole_0(k4_xboole_0(B_97, A_96), A_96))=k2_xboole_0(A_96, k4_xboole_0(B_97, A_96)))), inference(superposition, [status(thm), theory('equality')], [c_869, c_5223])).
% 7.91/2.98  tff(c_5401, plain, (![A_96, B_97]: (k2_xboole_0(A_96, k4_xboole_0(B_97, A_96))=k2_xboole_0(A_96, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_1952, c_2, c_5335])).
% 7.91/2.98  tff(c_44, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.91/2.98  tff(c_14085, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14049, c_44])).
% 7.91/2.98  tff(c_14086, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14049, c_5401, c_14085])).
% 7.91/2.98  tff(c_14302, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1083, c_14086])).
% 7.91/2.98  tff(c_14306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_14302])).
% 7.91/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/2.98  
% 7.91/2.98  Inference rules
% 7.91/2.98  ----------------------
% 7.91/2.98  #Ref     : 0
% 7.91/2.98  #Sup     : 3554
% 7.91/2.98  #Fact    : 0
% 7.91/2.98  #Define  : 0
% 7.91/2.98  #Split   : 1
% 7.91/2.98  #Chain   : 0
% 7.91/2.98  #Close   : 0
% 7.91/2.98  
% 7.91/2.98  Ordering : KBO
% 7.91/2.98  
% 7.91/2.98  Simplification rules
% 7.91/2.98  ----------------------
% 7.91/2.98  #Subsume      : 72
% 7.91/2.98  #Demod        : 4144
% 7.91/2.98  #Tautology    : 2387
% 7.91/2.98  #SimpNegUnit  : 0
% 7.91/2.98  #BackRed      : 12
% 7.91/2.98  
% 7.91/2.98  #Partial instantiations: 0
% 7.91/2.98  #Strategies tried      : 1
% 7.91/2.98  
% 7.91/2.98  Timing (in seconds)
% 7.91/2.98  ----------------------
% 7.91/2.98  Preprocessing        : 0.33
% 7.91/2.98  Parsing              : 0.17
% 7.91/2.98  CNF conversion       : 0.02
% 7.91/2.98  Main loop            : 1.88
% 7.91/2.98  Inferencing          : 0.47
% 7.91/2.98  Reduction            : 0.97
% 7.91/2.98  Demodulation         : 0.84
% 7.91/2.98  BG Simplification    : 0.06
% 7.91/2.98  Subsumption          : 0.27
% 7.91/2.98  Abstraction          : 0.09
% 7.91/2.98  MUC search           : 0.00
% 7.91/2.98  Cooper               : 0.00
% 7.91/2.98  Total                : 2.25
% 7.91/2.98  Index Insertion      : 0.00
% 7.91/2.98  Index Deletion       : 0.00
% 7.91/2.98  Index Matching       : 0.00
% 7.91/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
