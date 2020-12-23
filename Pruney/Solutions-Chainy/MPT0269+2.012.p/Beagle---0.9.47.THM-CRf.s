%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:45 EST 2020

% Result     : Theorem 15.64s
% Output     : CNFRefutation 15.64s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 944 expanded)
%              Number of leaves         :   39 ( 331 expanded)
%              Depth                    :   21
%              Number of atoms          :  147 (1337 expanded)
%              Number of equality atoms :   96 ( 866 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_81,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_210,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_222,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_24,c_210])).

tff(c_86,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tarski(A_61),B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_300,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k1_xboole_0
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_310,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(k1_tarski(A_61),B_62) = k1_xboole_0
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_84,c_300])).

tff(c_90,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_716,plain,(
    ! [A_131,B_132] :
      ( k3_xboole_0(A_131,B_132) = A_131
      | k4_xboole_0(A_131,B_132) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_210])).

tff(c_741,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_716])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_390,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1455,plain,(
    ! [A_166,B_167] : k5_xboole_0(A_166,k3_xboole_0(B_167,A_166)) = k4_xboole_0(A_166,B_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_390])).

tff(c_1518,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_1455])).

tff(c_312,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_300])).

tff(c_405,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k4_xboole_0(B_9,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_390])).

tff(c_421,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_405])).

tff(c_762,plain,(
    ! [A_133,B_134,C_135] : k5_xboole_0(k5_xboole_0(A_133,B_134),C_135) = k5_xboole_0(A_133,k5_xboole_0(B_134,C_135)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2880,plain,(
    ! [B_195,C_196] : k5_xboole_0(B_195,k5_xboole_0(B_195,C_196)) = k5_xboole_0(k1_xboole_0,C_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_762])).

tff(c_2997,plain,(
    ! [B_9] : k5_xboole_0(k1_xboole_0,B_9) = k5_xboole_0(B_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_2880])).

tff(c_3029,plain,(
    ! [B_9] : k5_xboole_0(k1_xboole_0,B_9) = B_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2997])).

tff(c_798,plain,(
    ! [B_9,C_135] : k5_xboole_0(B_9,k5_xboole_0(B_9,C_135)) = k5_xboole_0(k1_xboole_0,C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_762])).

tff(c_3137,plain,(
    ! [B_198,C_199] : k5_xboole_0(B_198,k5_xboole_0(B_198,C_199)) = C_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3029,c_798])).

tff(c_3215,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k4_xboole_0(k1_tarski('#skF_4'),'#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_3137])).

tff(c_3530,plain,
    ( k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_3215])).

tff(c_3538,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3530])).

tff(c_3539,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3538])).

tff(c_68,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_282,plain,(
    ! [A_90,B_91] : k1_enumset1(A_90,A_90,B_91) = k2_tarski(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [E_32,B_27,C_28] : r2_hidden(E_32,k1_enumset1(E_32,B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_320,plain,(
    ! [A_95,B_96] : r2_hidden(A_95,k2_tarski(A_95,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_50])).

tff(c_323,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_320])).

tff(c_38,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k3_xboole_0(A_19,B_20),C_21) = k3_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_745,plain,(
    ! [C_21] : k3_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),C_21)) = k4_xboole_0('#skF_3',C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_38])).

tff(c_18,plain,(
    ! [A_5,C_7,B_6] :
      ( r2_hidden(A_5,C_7)
      | ~ r2_hidden(A_5,B_6)
      | r2_hidden(A_5,k5_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46828,plain,(
    ! [A_621] :
      ( r2_hidden(A_621,'#skF_3')
      | ~ r2_hidden(A_621,k1_tarski('#skF_4'))
      | r2_hidden(A_621,k4_xboole_0(k1_tarski('#skF_4'),'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_18])).

tff(c_32,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3231,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3137])).

tff(c_855,plain,(
    ! [C_136] : k3_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),C_136)) = k4_xboole_0('#skF_3',C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_38])).

tff(c_870,plain,(
    ! [C_136] : k4_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),C_136)) = k5_xboole_0('#skF_3',k4_xboole_0('#skF_3',C_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_855,c_32])).

tff(c_11007,plain,(
    ! [C_136] : k4_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),C_136)) = k3_xboole_0('#skF_3',C_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3231,c_870])).

tff(c_11009,plain,(
    ! [C_340] : k4_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),C_340)) = k3_xboole_0('#skF_3',C_340) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3231,c_870])).

tff(c_628,plain,(
    ! [A_125,B_126,C_127] : k4_xboole_0(k3_xboole_0(A_125,B_126),C_127) = k3_xboole_0(A_125,k4_xboole_0(B_126,C_127)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1965,plain,(
    ! [B_178,C_179] : k3_xboole_0(B_178,k4_xboole_0(B_178,C_179)) = k4_xboole_0(B_178,C_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_628])).

tff(c_411,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_390])).

tff(c_1971,plain,(
    ! [B_178,C_179] : k5_xboole_0(k4_xboole_0(B_178,C_179),k4_xboole_0(B_178,C_179)) = k4_xboole_0(k4_xboole_0(B_178,C_179),B_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_1965,c_411])).

tff(c_2055,plain,(
    ! [B_180,C_181] : k4_xboole_0(k4_xboole_0(B_180,C_181),B_180) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_1971])).

tff(c_221,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_210])).

tff(c_2122,plain,(
    ! [B_180,C_181] : k3_xboole_0(k4_xboole_0(B_180,C_181),B_180) = k4_xboole_0(B_180,C_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_2055,c_221])).

tff(c_11051,plain,(
    ! [C_340] : k4_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),C_340)) = k3_xboole_0(k3_xboole_0('#skF_3',C_340),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11009,c_2122])).

tff(c_11136,plain,(
    ! [C_340] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_3',C_340)) = k3_xboole_0('#skF_3',C_340) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11007,c_2,c_11051])).

tff(c_11083,plain,(
    ! [C_340] :
      ( k3_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),C_340)) = '#skF_3'
      | k3_xboole_0('#skF_3',C_340) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11009,c_221])).

tff(c_15375,plain,(
    ! [C_378] :
      ( k4_xboole_0('#skF_3',C_378) = '#skF_3'
      | k3_xboole_0('#skF_3',C_378) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_11083])).

tff(c_2288,plain,(
    ! [A_188,B_189] : k3_xboole_0(A_188,k4_xboole_0(B_189,k3_xboole_0(A_188,B_189))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_312])).

tff(c_2319,plain,(
    ! [A_188,B_189] : k4_xboole_0(A_188,k4_xboole_0(B_189,k3_xboole_0(A_188,B_189))) = k5_xboole_0(A_188,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2288,c_32])).

tff(c_4586,plain,(
    ! [A_244,B_245] : k4_xboole_0(A_244,k4_xboole_0(B_245,k3_xboole_0(A_244,B_245))) = A_244 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2319])).

tff(c_4720,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(B_2,k3_xboole_0(B_2,A_1))) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4586])).

tff(c_15513,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,'#skF_3') = A_1
      | k3_xboole_0('#skF_3',k3_xboole_0('#skF_3',A_1)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15375,c_4720])).

tff(c_15689,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,'#skF_3') = A_1
      | k3_xboole_0('#skF_3',A_1) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11136,c_15513])).

tff(c_125,plain,(
    ! [B_76,A_77] : k3_xboole_0(B_76,A_77) = k3_xboole_0(A_77,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_141,plain,(
    ! [A_77] : k3_xboole_0(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_36])).

tff(c_2038,plain,(
    ! [B_178,C_179] : k4_xboole_0(k4_xboole_0(B_178,C_179),B_178) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_1971])).

tff(c_11155,plain,(
    ! [C_341] : k4_xboole_0(k3_xboole_0('#skF_3',C_341),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11009,c_2038])).

tff(c_11187,plain,(
    ! [C_341] : k4_xboole_0(k3_xboole_0('#skF_3',C_341),'#skF_3') = k3_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_341)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11155,c_2122])).

tff(c_11290,plain,(
    ! [C_342] : k3_xboole_0('#skF_3',k4_xboole_0(C_342,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_141,c_11187])).

tff(c_11371,plain,(
    ! [C_342] : k4_xboole_0('#skF_3',k4_xboole_0(C_342,'#skF_3')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11290,c_32])).

tff(c_11426,plain,(
    ! [C_342] : k4_xboole_0('#skF_3',k4_xboole_0(C_342,'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_11371])).

tff(c_417,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = k4_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_390])).

tff(c_423,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_417])).

tff(c_656,plain,(
    ! [B_9,C_127] : k3_xboole_0(B_9,k4_xboole_0(B_9,C_127)) = k4_xboole_0(B_9,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_628])).

tff(c_30,plain,(
    ! [A_12,B_13] : r1_xboole_0(k3_xboole_0(A_12,B_13),k5_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3982,plain,(
    ! [B_217,C_218] : r1_xboole_0(k3_xboole_0(B_217,k5_xboole_0(B_217,C_218)),C_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_3137,c_30])).

tff(c_4030,plain,(
    ! [A_14,B_15] : r1_xboole_0(k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)),k3_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3982])).

tff(c_4129,plain,(
    ! [A_227,B_228] : r1_xboole_0(k4_xboole_0(A_227,B_228),k3_xboole_0(A_227,B_228)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_4030])).

tff(c_9662,plain,(
    ! [C_316] : r1_xboole_0(k4_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),C_316)),k4_xboole_0('#skF_3',C_316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_4129])).

tff(c_9722,plain,(
    ! [B_62] :
      ( r1_xboole_0(k4_xboole_0('#skF_3',k1_xboole_0),k4_xboole_0('#skF_3',B_62))
      | ~ r2_hidden('#skF_4',B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_9662])).

tff(c_28346,plain,(
    ! [B_513] :
      ( r1_xboole_0('#skF_3',k4_xboole_0('#skF_3',B_513))
      | ~ r2_hidden('#skF_4',B_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_9722])).

tff(c_28378,plain,(
    ! [C_342] :
      ( r1_xboole_0('#skF_3','#skF_3')
      | ~ r2_hidden('#skF_4',k4_xboole_0(C_342,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11426,c_28346])).

tff(c_36962,plain,(
    ! [C_577] : ~ r2_hidden('#skF_4',k4_xboole_0(C_577,'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28378])).

tff(c_36972,plain,(
    ! [A_1] :
      ( ~ r2_hidden('#skF_4',A_1)
      | k3_xboole_0('#skF_3',A_1) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15689,c_36962])).

tff(c_46832,plain,
    ( k3_xboole_0('#skF_3',k4_xboole_0(k1_tarski('#skF_4'),'#skF_3')) != k1_xboole_0
    | r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46828,c_36972])).

tff(c_46892,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_312,c_745,c_46832])).

tff(c_46894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3539,c_46892])).

tff(c_46895,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28378])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46898,plain,(
    k3_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46895,c_4])).

tff(c_46900,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_46898])).

tff(c_46902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_46900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.64/7.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.64/7.70  
% 15.64/7.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.64/7.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 15.64/7.70  
% 15.64/7.70  %Foreground sorts:
% 15.64/7.70  
% 15.64/7.70  
% 15.64/7.70  %Background operators:
% 15.64/7.70  
% 15.64/7.70  
% 15.64/7.70  %Foreground operators:
% 15.64/7.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.64/7.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.64/7.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.64/7.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.64/7.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.64/7.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.64/7.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.64/7.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.64/7.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.64/7.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.64/7.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 15.64/7.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.64/7.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.64/7.70  tff('#skF_3', type, '#skF_3': $i).
% 15.64/7.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.64/7.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.64/7.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.64/7.70  tff('#skF_4', type, '#skF_4': $i).
% 15.64/7.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.64/7.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.64/7.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.64/7.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 15.64/7.70  
% 15.64/7.72  tff(f_107, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 15.64/7.72  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.64/7.72  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.64/7.72  tff(f_62, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 15.64/7.72  tff(f_97, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 15.64/7.72  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 15.64/7.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.64/7.72  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.64/7.72  tff(f_64, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 15.64/7.72  tff(f_81, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 15.64/7.72  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 15.64/7.72  tff(f_79, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 15.64/7.72  tff(f_60, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 15.64/7.72  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 15.64/7.72  tff(f_58, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 15.64/7.72  tff(f_50, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 15.64/7.72  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.64/7.72  tff(c_88, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.64/7.72  tff(c_24, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.64/7.72  tff(c_210, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.64/7.72  tff(c_222, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_24, c_210])).
% 15.64/7.72  tff(c_86, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.64/7.72  tff(c_40, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.64/7.72  tff(c_84, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_97])).
% 15.64/7.72  tff(c_300, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k1_xboole_0 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.64/7.72  tff(c_310, plain, (![A_61, B_62]: (k4_xboole_0(k1_tarski(A_61), B_62)=k1_xboole_0 | ~r2_hidden(A_61, B_62))), inference(resolution, [status(thm)], [c_84, c_300])).
% 15.64/7.72  tff(c_90, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.64/7.72  tff(c_26, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.64/7.72  tff(c_716, plain, (![A_131, B_132]: (k3_xboole_0(A_131, B_132)=A_131 | k4_xboole_0(A_131, B_132)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_210])).
% 15.64/7.72  tff(c_741, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_90, c_716])).
% 15.64/7.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.64/7.72  tff(c_390, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.64/7.72  tff(c_1455, plain, (![A_166, B_167]: (k5_xboole_0(A_166, k3_xboole_0(B_167, A_166))=k4_xboole_0(A_166, B_167))), inference(superposition, [status(thm), theory('equality')], [c_2, c_390])).
% 15.64/7.72  tff(c_1518, plain, (k5_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_741, c_1455])).
% 15.64/7.72  tff(c_312, plain, (![B_9]: (k4_xboole_0(B_9, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_300])).
% 15.64/7.72  tff(c_405, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k4_xboole_0(B_9, B_9))), inference(superposition, [status(thm), theory('equality')], [c_222, c_390])).
% 15.64/7.72  tff(c_421, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_405])).
% 15.64/7.72  tff(c_762, plain, (![A_133, B_134, C_135]: (k5_xboole_0(k5_xboole_0(A_133, B_134), C_135)=k5_xboole_0(A_133, k5_xboole_0(B_134, C_135)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.64/7.72  tff(c_2880, plain, (![B_195, C_196]: (k5_xboole_0(B_195, k5_xboole_0(B_195, C_196))=k5_xboole_0(k1_xboole_0, C_196))), inference(superposition, [status(thm), theory('equality')], [c_421, c_762])).
% 15.64/7.72  tff(c_2997, plain, (![B_9]: (k5_xboole_0(k1_xboole_0, B_9)=k5_xboole_0(B_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_421, c_2880])).
% 15.64/7.72  tff(c_3029, plain, (![B_9]: (k5_xboole_0(k1_xboole_0, B_9)=B_9)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2997])).
% 15.64/7.72  tff(c_798, plain, (![B_9, C_135]: (k5_xboole_0(B_9, k5_xboole_0(B_9, C_135))=k5_xboole_0(k1_xboole_0, C_135))), inference(superposition, [status(thm), theory('equality')], [c_421, c_762])).
% 15.64/7.72  tff(c_3137, plain, (![B_198, C_199]: (k5_xboole_0(B_198, k5_xboole_0(B_198, C_199))=C_199)), inference(demodulation, [status(thm), theory('equality')], [c_3029, c_798])).
% 15.64/7.72  tff(c_3215, plain, (k5_xboole_0(k1_tarski('#skF_4'), k4_xboole_0(k1_tarski('#skF_4'), '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1518, c_3137])).
% 15.64/7.72  tff(c_3530, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_310, c_3215])).
% 15.64/7.72  tff(c_3538, plain, (k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3530])).
% 15.64/7.72  tff(c_3539, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_86, c_3538])).
% 15.64/7.72  tff(c_68, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.64/7.72  tff(c_282, plain, (![A_90, B_91]: (k1_enumset1(A_90, A_90, B_91)=k2_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_83])).
% 15.64/7.72  tff(c_50, plain, (![E_32, B_27, C_28]: (r2_hidden(E_32, k1_enumset1(E_32, B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.64/7.72  tff(c_320, plain, (![A_95, B_96]: (r2_hidden(A_95, k2_tarski(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_50])).
% 15.64/7.72  tff(c_323, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_320])).
% 15.64/7.72  tff(c_38, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k3_xboole_0(A_19, B_20), C_21)=k3_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.64/7.72  tff(c_745, plain, (![C_21]: (k3_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), C_21))=k4_xboole_0('#skF_3', C_21))), inference(superposition, [status(thm), theory('equality')], [c_741, c_38])).
% 15.64/7.72  tff(c_18, plain, (![A_5, C_7, B_6]: (r2_hidden(A_5, C_7) | ~r2_hidden(A_5, B_6) | r2_hidden(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.64/7.72  tff(c_46828, plain, (![A_621]: (r2_hidden(A_621, '#skF_3') | ~r2_hidden(A_621, k1_tarski('#skF_4')) | r2_hidden(A_621, k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1518, c_18])).
% 15.64/7.72  tff(c_32, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.64/7.72  tff(c_3231, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3137])).
% 15.64/7.72  tff(c_855, plain, (![C_136]: (k3_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), C_136))=k4_xboole_0('#skF_3', C_136))), inference(superposition, [status(thm), theory('equality')], [c_741, c_38])).
% 15.64/7.72  tff(c_870, plain, (![C_136]: (k4_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), C_136))=k5_xboole_0('#skF_3', k4_xboole_0('#skF_3', C_136)))), inference(superposition, [status(thm), theory('equality')], [c_855, c_32])).
% 15.64/7.72  tff(c_11007, plain, (![C_136]: (k4_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), C_136))=k3_xboole_0('#skF_3', C_136))), inference(demodulation, [status(thm), theory('equality')], [c_3231, c_870])).
% 15.64/7.72  tff(c_11009, plain, (![C_340]: (k4_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), C_340))=k3_xboole_0('#skF_3', C_340))), inference(demodulation, [status(thm), theory('equality')], [c_3231, c_870])).
% 15.64/7.72  tff(c_628, plain, (![A_125, B_126, C_127]: (k4_xboole_0(k3_xboole_0(A_125, B_126), C_127)=k3_xboole_0(A_125, k4_xboole_0(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.64/7.72  tff(c_1965, plain, (![B_178, C_179]: (k3_xboole_0(B_178, k4_xboole_0(B_178, C_179))=k4_xboole_0(B_178, C_179))), inference(superposition, [status(thm), theory('equality')], [c_222, c_628])).
% 15.64/7.72  tff(c_411, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_390])).
% 15.64/7.72  tff(c_1971, plain, (![B_178, C_179]: (k5_xboole_0(k4_xboole_0(B_178, C_179), k4_xboole_0(B_178, C_179))=k4_xboole_0(k4_xboole_0(B_178, C_179), B_178))), inference(superposition, [status(thm), theory('equality')], [c_1965, c_411])).
% 15.64/7.72  tff(c_2055, plain, (![B_180, C_181]: (k4_xboole_0(k4_xboole_0(B_180, C_181), B_180)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_1971])).
% 15.64/7.72  tff(c_221, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_210])).
% 15.64/7.72  tff(c_2122, plain, (![B_180, C_181]: (k3_xboole_0(k4_xboole_0(B_180, C_181), B_180)=k4_xboole_0(B_180, C_181))), inference(superposition, [status(thm), theory('equality')], [c_2055, c_221])).
% 15.64/7.72  tff(c_11051, plain, (![C_340]: (k4_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), C_340))=k3_xboole_0(k3_xboole_0('#skF_3', C_340), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11009, c_2122])).
% 15.64/7.72  tff(c_11136, plain, (![C_340]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_3', C_340))=k3_xboole_0('#skF_3', C_340))), inference(demodulation, [status(thm), theory('equality')], [c_11007, c_2, c_11051])).
% 15.64/7.72  tff(c_11083, plain, (![C_340]: (k3_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), C_340))='#skF_3' | k3_xboole_0('#skF_3', C_340)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11009, c_221])).
% 15.64/7.72  tff(c_15375, plain, (![C_378]: (k4_xboole_0('#skF_3', C_378)='#skF_3' | k3_xboole_0('#skF_3', C_378)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_745, c_11083])).
% 15.64/7.72  tff(c_2288, plain, (![A_188, B_189]: (k3_xboole_0(A_188, k4_xboole_0(B_189, k3_xboole_0(A_188, B_189)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_628, c_312])).
% 15.64/7.72  tff(c_2319, plain, (![A_188, B_189]: (k4_xboole_0(A_188, k4_xboole_0(B_189, k3_xboole_0(A_188, B_189)))=k5_xboole_0(A_188, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2288, c_32])).
% 15.64/7.72  tff(c_4586, plain, (![A_244, B_245]: (k4_xboole_0(A_244, k4_xboole_0(B_245, k3_xboole_0(A_244, B_245)))=A_244)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2319])).
% 15.64/7.72  tff(c_4720, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(B_2, k3_xboole_0(B_2, A_1)))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4586])).
% 15.64/7.72  tff(c_15513, plain, (![A_1]: (k4_xboole_0(A_1, '#skF_3')=A_1 | k3_xboole_0('#skF_3', k3_xboole_0('#skF_3', A_1))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15375, c_4720])).
% 15.64/7.72  tff(c_15689, plain, (![A_1]: (k4_xboole_0(A_1, '#skF_3')=A_1 | k3_xboole_0('#skF_3', A_1)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11136, c_15513])).
% 15.64/7.72  tff(c_125, plain, (![B_76, A_77]: (k3_xboole_0(B_76, A_77)=k3_xboole_0(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.64/7.72  tff(c_36, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.64/7.72  tff(c_141, plain, (![A_77]: (k3_xboole_0(k1_xboole_0, A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_36])).
% 15.64/7.72  tff(c_2038, plain, (![B_178, C_179]: (k4_xboole_0(k4_xboole_0(B_178, C_179), B_178)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_1971])).
% 15.64/7.72  tff(c_11155, plain, (![C_341]: (k4_xboole_0(k3_xboole_0('#skF_3', C_341), '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11009, c_2038])).
% 15.64/7.72  tff(c_11187, plain, (![C_341]: (k4_xboole_0(k3_xboole_0('#skF_3', C_341), '#skF_3')=k3_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_341)))), inference(superposition, [status(thm), theory('equality')], [c_11155, c_2122])).
% 15.64/7.72  tff(c_11290, plain, (![C_342]: (k3_xboole_0('#skF_3', k4_xboole_0(C_342, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_141, c_11187])).
% 15.64/7.72  tff(c_11371, plain, (![C_342]: (k4_xboole_0('#skF_3', k4_xboole_0(C_342, '#skF_3'))=k5_xboole_0('#skF_3', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11290, c_32])).
% 15.64/7.72  tff(c_11426, plain, (![C_342]: (k4_xboole_0('#skF_3', k4_xboole_0(C_342, '#skF_3'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_11371])).
% 15.64/7.72  tff(c_417, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=k4_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_390])).
% 15.64/7.72  tff(c_423, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_417])).
% 15.64/7.72  tff(c_656, plain, (![B_9, C_127]: (k3_xboole_0(B_9, k4_xboole_0(B_9, C_127))=k4_xboole_0(B_9, C_127))), inference(superposition, [status(thm), theory('equality')], [c_222, c_628])).
% 15.64/7.72  tff(c_30, plain, (![A_12, B_13]: (r1_xboole_0(k3_xboole_0(A_12, B_13), k5_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.64/7.72  tff(c_3982, plain, (![B_217, C_218]: (r1_xboole_0(k3_xboole_0(B_217, k5_xboole_0(B_217, C_218)), C_218))), inference(superposition, [status(thm), theory('equality')], [c_3137, c_30])).
% 15.64/7.72  tff(c_4030, plain, (![A_14, B_15]: (r1_xboole_0(k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)), k3_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3982])).
% 15.64/7.72  tff(c_4129, plain, (![A_227, B_228]: (r1_xboole_0(k4_xboole_0(A_227, B_228), k3_xboole_0(A_227, B_228)))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_4030])).
% 15.64/7.72  tff(c_9662, plain, (![C_316]: (r1_xboole_0(k4_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), C_316)), k4_xboole_0('#skF_3', C_316)))), inference(superposition, [status(thm), theory('equality')], [c_745, c_4129])).
% 15.64/7.72  tff(c_9722, plain, (![B_62]: (r1_xboole_0(k4_xboole_0('#skF_3', k1_xboole_0), k4_xboole_0('#skF_3', B_62)) | ~r2_hidden('#skF_4', B_62))), inference(superposition, [status(thm), theory('equality')], [c_310, c_9662])).
% 15.64/7.72  tff(c_28346, plain, (![B_513]: (r1_xboole_0('#skF_3', k4_xboole_0('#skF_3', B_513)) | ~r2_hidden('#skF_4', B_513))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_9722])).
% 15.64/7.72  tff(c_28378, plain, (![C_342]: (r1_xboole_0('#skF_3', '#skF_3') | ~r2_hidden('#skF_4', k4_xboole_0(C_342, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_11426, c_28346])).
% 15.64/7.72  tff(c_36962, plain, (![C_577]: (~r2_hidden('#skF_4', k4_xboole_0(C_577, '#skF_3')))), inference(splitLeft, [status(thm)], [c_28378])).
% 15.64/7.72  tff(c_36972, plain, (![A_1]: (~r2_hidden('#skF_4', A_1) | k3_xboole_0('#skF_3', A_1)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15689, c_36962])).
% 15.64/7.72  tff(c_46832, plain, (k3_xboole_0('#skF_3', k4_xboole_0(k1_tarski('#skF_4'), '#skF_3'))!=k1_xboole_0 | r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_46828, c_36972])).
% 15.64/7.72  tff(c_46892, plain, (r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_312, c_745, c_46832])).
% 15.64/7.72  tff(c_46894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3539, c_46892])).
% 15.64/7.72  tff(c_46895, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_28378])).
% 15.64/7.72  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.64/7.72  tff(c_46898, plain, (k3_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_46895, c_4])).
% 15.64/7.72  tff(c_46900, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_46898])).
% 15.64/7.72  tff(c_46902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_46900])).
% 15.64/7.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.64/7.72  
% 15.64/7.72  Inference rules
% 15.64/7.72  ----------------------
% 15.64/7.72  #Ref     : 0
% 15.64/7.72  #Sup     : 11518
% 15.64/7.72  #Fact    : 8
% 15.64/7.72  #Define  : 0
% 15.64/7.72  #Split   : 2
% 15.64/7.72  #Chain   : 0
% 15.64/7.72  #Close   : 0
% 15.64/7.72  
% 15.64/7.72  Ordering : KBO
% 15.64/7.72  
% 15.64/7.72  Simplification rules
% 15.64/7.72  ----------------------
% 15.64/7.72  #Subsume      : 987
% 15.64/7.72  #Demod        : 16684
% 15.64/7.72  #Tautology    : 7153
% 15.64/7.72  #SimpNegUnit  : 397
% 15.64/7.72  #BackRed      : 28
% 15.64/7.72  
% 15.64/7.72  #Partial instantiations: 0
% 15.64/7.72  #Strategies tried      : 1
% 15.64/7.72  
% 15.64/7.72  Timing (in seconds)
% 15.64/7.72  ----------------------
% 15.64/7.72  Preprocessing        : 0.35
% 15.64/7.72  Parsing              : 0.18
% 15.64/7.72  CNF conversion       : 0.03
% 15.64/7.72  Main loop            : 6.61
% 15.64/7.72  Inferencing          : 0.96
% 15.64/7.73  Reduction            : 4.12
% 15.64/7.73  Demodulation         : 3.70
% 15.64/7.73  BG Simplification    : 0.12
% 15.64/7.73  Subsumption          : 1.11
% 15.64/7.73  Abstraction          : 0.20
% 15.64/7.73  MUC search           : 0.00
% 15.64/7.73  Cooper               : 0.00
% 15.64/7.73  Total                : 7.01
% 15.64/7.73  Index Insertion      : 0.00
% 15.64/7.73  Index Deletion       : 0.00
% 15.64/7.73  Index Matching       : 0.00
% 15.64/7.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
