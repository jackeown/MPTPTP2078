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
% DateTime   : Thu Dec  3 09:54:36 EST 2020

% Result     : Theorem 9.94s
% Output     : CNFRefutation 10.18s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 367 expanded)
%              Number of leaves         :   34 ( 137 expanded)
%              Depth                    :   14
%              Number of atoms          :  104 ( 464 expanded)
%              Number of equality atoms :   75 ( 306 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_52,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2071,plain,(
    ! [A_143,B_144,C_145] :
      ( r1_tarski(k2_tarski(A_143,B_144),C_145)
      | ~ r2_hidden(B_144,C_145)
      | ~ r2_hidden(A_143,C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9350,plain,(
    ! [A_257,C_258] :
      ( r1_tarski(k1_tarski(A_257),C_258)
      | ~ r2_hidden(A_257,C_258)
      | ~ r2_hidden(A_257,C_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2071])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9378,plain,(
    ! [A_257,C_258] :
      ( k4_xboole_0(k1_tarski(A_257),C_258) = k1_xboole_0
      | ~ r2_hidden(A_257,C_258) ) ),
    inference(resolution,[status(thm)],[c_9350,c_12])).

tff(c_1119,plain,(
    ! [A_115,B_116,C_117] : k5_xboole_0(k5_xboole_0(A_115,B_116),C_117) = k5_xboole_0(A_115,k5_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_207,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_218,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_108,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_713,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_728,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_713])).

tff(c_739,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_728])).

tff(c_1133,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k5_xboole_0(B_116,k5_xboole_0(A_115,B_116))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_739])).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130,plain,(
    ! [A_53] : k3_xboole_0(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_108])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [A_53] : k3_xboole_0(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_2])).

tff(c_1828,plain,(
    ! [A_132,B_133] : k5_xboole_0(k5_xboole_0(A_132,B_133),k3_xboole_0(A_132,B_133)) = k2_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1904,plain,(
    ! [A_21] : k5_xboole_0(A_21,k3_xboole_0(A_21,k1_xboole_0)) = k2_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1828])).

tff(c_1918,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_139,c_1904])).

tff(c_600,plain,(
    ! [A_86,B_87] : k2_xboole_0(A_86,k4_xboole_0(B_87,A_86)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_624,plain,(
    ! [B_4] : k2_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_600])).

tff(c_1920,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_624])).

tff(c_1895,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1828])).

tff(c_1917,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_1895])).

tff(c_1970,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_1917])).

tff(c_1157,plain,(
    ! [B_4,C_117] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_117)) = k5_xboole_0(k1_xboole_0,C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_1119])).

tff(c_4012,plain,(
    ! [B_188,C_189] : k5_xboole_0(B_188,k5_xboole_0(B_188,C_189)) = C_189 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1970,c_1157])).

tff(c_4055,plain,(
    ! [B_116,A_115] : k5_xboole_0(B_116,k5_xboole_0(A_115,B_116)) = k5_xboole_0(A_115,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_4012])).

tff(c_4105,plain,(
    ! [B_116,A_115] : k5_xboole_0(B_116,k5_xboole_0(A_115,B_116)) = A_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4055])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_217,plain,(
    ! [A_12,B_13] : k4_xboole_0(k4_xboole_0(A_12,B_13),A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_207])).

tff(c_731,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_713])).

tff(c_1868,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k5_xboole_0(B_23,k3_xboole_0(A_22,B_23))) = k2_xboole_0(A_22,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1828])).

tff(c_2099,plain,(
    ! [A_146,B_147] : k5_xboole_0(A_146,k4_xboole_0(B_147,A_146)) = k2_xboole_0(A_146,B_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_1868])).

tff(c_2148,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_2099])).

tff(c_2163,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2148])).

tff(c_844,plain,(
    ! [A_104,B_105] : k3_xboole_0(k4_xboole_0(A_104,B_105),A_104) = k4_xboole_0(A_104,B_105) ),
    inference(resolution,[status(thm)],[c_20,c_108])).

tff(c_875,plain,(
    ! [A_104,B_105] : k3_xboole_0(A_104,k4_xboole_0(A_104,B_105)) = k4_xboole_0(A_104,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_2])).

tff(c_24,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_850,plain,(
    ! [A_104,B_105] : k5_xboole_0(A_104,k4_xboole_0(A_104,B_105)) = k4_xboole_0(A_104,k4_xboole_0(A_104,B_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_731])).

tff(c_2709,plain,(
    ! [A_163,B_164] : k5_xboole_0(A_163,k4_xboole_0(A_163,B_164)) = k3_xboole_0(A_163,B_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_850])).

tff(c_32,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2723,plain,(
    ! [A_163,B_164] : k5_xboole_0(k3_xboole_0(A_163,B_164),k3_xboole_0(A_163,k4_xboole_0(A_163,B_164))) = k2_xboole_0(A_163,k4_xboole_0(A_163,B_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_32])).

tff(c_2779,plain,(
    ! [A_163,B_164] : k5_xboole_0(k3_xboole_0(A_163,B_164),k4_xboole_0(A_163,B_164)) = A_163 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2163,c_875,c_2723])).

tff(c_22172,plain,(
    ! [A_385,B_386,C_387] : k5_xboole_0(k5_xboole_0(A_385,B_386),k5_xboole_0(k3_xboole_0(A_385,B_386),C_387)) = k5_xboole_0(k2_xboole_0(A_385,B_386),C_387) ),
    inference(superposition,[status(thm),theory(equality)],[c_1828,c_30])).

tff(c_22382,plain,(
    ! [A_163,B_164] : k5_xboole_0(k2_xboole_0(A_163,B_164),k4_xboole_0(A_163,B_164)) = k5_xboole_0(k5_xboole_0(A_163,B_164),A_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_2779,c_22172])).

tff(c_23054,plain,(
    ! [A_391,B_392] : k5_xboole_0(k2_xboole_0(A_391,B_392),k4_xboole_0(A_391,B_392)) = B_392 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4105,c_30,c_22382])).

tff(c_23156,plain,(
    ! [A_257,C_258] :
      ( k5_xboole_0(k2_xboole_0(k1_tarski(A_257),C_258),k1_xboole_0) = C_258
      | ~ r2_hidden(A_257,C_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9378,c_23054])).

tff(c_23247,plain,(
    ! [A_257,C_258] :
      ( k2_xboole_0(k1_tarski(A_257),C_258) = C_258
      | ~ r2_hidden(A_257,C_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_23156])).

tff(c_1912,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_1868])).

tff(c_4116,plain,(
    ! [B_190,A_191] : k5_xboole_0(B_190,k5_xboole_0(A_191,B_190)) = A_191 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4055])).

tff(c_4011,plain,(
    ! [B_4,C_117] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_117)) = C_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1970,c_1157])).

tff(c_4125,plain,(
    ! [B_190,A_191] : k5_xboole_0(B_190,A_191) = k5_xboole_0(A_191,B_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_4116,c_4011])).

tff(c_1308,plain,(
    ! [A_121,B_122,C_123] : k4_xboole_0(k3_xboole_0(A_121,B_122),C_123) = k3_xboole_0(A_121,k4_xboole_0(B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_324,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_431,plain,(
    ! [A_74,B_75] : r1_tarski(k3_xboole_0(A_74,B_75),A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_20])).

tff(c_453,plain,(
    ! [A_74,B_75] : k4_xboole_0(k3_xboole_0(A_74,B_75),A_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_431,c_12])).

tff(c_1331,plain,(
    ! [C_123,B_122] : k3_xboole_0(C_123,k4_xboole_0(B_122,C_123)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_453])).

tff(c_7367,plain,(
    ! [B_236,A_237] : k5_xboole_0(k5_xboole_0(B_236,A_237),k3_xboole_0(A_237,B_236)) = k2_xboole_0(B_236,A_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1828])).

tff(c_7495,plain,(
    ! [B_122,C_123] : k5_xboole_0(k5_xboole_0(k4_xboole_0(B_122,C_123),C_123),k1_xboole_0) = k2_xboole_0(k4_xboole_0(B_122,C_123),C_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_7367])).

tff(c_7563,plain,(
    ! [B_122,C_123] : k2_xboole_0(k4_xboole_0(B_122,C_123),C_123) = k2_xboole_0(C_123,B_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1912,c_28,c_4125,c_7495])).

tff(c_50,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_25024,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7563,c_50])).

tff(c_25187,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23247,c_25024])).

tff(c_25191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_25187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:06:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.94/4.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.94/4.18  
% 9.94/4.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.94/4.19  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 9.94/4.19  
% 9.94/4.19  %Foreground sorts:
% 9.94/4.19  
% 9.94/4.19  
% 9.94/4.19  %Background operators:
% 9.94/4.19  
% 9.94/4.19  
% 9.94/4.19  %Foreground operators:
% 9.94/4.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.94/4.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.94/4.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.94/4.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.94/4.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.94/4.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.94/4.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.94/4.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.94/4.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.94/4.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.94/4.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.94/4.19  tff('#skF_2', type, '#skF_2': $i).
% 9.94/4.19  tff('#skF_1', type, '#skF_1': $i).
% 9.94/4.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.94/4.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.94/4.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.94/4.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.94/4.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.94/4.19  
% 10.10/4.21  tff(f_80, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 10.10/4.21  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.10/4.21  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.10/4.21  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.10/4.21  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.10/4.21  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.10/4.21  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.10/4.21  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.10/4.21  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.10/4.21  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.10/4.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.10/4.21  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 10.10/4.21  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.10/4.21  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.10/4.21  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.10/4.21  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 10.10/4.21  tff(c_52, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.10/4.21  tff(c_28, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.10/4.21  tff(c_34, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.10/4.21  tff(c_2071, plain, (![A_143, B_144, C_145]: (r1_tarski(k2_tarski(A_143, B_144), C_145) | ~r2_hidden(B_144, C_145) | ~r2_hidden(A_143, C_145))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.18/4.21  tff(c_9350, plain, (![A_257, C_258]: (r1_tarski(k1_tarski(A_257), C_258) | ~r2_hidden(A_257, C_258) | ~r2_hidden(A_257, C_258))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2071])).
% 10.18/4.21  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.18/4.21  tff(c_9378, plain, (![A_257, C_258]: (k4_xboole_0(k1_tarski(A_257), C_258)=k1_xboole_0 | ~r2_hidden(A_257, C_258))), inference(resolution, [status(thm)], [c_9350, c_12])).
% 10.18/4.21  tff(c_1119, plain, (![A_115, B_116, C_117]: (k5_xboole_0(k5_xboole_0(A_115, B_116), C_117)=k5_xboole_0(A_115, k5_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.18/4.21  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.18/4.21  tff(c_207, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.18/4.21  tff(c_218, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_207])).
% 10.18/4.21  tff(c_108, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.18/4.21  tff(c_119, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_108])).
% 10.18/4.21  tff(c_713, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.18/4.21  tff(c_728, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_119, c_713])).
% 10.18/4.21  tff(c_739, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_218, c_728])).
% 10.18/4.21  tff(c_1133, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k5_xboole_0(B_116, k5_xboole_0(A_115, B_116)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1119, c_739])).
% 10.18/4.21  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.18/4.21  tff(c_130, plain, (![A_53]: (k3_xboole_0(k1_xboole_0, A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_108])).
% 10.18/4.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.18/4.21  tff(c_139, plain, (![A_53]: (k3_xboole_0(A_53, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_2])).
% 10.18/4.21  tff(c_1828, plain, (![A_132, B_133]: (k5_xboole_0(k5_xboole_0(A_132, B_133), k3_xboole_0(A_132, B_133))=k2_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.18/4.21  tff(c_1904, plain, (![A_21]: (k5_xboole_0(A_21, k3_xboole_0(A_21, k1_xboole_0))=k2_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1828])).
% 10.18/4.21  tff(c_1918, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_139, c_1904])).
% 10.18/4.21  tff(c_600, plain, (![A_86, B_87]: (k2_xboole_0(A_86, k4_xboole_0(B_87, A_86))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.18/4.21  tff(c_624, plain, (![B_4]: (k2_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_218, c_600])).
% 10.18/4.21  tff(c_1920, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_624])).
% 10.18/4.21  tff(c_1895, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_119, c_1828])).
% 10.18/4.21  tff(c_1917, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_739, c_1895])).
% 10.18/4.21  tff(c_1970, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_1917])).
% 10.18/4.21  tff(c_1157, plain, (![B_4, C_117]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_117))=k5_xboole_0(k1_xboole_0, C_117))), inference(superposition, [status(thm), theory('equality')], [c_739, c_1119])).
% 10.18/4.21  tff(c_4012, plain, (![B_188, C_189]: (k5_xboole_0(B_188, k5_xboole_0(B_188, C_189))=C_189)), inference(demodulation, [status(thm), theory('equality')], [c_1970, c_1157])).
% 10.18/4.21  tff(c_4055, plain, (![B_116, A_115]: (k5_xboole_0(B_116, k5_xboole_0(A_115, B_116))=k5_xboole_0(A_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_4012])).
% 10.18/4.21  tff(c_4105, plain, (![B_116, A_115]: (k5_xboole_0(B_116, k5_xboole_0(A_115, B_116))=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4055])).
% 10.18/4.21  tff(c_30, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.18/4.21  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.18/4.21  tff(c_217, plain, (![A_12, B_13]: (k4_xboole_0(k4_xboole_0(A_12, B_13), A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_207])).
% 10.18/4.21  tff(c_731, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_713])).
% 10.18/4.21  tff(c_1868, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k5_xboole_0(B_23, k3_xboole_0(A_22, B_23)))=k2_xboole_0(A_22, B_23))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1828])).
% 10.18/4.21  tff(c_2099, plain, (![A_146, B_147]: (k5_xboole_0(A_146, k4_xboole_0(B_147, A_146))=k2_xboole_0(A_146, B_147))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_1868])).
% 10.18/4.21  tff(c_2148, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k5_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_217, c_2099])).
% 10.18/4.21  tff(c_2163, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(A_12, B_13))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2148])).
% 10.18/4.21  tff(c_844, plain, (![A_104, B_105]: (k3_xboole_0(k4_xboole_0(A_104, B_105), A_104)=k4_xboole_0(A_104, B_105))), inference(resolution, [status(thm)], [c_20, c_108])).
% 10.18/4.21  tff(c_875, plain, (![A_104, B_105]: (k3_xboole_0(A_104, k4_xboole_0(A_104, B_105))=k4_xboole_0(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_844, c_2])).
% 10.18/4.21  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.18/4.21  tff(c_850, plain, (![A_104, B_105]: (k5_xboole_0(A_104, k4_xboole_0(A_104, B_105))=k4_xboole_0(A_104, k4_xboole_0(A_104, B_105)))), inference(superposition, [status(thm), theory('equality')], [c_844, c_731])).
% 10.18/4.21  tff(c_2709, plain, (![A_163, B_164]: (k5_xboole_0(A_163, k4_xboole_0(A_163, B_164))=k3_xboole_0(A_163, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_850])).
% 10.18/4.21  tff(c_32, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.18/4.21  tff(c_2723, plain, (![A_163, B_164]: (k5_xboole_0(k3_xboole_0(A_163, B_164), k3_xboole_0(A_163, k4_xboole_0(A_163, B_164)))=k2_xboole_0(A_163, k4_xboole_0(A_163, B_164)))), inference(superposition, [status(thm), theory('equality')], [c_2709, c_32])).
% 10.18/4.21  tff(c_2779, plain, (![A_163, B_164]: (k5_xboole_0(k3_xboole_0(A_163, B_164), k4_xboole_0(A_163, B_164))=A_163)), inference(demodulation, [status(thm), theory('equality')], [c_2163, c_875, c_2723])).
% 10.18/4.21  tff(c_22172, plain, (![A_385, B_386, C_387]: (k5_xboole_0(k5_xboole_0(A_385, B_386), k5_xboole_0(k3_xboole_0(A_385, B_386), C_387))=k5_xboole_0(k2_xboole_0(A_385, B_386), C_387))), inference(superposition, [status(thm), theory('equality')], [c_1828, c_30])).
% 10.18/4.21  tff(c_22382, plain, (![A_163, B_164]: (k5_xboole_0(k2_xboole_0(A_163, B_164), k4_xboole_0(A_163, B_164))=k5_xboole_0(k5_xboole_0(A_163, B_164), A_163))), inference(superposition, [status(thm), theory('equality')], [c_2779, c_22172])).
% 10.18/4.21  tff(c_23054, plain, (![A_391, B_392]: (k5_xboole_0(k2_xboole_0(A_391, B_392), k4_xboole_0(A_391, B_392))=B_392)), inference(demodulation, [status(thm), theory('equality')], [c_4105, c_30, c_22382])).
% 10.18/4.21  tff(c_23156, plain, (![A_257, C_258]: (k5_xboole_0(k2_xboole_0(k1_tarski(A_257), C_258), k1_xboole_0)=C_258 | ~r2_hidden(A_257, C_258))), inference(superposition, [status(thm), theory('equality')], [c_9378, c_23054])).
% 10.18/4.21  tff(c_23247, plain, (![A_257, C_258]: (k2_xboole_0(k1_tarski(A_257), C_258)=C_258 | ~r2_hidden(A_257, C_258))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_23156])).
% 10.18/4.21  tff(c_1912, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_1868])).
% 10.18/4.21  tff(c_4116, plain, (![B_190, A_191]: (k5_xboole_0(B_190, k5_xboole_0(A_191, B_190))=A_191)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4055])).
% 10.18/4.21  tff(c_4011, plain, (![B_4, C_117]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_117))=C_117)), inference(demodulation, [status(thm), theory('equality')], [c_1970, c_1157])).
% 10.18/4.21  tff(c_4125, plain, (![B_190, A_191]: (k5_xboole_0(B_190, A_191)=k5_xboole_0(A_191, B_190))), inference(superposition, [status(thm), theory('equality')], [c_4116, c_4011])).
% 10.18/4.21  tff(c_1308, plain, (![A_121, B_122, C_123]: (k4_xboole_0(k3_xboole_0(A_121, B_122), C_123)=k3_xboole_0(A_121, k4_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.18/4.21  tff(c_324, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.18/4.21  tff(c_431, plain, (![A_74, B_75]: (r1_tarski(k3_xboole_0(A_74, B_75), A_74))), inference(superposition, [status(thm), theory('equality')], [c_324, c_20])).
% 10.18/4.21  tff(c_453, plain, (![A_74, B_75]: (k4_xboole_0(k3_xboole_0(A_74, B_75), A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_431, c_12])).
% 10.18/4.21  tff(c_1331, plain, (![C_123, B_122]: (k3_xboole_0(C_123, k4_xboole_0(B_122, C_123))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1308, c_453])).
% 10.18/4.21  tff(c_7367, plain, (![B_236, A_237]: (k5_xboole_0(k5_xboole_0(B_236, A_237), k3_xboole_0(A_237, B_236))=k2_xboole_0(B_236, A_237))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1828])).
% 10.18/4.21  tff(c_7495, plain, (![B_122, C_123]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(B_122, C_123), C_123), k1_xboole_0)=k2_xboole_0(k4_xboole_0(B_122, C_123), C_123))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_7367])).
% 10.18/4.21  tff(c_7563, plain, (![B_122, C_123]: (k2_xboole_0(k4_xboole_0(B_122, C_123), C_123)=k2_xboole_0(C_123, B_122))), inference(demodulation, [status(thm), theory('equality')], [c_1912, c_28, c_4125, c_7495])).
% 10.18/4.21  tff(c_50, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.18/4.21  tff(c_25024, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7563, c_50])).
% 10.18/4.21  tff(c_25187, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_23247, c_25024])).
% 10.18/4.21  tff(c_25191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_25187])).
% 10.18/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/4.21  
% 10.18/4.21  Inference rules
% 10.18/4.21  ----------------------
% 10.18/4.21  #Ref     : 0
% 10.18/4.21  #Sup     : 6237
% 10.18/4.21  #Fact    : 0
% 10.18/4.21  #Define  : 0
% 10.18/4.21  #Split   : 2
% 10.18/4.21  #Chain   : 0
% 10.18/4.21  #Close   : 0
% 10.18/4.21  
% 10.18/4.21  Ordering : KBO
% 10.18/4.21  
% 10.18/4.21  Simplification rules
% 10.18/4.21  ----------------------
% 10.18/4.21  #Subsume      : 178
% 10.18/4.21  #Demod        : 7610
% 10.18/4.21  #Tautology    : 4136
% 10.18/4.21  #SimpNegUnit  : 0
% 10.18/4.21  #BackRed      : 9
% 10.18/4.21  
% 10.18/4.21  #Partial instantiations: 0
% 10.18/4.21  #Strategies tried      : 1
% 10.18/4.21  
% 10.18/4.21  Timing (in seconds)
% 10.18/4.21  ----------------------
% 10.18/4.21  Preprocessing        : 0.31
% 10.18/4.21  Parsing              : 0.17
% 10.18/4.21  CNF conversion       : 0.02
% 10.18/4.21  Main loop            : 3.11
% 10.18/4.21  Inferencing          : 0.65
% 10.18/4.21  Reduction            : 1.76
% 10.18/4.21  Demodulation         : 1.57
% 10.18/4.21  BG Simplification    : 0.08
% 10.18/4.21  Subsumption          : 0.46
% 10.18/4.21  Abstraction          : 0.14
% 10.18/4.21  MUC search           : 0.00
% 10.18/4.21  Cooper               : 0.00
% 10.18/4.21  Total                : 3.46
% 10.18/4.21  Index Insertion      : 0.00
% 10.18/4.21  Index Deletion       : 0.00
% 10.18/4.21  Index Matching       : 0.00
% 10.18/4.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
