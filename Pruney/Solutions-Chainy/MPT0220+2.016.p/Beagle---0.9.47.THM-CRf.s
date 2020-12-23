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
% DateTime   : Thu Dec  3 09:48:06 EST 2020

% Result     : Theorem 10.76s
% Output     : CNFRefutation 10.76s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 594 expanded)
%              Number of leaves         :   31 ( 214 expanded)
%              Depth                    :   18
%              Number of atoms          :   74 ( 606 expanded)
%              Number of equality atoms :   64 ( 551 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_192,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_204,plain,(
    ! [A_66] : k5_xboole_0(k1_xboole_0,A_66) = k2_xboole_0(k1_xboole_0,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_192])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_214,plain,(
    ! [A_66] : k5_xboole_0(A_66,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_4])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_289,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = k2_xboole_0(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_192])).

tff(c_674,plain,(
    ! [B_89] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_89)) = k4_xboole_0(k1_xboole_0,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_201])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_157,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_168,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(resolution,[status(thm)],[c_22,c_157])).

tff(c_807,plain,(
    ! [B_102] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_102)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_168])).

tff(c_296,plain,(
    ! [B_71] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_71)) = k4_xboole_0(k1_xboole_0,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_201])).

tff(c_814,plain,(
    ! [B_102] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_102)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_296])).

tff(c_886,plain,(
    ! [B_104] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_104)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_814])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_954,plain,(
    ! [B_105] : k3_xboole_0(k1_xboole_0,B_105) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_312,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_289])).

tff(c_962,plain,(
    ! [B_105] : k5_xboole_0(B_105,k1_xboole_0) = k4_xboole_0(B_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_312])).

tff(c_1004,plain,(
    ! [B_105] : k2_xboole_0(k1_xboole_0,B_105) = B_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_18,c_962])).

tff(c_1140,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_201])).

tff(c_26,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_510,plain,(
    ! [A_82,B_83,C_84] : k5_xboole_0(k5_xboole_0(A_82,B_83),C_84) = k5_xboole_0(A_82,k5_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1373,plain,(
    ! [B_122,A_123,B_124] : k5_xboole_0(B_122,k5_xboole_0(A_123,B_124)) = k5_xboole_0(A_123,k5_xboole_0(B_124,B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_510])).

tff(c_2416,plain,(
    ! [A_140,B_141] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_140,B_141)) = k5_xboole_0(B_141,A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_1373])).

tff(c_2530,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2416])).

tff(c_2565,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k2_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_2530])).

tff(c_2521,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_2416])).

tff(c_2563,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_2521])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4947,plain,(
    ! [A_196,B_197,C_198] : k5_xboole_0(A_196,k5_xboole_0(k3_xboole_0(A_196,B_197),C_198)) = k5_xboole_0(k4_xboole_0(A_196,B_197),C_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_510])).

tff(c_5020,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_4947])).

tff(c_5145,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_26,c_5020])).

tff(c_1001,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_954])).

tff(c_348,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_366,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_348])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_157])).

tff(c_309,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_289])).

tff(c_369,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k3_xboole_0(B_6,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_309])).

tff(c_1083,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_369])).

tff(c_40,plain,(
    ! [A_43,B_44] : r1_tarski(k1_tarski(A_43),k2_tarski(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_167,plain,(
    ! [A_43,B_44] : k3_xboole_0(k1_tarski(A_43),k2_tarski(A_43,B_44)) = k1_tarski(A_43) ),
    inference(resolution,[status(thm)],[c_40,c_157])).

tff(c_2527,plain,(
    ! [A_7,B_8] : k5_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2416])).

tff(c_2843,plain,(
    ! [A_150,B_151] : k5_xboole_0(k3_xboole_0(A_150,B_151),A_150) = k4_xboole_0(A_150,B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_2527])).

tff(c_2918,plain,(
    ! [A_43,B_44] : k5_xboole_0(k1_tarski(A_43),k1_tarski(A_43)) = k4_xboole_0(k1_tarski(A_43),k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_2843])).

tff(c_2950,plain,(
    ! [A_43,B_44] : k4_xboole_0(k1_tarski(A_43),k2_tarski(A_43,B_44)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_2918])).

tff(c_1139,plain,(
    ! [A_66] : k5_xboole_0(A_66,k1_xboole_0) = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_214])).

tff(c_5804,plain,(
    ! [A_209,B_210,C_211] : k5_xboole_0(A_209,k5_xboole_0(k4_xboole_0(B_210,A_209),C_211)) = k5_xboole_0(k2_xboole_0(A_209,B_210),C_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_510])).

tff(c_5964,plain,(
    ! [A_209,B_210] : k5_xboole_0(k2_xboole_0(A_209,B_210),k4_xboole_0(B_210,A_209)) = k5_xboole_0(A_209,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_5804])).

tff(c_6037,plain,(
    ! [A_212,B_213] : k5_xboole_0(k2_xboole_0(A_212,B_213),k4_xboole_0(B_213,A_212)) = A_212 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_5964])).

tff(c_6115,plain,(
    ! [A_43,B_44] : k5_xboole_0(k2_xboole_0(k2_tarski(A_43,B_44),k1_tarski(A_43)),k1_xboole_0) = k2_tarski(A_43,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_2950,c_6037])).

tff(c_6163,plain,(
    ! [A_43,B_44] : k2_xboole_0(k1_tarski(A_43),k2_tarski(A_43,B_44)) = k2_tarski(A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_4,c_5145,c_6115])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6163,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.76/4.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/4.61  
% 10.76/4.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/4.62  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 10.76/4.62  
% 10.76/4.62  %Foreground sorts:
% 10.76/4.62  
% 10.76/4.62  
% 10.76/4.62  %Background operators:
% 10.76/4.62  
% 10.76/4.62  
% 10.76/4.62  %Foreground operators:
% 10.76/4.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.76/4.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.76/4.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.76/4.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.76/4.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.76/4.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.76/4.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.76/4.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.76/4.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.76/4.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.76/4.62  tff('#skF_2', type, '#skF_2': $i).
% 10.76/4.62  tff('#skF_1', type, '#skF_1': $i).
% 10.76/4.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.76/4.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.76/4.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.76/4.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.76/4.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.76/4.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.76/4.62  
% 10.76/4.63  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.76/4.63  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.76/4.63  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.76/4.63  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.76/4.63  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.76/4.63  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.76/4.63  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.76/4.63  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.76/4.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.76/4.63  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.76/4.63  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.76/4.63  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 10.76/4.63  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 10.76/4.63  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.76/4.63  tff(c_192, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.76/4.63  tff(c_204, plain, (![A_66]: (k5_xboole_0(k1_xboole_0, A_66)=k2_xboole_0(k1_xboole_0, A_66))), inference(superposition, [status(thm), theory('equality')], [c_18, c_192])).
% 10.76/4.63  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.76/4.63  tff(c_214, plain, (![A_66]: (k5_xboole_0(A_66, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_66))), inference(superposition, [status(thm), theory('equality')], [c_204, c_4])).
% 10.76/4.63  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.76/4.63  tff(c_289, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.76/4.63  tff(c_201, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=k2_xboole_0(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_192])).
% 10.76/4.63  tff(c_674, plain, (![B_89]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_89))=k4_xboole_0(k1_xboole_0, B_89))), inference(superposition, [status(thm), theory('equality')], [c_289, c_201])).
% 10.76/4.63  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.76/4.63  tff(c_157, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.76/4.63  tff(c_168, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(resolution, [status(thm)], [c_22, c_157])).
% 10.76/4.63  tff(c_807, plain, (![B_102]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_102))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_674, c_168])).
% 10.76/4.63  tff(c_296, plain, (![B_71]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_71))=k4_xboole_0(k1_xboole_0, B_71))), inference(superposition, [status(thm), theory('equality')], [c_289, c_201])).
% 10.76/4.63  tff(c_814, plain, (![B_102]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_102))=k2_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_807, c_296])).
% 10.76/4.63  tff(c_886, plain, (![B_104]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_104))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_814])).
% 10.76/4.63  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.76/4.63  tff(c_954, plain, (![B_105]: (k3_xboole_0(k1_xboole_0, B_105)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_886, c_20])).
% 10.76/4.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.76/4.63  tff(c_312, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_289])).
% 10.76/4.63  tff(c_962, plain, (![B_105]: (k5_xboole_0(B_105, k1_xboole_0)=k4_xboole_0(B_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_954, c_312])).
% 10.76/4.63  tff(c_1004, plain, (![B_105]: (k2_xboole_0(k1_xboole_0, B_105)=B_105)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_18, c_962])).
% 10.76/4.63  tff(c_1140, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_201])).
% 10.76/4.63  tff(c_26, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.76/4.63  tff(c_510, plain, (![A_82, B_83, C_84]: (k5_xboole_0(k5_xboole_0(A_82, B_83), C_84)=k5_xboole_0(A_82, k5_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.76/4.63  tff(c_1373, plain, (![B_122, A_123, B_124]: (k5_xboole_0(B_122, k5_xboole_0(A_123, B_124))=k5_xboole_0(A_123, k5_xboole_0(B_124, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_510])).
% 10.76/4.63  tff(c_2416, plain, (![A_140, B_141]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_140, B_141))=k5_xboole_0(B_141, A_140))), inference(superposition, [status(thm), theory('equality')], [c_1140, c_1373])).
% 10.76/4.63  tff(c_2530, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2416])).
% 10.76/4.63  tff(c_2565, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k2_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_2530])).
% 10.76/4.63  tff(c_2521, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_312, c_2416])).
% 10.76/4.63  tff(c_2563, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_2521])).
% 10.76/4.63  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.76/4.63  tff(c_4947, plain, (![A_196, B_197, C_198]: (k5_xboole_0(A_196, k5_xboole_0(k3_xboole_0(A_196, B_197), C_198))=k5_xboole_0(k4_xboole_0(A_196, B_197), C_198))), inference(superposition, [status(thm), theory('equality')], [c_12, c_510])).
% 10.76/4.63  tff(c_5020, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2563, c_4947])).
% 10.76/4.63  tff(c_5145, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_26, c_5020])).
% 10.76/4.63  tff(c_1001, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_954])).
% 10.76/4.63  tff(c_348, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.76/4.63  tff(c_366, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_348])).
% 10.76/4.63  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.76/4.63  tff(c_169, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_157])).
% 10.76/4.63  tff(c_309, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_169, c_289])).
% 10.76/4.63  tff(c_369, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k3_xboole_0(B_6, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_309])).
% 10.76/4.63  tff(c_1083, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1001, c_369])).
% 10.76/4.63  tff(c_40, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), k2_tarski(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.76/4.63  tff(c_167, plain, (![A_43, B_44]: (k3_xboole_0(k1_tarski(A_43), k2_tarski(A_43, B_44))=k1_tarski(A_43))), inference(resolution, [status(thm)], [c_40, c_157])).
% 10.76/4.63  tff(c_2527, plain, (![A_7, B_8]: (k5_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2416])).
% 10.76/4.63  tff(c_2843, plain, (![A_150, B_151]: (k5_xboole_0(k3_xboole_0(A_150, B_151), A_150)=k4_xboole_0(A_150, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_2527])).
% 10.76/4.63  tff(c_2918, plain, (![A_43, B_44]: (k5_xboole_0(k1_tarski(A_43), k1_tarski(A_43))=k4_xboole_0(k1_tarski(A_43), k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_2843])).
% 10.76/4.63  tff(c_2950, plain, (![A_43, B_44]: (k4_xboole_0(k1_tarski(A_43), k2_tarski(A_43, B_44))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_2918])).
% 10.76/4.63  tff(c_1139, plain, (![A_66]: (k5_xboole_0(A_66, k1_xboole_0)=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_214])).
% 10.76/4.63  tff(c_5804, plain, (![A_209, B_210, C_211]: (k5_xboole_0(A_209, k5_xboole_0(k4_xboole_0(B_210, A_209), C_211))=k5_xboole_0(k2_xboole_0(A_209, B_210), C_211))), inference(superposition, [status(thm), theory('equality')], [c_26, c_510])).
% 10.76/4.63  tff(c_5964, plain, (![A_209, B_210]: (k5_xboole_0(k2_xboole_0(A_209, B_210), k4_xboole_0(B_210, A_209))=k5_xboole_0(A_209, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1083, c_5804])).
% 10.76/4.63  tff(c_6037, plain, (![A_212, B_213]: (k5_xboole_0(k2_xboole_0(A_212, B_213), k4_xboole_0(B_213, A_212))=A_212)), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_5964])).
% 10.76/4.63  tff(c_6115, plain, (![A_43, B_44]: (k5_xboole_0(k2_xboole_0(k2_tarski(A_43, B_44), k1_tarski(A_43)), k1_xboole_0)=k2_tarski(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_2950, c_6037])).
% 10.76/4.63  tff(c_6163, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), k2_tarski(A_43, B_44))=k2_tarski(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_4, c_5145, c_6115])).
% 10.76/4.63  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.76/4.63  tff(c_22738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6163, c_42])).
% 10.76/4.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/4.63  
% 10.76/4.63  Inference rules
% 10.76/4.63  ----------------------
% 10.76/4.63  #Ref     : 0
% 10.76/4.63  #Sup     : 5644
% 10.76/4.63  #Fact    : 0
% 10.76/4.63  #Define  : 0
% 10.76/4.63  #Split   : 0
% 10.76/4.63  #Chain   : 0
% 10.76/4.63  #Close   : 0
% 10.76/4.63  
% 10.76/4.63  Ordering : KBO
% 10.76/4.63  
% 10.76/4.63  Simplification rules
% 10.76/4.63  ----------------------
% 10.76/4.63  #Subsume      : 333
% 10.76/4.63  #Demod        : 6955
% 10.76/4.63  #Tautology    : 3344
% 10.76/4.63  #SimpNegUnit  : 0
% 10.76/4.63  #BackRed      : 13
% 10.76/4.63  
% 10.76/4.63  #Partial instantiations: 0
% 10.76/4.63  #Strategies tried      : 1
% 10.76/4.63  
% 10.76/4.63  Timing (in seconds)
% 10.76/4.63  ----------------------
% 10.76/4.63  Preprocessing        : 0.33
% 10.76/4.63  Parsing              : 0.18
% 10.76/4.64  CNF conversion       : 0.02
% 10.76/4.64  Main loop            : 3.53
% 10.76/4.64  Inferencing          : 0.69
% 10.76/4.64  Reduction            : 2.15
% 10.76/4.64  Demodulation         : 1.98
% 10.76/4.64  BG Simplification    : 0.09
% 10.76/4.64  Subsumption          : 0.44
% 10.76/4.64  Abstraction          : 0.17
% 10.76/4.64  MUC search           : 0.00
% 10.76/4.64  Cooper               : 0.00
% 10.76/4.64  Total                : 3.90
% 10.76/4.64  Index Insertion      : 0.00
% 10.76/4.64  Index Deletion       : 0.00
% 10.76/4.64  Index Matching       : 0.00
% 10.76/4.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
