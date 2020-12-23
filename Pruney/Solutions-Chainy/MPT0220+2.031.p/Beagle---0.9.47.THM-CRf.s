%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:08 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 134 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 ( 119 expanded)
%              Number of equality atoms :   52 ( 110 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,(
    ! [B_63,A_64] : k5_xboole_0(B_63,A_64) = k5_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_16])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_274,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k4_xboole_0(B_76,A_75)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_294,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k2_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_274])).

tff(c_309,plain,(
    ! [A_78] : k2_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_294])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_203,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_216,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(resolution,[status(thm)],[c_18,c_203])).

tff(c_372,plain,(
    ! [A_82] : k3_xboole_0(k1_xboole_0,A_82) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_216])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_377,plain,(
    ! [A_82] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_8])).

tff(c_411,plain,(
    ! [A_82] : k4_xboole_0(k1_xboole_0,A_82) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_377])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_319,plain,(
    ! [A_78] : k4_xboole_0(k1_xboole_0,A_78) = k4_xboole_0(A_78,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_14])).

tff(c_627,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_319])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_343,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_369,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_343])).

tff(c_628,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_369])).

tff(c_38,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1212,plain,(
    ! [A_127,B_128] : k3_xboole_0(k1_tarski(A_127),k2_tarski(A_127,B_128)) = k1_tarski(A_127) ),
    inference(resolution,[status(thm)],[c_38,c_203])).

tff(c_1221,plain,(
    ! [A_127,B_128] : k5_xboole_0(k1_tarski(A_127),k1_tarski(A_127)) = k4_xboole_0(k1_tarski(A_127),k2_tarski(A_127,B_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_8])).

tff(c_1232,plain,(
    ! [A_129,B_130] : k4_xboole_0(k1_tarski(A_129),k2_tarski(A_129,B_130)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_1221])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1237,plain,(
    ! [A_129,B_130] : k2_xboole_0(k2_tarski(A_129,B_130),k1_tarski(A_129)) = k5_xboole_0(k2_tarski(A_129,B_130),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_22])).

tff(c_11823,plain,(
    ! [A_256,B_257] : k2_xboole_0(k2_tarski(A_256,B_257),k1_tarski(A_256)) = k2_tarski(A_256,B_257) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1237])).

tff(c_499,plain,(
    ! [A_88,B_89,C_90] : k5_xboole_0(k5_xboole_0(A_88,B_89),C_90) = k5_xboole_0(A_88,k5_xboole_0(B_89,C_90)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2368,plain,(
    ! [C_160,A_161,B_162] : k5_xboole_0(C_160,k5_xboole_0(A_161,B_162)) = k5_xboole_0(A_161,k5_xboole_0(B_162,C_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_4])).

tff(c_2786,plain,(
    ! [A_163,C_164] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_163,C_164)) = k5_xboole_0(C_164,A_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_2368])).

tff(c_2915,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2786])).

tff(c_2965,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k2_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_2915])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_366,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_343])).

tff(c_2883,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_2786])).

tff(c_2956,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_2883])).

tff(c_4807,plain,(
    ! [A_189,B_190,C_191] : k5_xboole_0(A_189,k5_xboole_0(k3_xboole_0(A_189,B_190),C_191)) = k5_xboole_0(k4_xboole_0(A_189,B_190),C_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_499])).

tff(c_4889,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2956,c_4807])).

tff(c_5018,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2965,c_22,c_4889])).

tff(c_11892,plain,(
    ! [A_256,B_257] : k2_xboole_0(k1_tarski(A_256),k2_tarski(A_256,B_257)) = k2_tarski(A_256,B_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_11823,c_5018])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11892,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/3.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/3.06  
% 7.97/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/3.06  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.97/3.06  
% 7.97/3.06  %Foreground sorts:
% 7.97/3.06  
% 7.97/3.06  
% 7.97/3.06  %Background operators:
% 7.97/3.06  
% 7.97/3.06  
% 7.97/3.06  %Foreground operators:
% 7.97/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/3.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.97/3.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.97/3.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.97/3.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.97/3.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.97/3.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.97/3.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.97/3.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.97/3.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.97/3.06  tff('#skF_2', type, '#skF_2': $i).
% 7.97/3.06  tff('#skF_1', type, '#skF_1': $i).
% 7.97/3.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.97/3.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.97/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/3.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.97/3.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.97/3.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.97/3.06  
% 7.97/3.08  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.97/3.08  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.97/3.08  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.97/3.08  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.97/3.08  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.97/3.08  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.97/3.08  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.97/3.08  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.97/3.08  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.97/3.08  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.97/3.08  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.97/3.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.97/3.08  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.97/3.08  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.97/3.08  tff(c_116, plain, (![B_63, A_64]: (k5_xboole_0(B_63, A_64)=k5_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.97/3.08  tff(c_132, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_116, c_16])).
% 7.97/3.08  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.97/3.08  tff(c_274, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k4_xboole_0(B_76, A_75))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.97/3.08  tff(c_294, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k2_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_274])).
% 7.97/3.08  tff(c_309, plain, (![A_78]: (k2_xboole_0(k1_xboole_0, A_78)=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_294])).
% 7.97/3.08  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.97/3.08  tff(c_203, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.97/3.08  tff(c_216, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(resolution, [status(thm)], [c_18, c_203])).
% 7.97/3.08  tff(c_372, plain, (![A_82]: (k3_xboole_0(k1_xboole_0, A_82)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_309, c_216])).
% 7.97/3.08  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.97/3.08  tff(c_377, plain, (![A_82]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_82))), inference(superposition, [status(thm), theory('equality')], [c_372, c_8])).
% 7.97/3.08  tff(c_411, plain, (![A_82]: (k4_xboole_0(k1_xboole_0, A_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_377])).
% 7.97/3.08  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.97/3.08  tff(c_319, plain, (![A_78]: (k4_xboole_0(k1_xboole_0, A_78)=k4_xboole_0(A_78, A_78))), inference(superposition, [status(thm), theory('equality')], [c_309, c_14])).
% 7.97/3.08  tff(c_627, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_319])).
% 7.97/3.08  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.97/3.08  tff(c_343, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.97/3.08  tff(c_369, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_343])).
% 7.97/3.08  tff(c_628, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_627, c_369])).
% 7.97/3.08  tff(c_38, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.97/3.08  tff(c_1212, plain, (![A_127, B_128]: (k3_xboole_0(k1_tarski(A_127), k2_tarski(A_127, B_128))=k1_tarski(A_127))), inference(resolution, [status(thm)], [c_38, c_203])).
% 7.97/3.08  tff(c_1221, plain, (![A_127, B_128]: (k5_xboole_0(k1_tarski(A_127), k1_tarski(A_127))=k4_xboole_0(k1_tarski(A_127), k2_tarski(A_127, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_1212, c_8])).
% 7.97/3.08  tff(c_1232, plain, (![A_129, B_130]: (k4_xboole_0(k1_tarski(A_129), k2_tarski(A_129, B_130))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_628, c_1221])).
% 7.97/3.08  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.97/3.08  tff(c_1237, plain, (![A_129, B_130]: (k2_xboole_0(k2_tarski(A_129, B_130), k1_tarski(A_129))=k5_xboole_0(k2_tarski(A_129, B_130), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1232, c_22])).
% 7.97/3.08  tff(c_11823, plain, (![A_256, B_257]: (k2_xboole_0(k2_tarski(A_256, B_257), k1_tarski(A_256))=k2_tarski(A_256, B_257))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1237])).
% 7.97/3.08  tff(c_499, plain, (![A_88, B_89, C_90]: (k5_xboole_0(k5_xboole_0(A_88, B_89), C_90)=k5_xboole_0(A_88, k5_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.97/3.08  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.97/3.08  tff(c_2368, plain, (![C_160, A_161, B_162]: (k5_xboole_0(C_160, k5_xboole_0(A_161, B_162))=k5_xboole_0(A_161, k5_xboole_0(B_162, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_499, c_4])).
% 7.97/3.08  tff(c_2786, plain, (![A_163, C_164]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_163, C_164))=k5_xboole_0(C_164, A_163))), inference(superposition, [status(thm), theory('equality')], [c_132, c_2368])).
% 7.97/3.08  tff(c_2915, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2786])).
% 7.97/3.08  tff(c_2965, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k2_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_2915])).
% 7.97/3.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.97/3.08  tff(c_366, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_343])).
% 7.97/3.08  tff(c_2883, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_366, c_2786])).
% 7.97/3.08  tff(c_2956, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_2883])).
% 7.97/3.08  tff(c_4807, plain, (![A_189, B_190, C_191]: (k5_xboole_0(A_189, k5_xboole_0(k3_xboole_0(A_189, B_190), C_191))=k5_xboole_0(k4_xboole_0(A_189, B_190), C_191))), inference(superposition, [status(thm), theory('equality')], [c_8, c_499])).
% 7.97/3.08  tff(c_4889, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2956, c_4807])).
% 7.97/3.08  tff(c_5018, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2965, c_22, c_4889])).
% 7.97/3.08  tff(c_11892, plain, (![A_256, B_257]: (k2_xboole_0(k1_tarski(A_256), k2_tarski(A_256, B_257))=k2_tarski(A_256, B_257))), inference(superposition, [status(thm), theory('equality')], [c_11823, c_5018])).
% 7.97/3.08  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.97/3.08  tff(c_11979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11892, c_40])).
% 7.97/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/3.08  
% 7.97/3.08  Inference rules
% 7.97/3.08  ----------------------
% 7.97/3.08  #Ref     : 0
% 7.97/3.08  #Sup     : 2987
% 7.97/3.08  #Fact    : 0
% 7.97/3.08  #Define  : 0
% 7.97/3.08  #Split   : 0
% 7.97/3.08  #Chain   : 0
% 7.97/3.08  #Close   : 0
% 7.97/3.08  
% 7.97/3.08  Ordering : KBO
% 7.97/3.08  
% 7.97/3.08  Simplification rules
% 7.97/3.08  ----------------------
% 7.97/3.08  #Subsume      : 182
% 7.97/3.08  #Demod        : 3313
% 7.97/3.08  #Tautology    : 1680
% 7.97/3.08  #SimpNegUnit  : 0
% 7.97/3.08  #BackRed      : 2
% 7.97/3.08  
% 7.97/3.08  #Partial instantiations: 0
% 7.97/3.08  #Strategies tried      : 1
% 7.97/3.08  
% 7.97/3.08  Timing (in seconds)
% 7.97/3.08  ----------------------
% 7.97/3.08  Preprocessing        : 0.31
% 7.97/3.08  Parsing              : 0.17
% 7.97/3.08  CNF conversion       : 0.02
% 7.97/3.08  Main loop            : 2.02
% 7.97/3.08  Inferencing          : 0.47
% 7.97/3.08  Reduction            : 1.18
% 7.97/3.08  Demodulation         : 1.07
% 7.97/3.08  BG Simplification    : 0.06
% 7.97/3.08  Subsumption          : 0.22
% 7.97/3.08  Abstraction          : 0.10
% 7.97/3.08  MUC search           : 0.00
% 7.97/3.08  Cooper               : 0.00
% 7.97/3.08  Total                : 2.36
% 7.97/3.08  Index Insertion      : 0.00
% 7.97/3.08  Index Deletion       : 0.00
% 7.97/3.08  Index Matching       : 0.00
% 7.97/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
