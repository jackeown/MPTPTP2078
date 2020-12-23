%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:58 EST 2020

% Result     : Theorem 8.95s
% Output     : CNFRefutation 8.95s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 146 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :   84 ( 152 expanded)
%              Number of equality atoms :   66 ( 119 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),B_36) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_184,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_85,c_184])).

tff(c_220,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = A_54
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_238,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_189,c_220])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_316,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_362,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_316])).

tff(c_366,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_362])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1463,plain,(
    ! [A_107,B_108] : k4_xboole_0(k4_xboole_0(A_107,B_108),B_108) = k4_xboole_0(A_107,B_108) ),
    inference(resolution,[status(thm)],[c_26,c_220])).

tff(c_1493,plain,(
    ! [A_107,B_108] : k4_xboole_0(k4_xboole_0(A_107,B_108),k4_xboole_0(A_107,B_108)) = k3_xboole_0(k4_xboole_0(A_107,B_108),B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_20])).

tff(c_1561,plain,(
    ! [A_109,B_110] : k3_xboole_0(k4_xboole_0(A_109,B_110),B_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_1493])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1578,plain,(
    ! [A_109,B_110,C_19] : k3_xboole_0(k4_xboole_0(A_109,B_110),k4_xboole_0(B_110,C_19)) = k4_xboole_0(k1_xboole_0,C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_22])).

tff(c_2208,plain,(
    ! [A_127,B_128,C_129] : k3_xboole_0(k4_xboole_0(A_127,B_128),k4_xboole_0(B_128,C_129)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_1578])).

tff(c_2289,plain,(
    ! [A_127,A_15,B_16] : k3_xboole_0(k4_xboole_0(A_127,A_15),k3_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2208])).

tff(c_959,plain,(
    ! [A_84,B_85,C_86] : k4_xboole_0(k3_xboole_0(A_84,B_85),C_86) = k3_xboole_0(A_84,k4_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1846,plain,(
    ! [A_119,B_120] : k3_xboole_0(A_119,k4_xboole_0(B_120,k3_xboole_0(A_119,B_120))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_366])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1875,plain,(
    ! [A_119,B_120] : k4_xboole_0(A_119,k4_xboole_0(B_120,k3_xboole_0(A_119,B_120))) = k4_xboole_0(A_119,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1846,c_18])).

tff(c_2336,plain,(
    ! [A_130,B_131] : k4_xboole_0(A_130,k4_xboole_0(B_131,k3_xboole_0(A_130,B_131))) = A_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1875])).

tff(c_190,plain,(
    ! [B_22,A_21] : r1_xboole_0(B_22,k4_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_26,c_184])).

tff(c_237,plain,(
    ! [B_22,A_21] : k4_xboole_0(B_22,k4_xboole_0(A_21,B_22)) = B_22 ),
    inference(resolution,[status(thm)],[c_190,c_220])).

tff(c_1604,plain,(
    ! [B_22,A_21] : k3_xboole_0(B_22,k4_xboole_0(A_21,B_22)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_1561])).

tff(c_6653,plain,(
    ! [B_212,A_213] : k3_xboole_0(k4_xboole_0(B_212,k3_xboole_0(A_213,B_212)),A_213) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2336,c_1604])).

tff(c_6735,plain,(
    ! [A_15,B_16,A_127] : k3_xboole_0(k4_xboole_0(k3_xboole_0(A_15,B_16),k1_xboole_0),k4_xboole_0(A_127,A_15)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_6653])).

tff(c_8480,plain,(
    ! [A_232,B_233,A_234] : k3_xboole_0(k3_xboole_0(A_232,B_233),k4_xboole_0(A_234,A_232)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6735])).

tff(c_367,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_362])).

tff(c_372,plain,(
    ! [A_63] : k4_xboole_0(A_63,k1_xboole_0) = k3_xboole_0(A_63,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_20])).

tff(c_399,plain,(
    ! [A_63] : k3_xboole_0(A_63,A_63) = A_63 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_372])).

tff(c_1009,plain,(
    ! [A_63,C_86] : k3_xboole_0(A_63,k4_xboole_0(A_63,C_86)) = k4_xboole_0(A_63,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_959])).

tff(c_8750,plain,(
    ! [A_235,B_236] : k4_xboole_0(k3_xboole_0(A_235,B_236),A_235) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8480,c_1009])).

tff(c_206,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | k4_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_210,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | k4_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_206,c_39])).

tff(c_9017,plain,(
    ! [A_235,B_236] : k2_xboole_0(k3_xboole_0(A_235,B_236),A_235) = A_235 ),
    inference(superposition,[status(thm),theory(equality)],[c_8750,c_210])).

tff(c_469,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k4_xboole_0(B_68,A_67)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_482,plain,(
    ! [A_13,B_14] : k5_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = k2_xboole_0(k3_xboole_0(A_13,B_14),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_469])).

tff(c_12140,plain,(
    ! [A_272,B_273] : k5_xboole_0(k3_xboole_0(A_272,B_273),k4_xboole_0(A_272,B_273)) = A_272 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9017,c_482])).

tff(c_86,plain,(
    ! [B_37,A_38] : k5_xboole_0(B_37,A_38) = k5_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    ! [B_37] : k5_xboole_0(k1_xboole_0,B_37) = B_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_24])).

tff(c_34,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_640,plain,(
    ! [A_75,B_76,C_77] : k5_xboole_0(k5_xboole_0(A_75,B_76),C_77) = k5_xboole_0(A_75,k5_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_704,plain,(
    ! [A_28,C_77] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_77)) = k5_xboole_0(k1_xboole_0,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_640])).

tff(c_717,plain,(
    ! [A_28,C_77] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_77)) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_704])).

tff(c_22705,plain,(
    ! [A_364,B_365] : k5_xboole_0(k3_xboole_0(A_364,B_365),A_364) = k4_xboole_0(A_364,B_365) ),
    inference(superposition,[status(thm),theory(equality)],[c_12140,c_717])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22758,plain,(
    ! [A_364,B_365] : k5_xboole_0(A_364,k3_xboole_0(A_364,B_365)) = k4_xboole_0(A_364,B_365) ),
    inference(superposition,[status(thm),theory(equality)],[c_22705,c_2])).

tff(c_38,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22758,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:04:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.95/3.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.53  
% 8.95/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.53  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 8.95/3.53  
% 8.95/3.53  %Foreground sorts:
% 8.95/3.53  
% 8.95/3.53  
% 8.95/3.53  %Background operators:
% 8.95/3.53  
% 8.95/3.53  
% 8.95/3.53  %Foreground operators:
% 8.95/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.95/3.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.95/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.95/3.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.95/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.95/3.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.95/3.53  tff('#skF_2', type, '#skF_2': $i).
% 8.95/3.53  tff('#skF_1', type, '#skF_1': $i).
% 8.95/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.95/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.95/3.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.95/3.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.95/3.53  
% 8.95/3.55  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.95/3.55  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.95/3.55  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.95/3.55  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.95/3.55  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.95/3.55  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.95/3.55  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.95/3.55  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.95/3.55  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.95/3.55  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.95/3.55  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 8.95/3.55  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.95/3.55  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.95/3.55  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.95/3.55  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.95/3.55  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.95/3.55  tff(f_68, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.95/3.55  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.95/3.55  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.95/3.55  tff(c_82, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), B_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.95/3.55  tff(c_85, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_82])).
% 8.95/3.55  tff(c_184, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.95/3.55  tff(c_189, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_85, c_184])).
% 8.95/3.55  tff(c_220, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=A_54 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.95/3.55  tff(c_238, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_189, c_220])).
% 8.95/3.55  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.95/3.55  tff(c_316, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.95/3.55  tff(c_362, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_316])).
% 8.95/3.55  tff(c_366, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_362])).
% 8.95/3.55  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.95/3.55  tff(c_1463, plain, (![A_107, B_108]: (k4_xboole_0(k4_xboole_0(A_107, B_108), B_108)=k4_xboole_0(A_107, B_108))), inference(resolution, [status(thm)], [c_26, c_220])).
% 8.95/3.55  tff(c_1493, plain, (![A_107, B_108]: (k4_xboole_0(k4_xboole_0(A_107, B_108), k4_xboole_0(A_107, B_108))=k3_xboole_0(k4_xboole_0(A_107, B_108), B_108))), inference(superposition, [status(thm), theory('equality')], [c_1463, c_20])).
% 8.95/3.55  tff(c_1561, plain, (![A_109, B_110]: (k3_xboole_0(k4_xboole_0(A_109, B_110), B_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_366, c_1493])).
% 8.95/3.55  tff(c_22, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.95/3.55  tff(c_1578, plain, (![A_109, B_110, C_19]: (k3_xboole_0(k4_xboole_0(A_109, B_110), k4_xboole_0(B_110, C_19))=k4_xboole_0(k1_xboole_0, C_19))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_22])).
% 8.95/3.55  tff(c_2208, plain, (![A_127, B_128, C_129]: (k3_xboole_0(k4_xboole_0(A_127, B_128), k4_xboole_0(B_128, C_129))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_238, c_1578])).
% 8.95/3.55  tff(c_2289, plain, (![A_127, A_15, B_16]: (k3_xboole_0(k4_xboole_0(A_127, A_15), k3_xboole_0(A_15, B_16))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_2208])).
% 8.95/3.55  tff(c_959, plain, (![A_84, B_85, C_86]: (k4_xboole_0(k3_xboole_0(A_84, B_85), C_86)=k3_xboole_0(A_84, k4_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.95/3.55  tff(c_1846, plain, (![A_119, B_120]: (k3_xboole_0(A_119, k4_xboole_0(B_120, k3_xboole_0(A_119, B_120)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_959, c_366])).
% 8.95/3.55  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.95/3.55  tff(c_1875, plain, (![A_119, B_120]: (k4_xboole_0(A_119, k4_xboole_0(B_120, k3_xboole_0(A_119, B_120)))=k4_xboole_0(A_119, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1846, c_18])).
% 8.95/3.55  tff(c_2336, plain, (![A_130, B_131]: (k4_xboole_0(A_130, k4_xboole_0(B_131, k3_xboole_0(A_130, B_131)))=A_130)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1875])).
% 8.95/3.55  tff(c_190, plain, (![B_22, A_21]: (r1_xboole_0(B_22, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_26, c_184])).
% 8.95/3.55  tff(c_237, plain, (![B_22, A_21]: (k4_xboole_0(B_22, k4_xboole_0(A_21, B_22))=B_22)), inference(resolution, [status(thm)], [c_190, c_220])).
% 8.95/3.55  tff(c_1604, plain, (![B_22, A_21]: (k3_xboole_0(B_22, k4_xboole_0(A_21, B_22))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_237, c_1561])).
% 8.95/3.55  tff(c_6653, plain, (![B_212, A_213]: (k3_xboole_0(k4_xboole_0(B_212, k3_xboole_0(A_213, B_212)), A_213)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2336, c_1604])).
% 8.95/3.55  tff(c_6735, plain, (![A_15, B_16, A_127]: (k3_xboole_0(k4_xboole_0(k3_xboole_0(A_15, B_16), k1_xboole_0), k4_xboole_0(A_127, A_15))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2289, c_6653])).
% 8.95/3.55  tff(c_8480, plain, (![A_232, B_233, A_234]: (k3_xboole_0(k3_xboole_0(A_232, B_233), k4_xboole_0(A_234, A_232))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6735])).
% 8.95/3.55  tff(c_367, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_362])).
% 8.95/3.55  tff(c_372, plain, (![A_63]: (k4_xboole_0(A_63, k1_xboole_0)=k3_xboole_0(A_63, A_63))), inference(superposition, [status(thm), theory('equality')], [c_367, c_20])).
% 8.95/3.55  tff(c_399, plain, (![A_63]: (k3_xboole_0(A_63, A_63)=A_63)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_372])).
% 8.95/3.55  tff(c_1009, plain, (![A_63, C_86]: (k3_xboole_0(A_63, k4_xboole_0(A_63, C_86))=k4_xboole_0(A_63, C_86))), inference(superposition, [status(thm), theory('equality')], [c_399, c_959])).
% 8.95/3.55  tff(c_8750, plain, (![A_235, B_236]: (k4_xboole_0(k3_xboole_0(A_235, B_236), A_235)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8480, c_1009])).
% 8.95/3.55  tff(c_206, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | k4_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.95/3.55  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.95/3.55  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.95/3.55  tff(c_39, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 8.95/3.55  tff(c_210, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | k4_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_206, c_39])).
% 8.95/3.55  tff(c_9017, plain, (![A_235, B_236]: (k2_xboole_0(k3_xboole_0(A_235, B_236), A_235)=A_235)), inference(superposition, [status(thm), theory('equality')], [c_8750, c_210])).
% 8.95/3.55  tff(c_469, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k4_xboole_0(B_68, A_67))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.95/3.55  tff(c_482, plain, (![A_13, B_14]: (k5_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=k2_xboole_0(k3_xboole_0(A_13, B_14), A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_469])).
% 8.95/3.55  tff(c_12140, plain, (![A_272, B_273]: (k5_xboole_0(k3_xboole_0(A_272, B_273), k4_xboole_0(A_272, B_273))=A_272)), inference(demodulation, [status(thm), theory('equality')], [c_9017, c_482])).
% 8.95/3.55  tff(c_86, plain, (![B_37, A_38]: (k5_xboole_0(B_37, A_38)=k5_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.95/3.55  tff(c_24, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.95/3.55  tff(c_106, plain, (![B_37]: (k5_xboole_0(k1_xboole_0, B_37)=B_37)), inference(superposition, [status(thm), theory('equality')], [c_86, c_24])).
% 8.95/3.55  tff(c_34, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.95/3.55  tff(c_640, plain, (![A_75, B_76, C_77]: (k5_xboole_0(k5_xboole_0(A_75, B_76), C_77)=k5_xboole_0(A_75, k5_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.95/3.55  tff(c_704, plain, (![A_28, C_77]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_77))=k5_xboole_0(k1_xboole_0, C_77))), inference(superposition, [status(thm), theory('equality')], [c_34, c_640])).
% 8.95/3.55  tff(c_717, plain, (![A_28, C_77]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_77))=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_704])).
% 8.95/3.55  tff(c_22705, plain, (![A_364, B_365]: (k5_xboole_0(k3_xboole_0(A_364, B_365), A_364)=k4_xboole_0(A_364, B_365))), inference(superposition, [status(thm), theory('equality')], [c_12140, c_717])).
% 8.95/3.55  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.95/3.55  tff(c_22758, plain, (![A_364, B_365]: (k5_xboole_0(A_364, k3_xboole_0(A_364, B_365))=k4_xboole_0(A_364, B_365))), inference(superposition, [status(thm), theory('equality')], [c_22705, c_2])).
% 8.95/3.55  tff(c_38, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.95/3.55  tff(c_22913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22758, c_38])).
% 8.95/3.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.55  
% 8.95/3.55  Inference rules
% 8.95/3.55  ----------------------
% 8.95/3.55  #Ref     : 0
% 8.95/3.55  #Sup     : 5732
% 8.95/3.55  #Fact    : 0
% 8.95/3.55  #Define  : 0
% 8.95/3.55  #Split   : 0
% 8.95/3.55  #Chain   : 0
% 8.95/3.55  #Close   : 0
% 8.95/3.55  
% 8.95/3.55  Ordering : KBO
% 8.95/3.55  
% 8.95/3.55  Simplification rules
% 8.95/3.55  ----------------------
% 8.95/3.55  #Subsume      : 157
% 8.95/3.55  #Demod        : 6011
% 8.95/3.55  #Tautology    : 3978
% 8.95/3.55  #SimpNegUnit  : 0
% 8.95/3.55  #BackRed      : 3
% 8.95/3.55  
% 8.95/3.55  #Partial instantiations: 0
% 8.95/3.55  #Strategies tried      : 1
% 8.95/3.55  
% 8.95/3.55  Timing (in seconds)
% 8.95/3.55  ----------------------
% 8.95/3.55  Preprocessing        : 0.32
% 8.95/3.55  Parsing              : 0.17
% 8.95/3.55  CNF conversion       : 0.02
% 8.95/3.55  Main loop            : 2.41
% 8.95/3.55  Inferencing          : 0.62
% 8.95/3.55  Reduction            : 1.22
% 8.95/3.55  Demodulation         : 1.05
% 8.95/3.55  BG Simplification    : 0.07
% 8.95/3.55  Subsumption          : 0.37
% 8.95/3.55  Abstraction          : 0.13
% 8.95/3.55  MUC search           : 0.00
% 8.95/3.55  Cooper               : 0.00
% 8.95/3.55  Total                : 2.76
% 8.95/3.55  Index Insertion      : 0.00
% 8.95/3.55  Index Deletion       : 0.00
% 8.95/3.55  Index Matching       : 0.00
% 8.95/3.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
