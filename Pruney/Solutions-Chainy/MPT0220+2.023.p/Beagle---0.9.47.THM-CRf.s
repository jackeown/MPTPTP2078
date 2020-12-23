%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:07 EST 2020

% Result     : Theorem 8.05s
% Output     : CNFRefutation 8.13s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 403 expanded)
%              Number of leaves         :   31 ( 150 expanded)
%              Depth                    :   15
%              Number of atoms          :   69 ( 406 expanded)
%              Number of equality atoms :   61 ( 376 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_20,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_296,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_311,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_296])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_208,plain,(
    ! [B_67] : k3_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_217,plain,(
    ! [B_67] : k3_xboole_0(B_67,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_2])).

tff(c_467,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_492,plain,(
    ! [B_67] : k5_xboole_0(B_67,k1_xboole_0) = k4_xboole_0(B_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_467])).

tff(c_511,plain,(
    ! [B_67] : k2_xboole_0(B_67,k1_xboole_0) = B_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_16,c_492])).

tff(c_315,plain,(
    ! [A_73] : k5_xboole_0(A_73,k1_xboole_0) = k2_xboole_0(A_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_296])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_324,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = k2_xboole_0(A_73,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_4])).

tff(c_567,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_324])).

tff(c_197,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_178])).

tff(c_338,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_197])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_151])).

tff(c_498,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_467])).

tff(c_513,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_498])).

tff(c_40,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1316,plain,(
    ! [A_123,B_124] : k3_xboole_0(k1_tarski(A_123),k2_tarski(A_123,B_124)) = k1_tarski(A_123) ),
    inference(resolution,[status(thm)],[c_40,c_151])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1325,plain,(
    ! [A_123,B_124] : k5_xboole_0(k1_tarski(A_123),k1_tarski(A_123)) = k4_xboole_0(k1_tarski(A_123),k2_tarski(A_123,B_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1316,c_12])).

tff(c_1333,plain,(
    ! [A_123,B_124] : k4_xboole_0(k1_tarski(A_123),k2_tarski(A_123,B_124)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_1325])).

tff(c_1239,plain,(
    ! [B_121,A_122] : k5_xboole_0(B_121,k3_xboole_0(A_122,B_121)) = k4_xboole_0(B_121,A_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_467])).

tff(c_634,plain,(
    ! [A_85,B_86,C_87] : k5_xboole_0(k5_xboole_0(A_85,B_86),C_87) = k5_xboole_0(A_85,k5_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_670,plain,(
    ! [B_6,C_87] : k5_xboole_0(B_6,k5_xboole_0(B_6,C_87)) = k5_xboole_0(k1_xboole_0,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_634])).

tff(c_708,plain,(
    ! [B_6,C_87] : k5_xboole_0(B_6,k5_xboole_0(B_6,C_87)) = C_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_670])).

tff(c_1404,plain,(
    ! [B_129,A_130] : k5_xboole_0(B_129,k4_xboole_0(B_129,A_130)) = k3_xboole_0(A_130,B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_708])).

tff(c_1443,plain,(
    ! [A_123,B_124] : k3_xboole_0(k2_tarski(A_123,B_124),k1_tarski(A_123)) = k5_xboole_0(k1_tarski(A_123),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_1404])).

tff(c_1474,plain,(
    ! [A_123,B_124] : k3_xboole_0(k2_tarski(A_123,B_124),k1_tarski(A_123)) = k1_tarski(A_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_4,c_1443])).

tff(c_868,plain,(
    ! [B_113,C_114] : k5_xboole_0(B_113,k5_xboole_0(B_113,C_114)) = C_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_670])).

tff(c_1481,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k4_xboole_0(A_131,B_132)) = k3_xboole_0(A_131,B_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_868])).

tff(c_923,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k5_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_868])).

tff(c_1496,plain,(
    ! [A_131,B_132] : k5_xboole_0(k4_xboole_0(A_131,B_132),k3_xboole_0(A_131,B_132)) = A_131 ),
    inference(superposition,[status(thm),theory(equality)],[c_1481,c_923])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1544,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1481])).

tff(c_1560,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1544])).

tff(c_181,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,k4_xboole_0(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_18])).

tff(c_1981,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_181])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2479,plain,(
    ! [A_161,A_159,B_160] : k5_xboole_0(A_161,k5_xboole_0(A_159,B_160)) = k5_xboole_0(A_159,k5_xboole_0(B_160,A_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_634])).

tff(c_2853,plain,(
    ! [A_162,A_163] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_162,A_163)) = k5_xboole_0(A_163,A_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_2479])).

tff(c_2979,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2853])).

tff(c_3122,plain,(
    ! [B_166,A_167] : k5_xboole_0(k4_xboole_0(B_166,A_167),A_167) = k2_xboole_0(A_167,B_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_2979])).

tff(c_3184,plain,(
    ! [A_65,B_66] : k5_xboole_0(k4_xboole_0(A_65,B_66),k3_xboole_0(A_65,B_66)) = k2_xboole_0(k3_xboole_0(A_65,B_66),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_3122])).

tff(c_3413,plain,(
    ! [A_172,B_173] : k2_xboole_0(k3_xboole_0(A_172,B_173),A_172) = A_172 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1496,c_3184])).

tff(c_3432,plain,(
    ! [A_123,B_124] : k2_xboole_0(k1_tarski(A_123),k2_tarski(A_123,B_124)) = k2_tarski(A_123,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_1474,c_3413])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3432,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.05/3.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.13/3.20  
% 8.13/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.13/3.20  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.13/3.20  
% 8.13/3.20  %Foreground sorts:
% 8.13/3.20  
% 8.13/3.20  
% 8.13/3.20  %Background operators:
% 8.13/3.20  
% 8.13/3.20  
% 8.13/3.20  %Foreground operators:
% 8.13/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.13/3.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.13/3.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.13/3.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.13/3.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.13/3.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.13/3.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.13/3.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.13/3.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.13/3.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.13/3.20  tff('#skF_2', type, '#skF_2': $i).
% 8.13/3.20  tff('#skF_1', type, '#skF_1': $i).
% 8.13/3.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.13/3.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.13/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.13/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.13/3.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.13/3.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.13/3.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.13/3.20  
% 8.13/3.22  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 8.13/3.22  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.13/3.22  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.13/3.22  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.13/3.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.13/3.22  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.13/3.22  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.13/3.22  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.13/3.22  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.13/3.22  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.13/3.22  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.13/3.22  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 8.13/3.22  tff(c_20, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.13/3.22  tff(c_296, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.13/3.22  tff(c_311, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_296])).
% 8.13/3.22  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.13/3.22  tff(c_178, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.13/3.22  tff(c_208, plain, (![B_67]: (k3_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_20])).
% 8.13/3.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.13/3.22  tff(c_217, plain, (![B_67]: (k3_xboole_0(B_67, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_2])).
% 8.13/3.22  tff(c_467, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.13/3.22  tff(c_492, plain, (![B_67]: (k5_xboole_0(B_67, k1_xboole_0)=k4_xboole_0(B_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_217, c_467])).
% 8.13/3.22  tff(c_511, plain, (![B_67]: (k2_xboole_0(B_67, k1_xboole_0)=B_67)), inference(demodulation, [status(thm), theory('equality')], [c_311, c_16, c_492])).
% 8.13/3.22  tff(c_315, plain, (![A_73]: (k5_xboole_0(A_73, k1_xboole_0)=k2_xboole_0(A_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_296])).
% 8.13/3.22  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.13/3.22  tff(c_324, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=k2_xboole_0(A_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_315, c_4])).
% 8.13/3.22  tff(c_567, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_511, c_324])).
% 8.13/3.22  tff(c_197, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_178])).
% 8.13/3.22  tff(c_338, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_217, c_197])).
% 8.13/3.22  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.13/3.22  tff(c_151, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.13/3.22  tff(c_159, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_151])).
% 8.13/3.22  tff(c_498, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_159, c_467])).
% 8.13/3.22  tff(c_513, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_338, c_498])).
% 8.13/3.22  tff(c_40, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.13/3.22  tff(c_1316, plain, (![A_123, B_124]: (k3_xboole_0(k1_tarski(A_123), k2_tarski(A_123, B_124))=k1_tarski(A_123))), inference(resolution, [status(thm)], [c_40, c_151])).
% 8.13/3.22  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.13/3.22  tff(c_1325, plain, (![A_123, B_124]: (k5_xboole_0(k1_tarski(A_123), k1_tarski(A_123))=k4_xboole_0(k1_tarski(A_123), k2_tarski(A_123, B_124)))), inference(superposition, [status(thm), theory('equality')], [c_1316, c_12])).
% 8.13/3.22  tff(c_1333, plain, (![A_123, B_124]: (k4_xboole_0(k1_tarski(A_123), k2_tarski(A_123, B_124))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_513, c_1325])).
% 8.13/3.22  tff(c_1239, plain, (![B_121, A_122]: (k5_xboole_0(B_121, k3_xboole_0(A_122, B_121))=k4_xboole_0(B_121, A_122))), inference(superposition, [status(thm), theory('equality')], [c_2, c_467])).
% 8.13/3.22  tff(c_634, plain, (![A_85, B_86, C_87]: (k5_xboole_0(k5_xboole_0(A_85, B_86), C_87)=k5_xboole_0(A_85, k5_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.13/3.22  tff(c_670, plain, (![B_6, C_87]: (k5_xboole_0(B_6, k5_xboole_0(B_6, C_87))=k5_xboole_0(k1_xboole_0, C_87))), inference(superposition, [status(thm), theory('equality')], [c_513, c_634])).
% 8.13/3.22  tff(c_708, plain, (![B_6, C_87]: (k5_xboole_0(B_6, k5_xboole_0(B_6, C_87))=C_87)), inference(demodulation, [status(thm), theory('equality')], [c_567, c_670])).
% 8.13/3.22  tff(c_1404, plain, (![B_129, A_130]: (k5_xboole_0(B_129, k4_xboole_0(B_129, A_130))=k3_xboole_0(A_130, B_129))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_708])).
% 8.13/3.22  tff(c_1443, plain, (![A_123, B_124]: (k3_xboole_0(k2_tarski(A_123, B_124), k1_tarski(A_123))=k5_xboole_0(k1_tarski(A_123), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1333, c_1404])).
% 8.13/3.22  tff(c_1474, plain, (![A_123, B_124]: (k3_xboole_0(k2_tarski(A_123, B_124), k1_tarski(A_123))=k1_tarski(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_4, c_1443])).
% 8.13/3.22  tff(c_868, plain, (![B_113, C_114]: (k5_xboole_0(B_113, k5_xboole_0(B_113, C_114))=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_567, c_670])).
% 8.13/3.22  tff(c_1481, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k4_xboole_0(A_131, B_132))=k3_xboole_0(A_131, B_132))), inference(superposition, [status(thm), theory('equality')], [c_12, c_868])).
% 8.13/3.22  tff(c_923, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k5_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_868])).
% 8.13/3.22  tff(c_1496, plain, (![A_131, B_132]: (k5_xboole_0(k4_xboole_0(A_131, B_132), k3_xboole_0(A_131, B_132))=A_131)), inference(superposition, [status(thm), theory('equality')], [c_1481, c_923])).
% 8.13/3.22  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.13/3.22  tff(c_1544, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1481])).
% 8.13/3.22  tff(c_1560, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1544])).
% 8.13/3.22  tff(c_181, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k3_xboole_0(A_65, k4_xboole_0(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_18])).
% 8.13/3.22  tff(c_1981, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_181])).
% 8.13/3.22  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.13/3.22  tff(c_2479, plain, (![A_161, A_159, B_160]: (k5_xboole_0(A_161, k5_xboole_0(A_159, B_160))=k5_xboole_0(A_159, k5_xboole_0(B_160, A_161)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_634])).
% 8.13/3.22  tff(c_2853, plain, (![A_162, A_163]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_162, A_163))=k5_xboole_0(A_163, A_162))), inference(superposition, [status(thm), theory('equality')], [c_567, c_2479])).
% 8.13/3.22  tff(c_2979, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2853])).
% 8.13/3.22  tff(c_3122, plain, (![B_166, A_167]: (k5_xboole_0(k4_xboole_0(B_166, A_167), A_167)=k2_xboole_0(A_167, B_166))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_2979])).
% 8.13/3.22  tff(c_3184, plain, (![A_65, B_66]: (k5_xboole_0(k4_xboole_0(A_65, B_66), k3_xboole_0(A_65, B_66))=k2_xboole_0(k3_xboole_0(A_65, B_66), A_65))), inference(superposition, [status(thm), theory('equality')], [c_1981, c_3122])).
% 8.13/3.22  tff(c_3413, plain, (![A_172, B_173]: (k2_xboole_0(k3_xboole_0(A_172, B_173), A_172)=A_172)), inference(demodulation, [status(thm), theory('equality')], [c_1496, c_3184])).
% 8.13/3.22  tff(c_3432, plain, (![A_123, B_124]: (k2_xboole_0(k1_tarski(A_123), k2_tarski(A_123, B_124))=k2_tarski(A_123, B_124))), inference(superposition, [status(thm), theory('equality')], [c_1474, c_3413])).
% 8.13/3.22  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.13/3.22  tff(c_12997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3432, c_42])).
% 8.13/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.13/3.22  
% 8.13/3.22  Inference rules
% 8.13/3.22  ----------------------
% 8.13/3.22  #Ref     : 0
% 8.13/3.22  #Sup     : 3221
% 8.13/3.22  #Fact    : 0
% 8.13/3.22  #Define  : 0
% 8.13/3.22  #Split   : 0
% 8.13/3.22  #Chain   : 0
% 8.13/3.22  #Close   : 0
% 8.13/3.22  
% 8.13/3.22  Ordering : KBO
% 8.13/3.22  
% 8.13/3.22  Simplification rules
% 8.13/3.22  ----------------------
% 8.13/3.22  #Subsume      : 186
% 8.13/3.22  #Demod        : 3762
% 8.13/3.22  #Tautology    : 1898
% 8.13/3.22  #SimpNegUnit  : 0
% 8.13/3.22  #BackRed      : 5
% 8.13/3.22  
% 8.13/3.22  #Partial instantiations: 0
% 8.13/3.22  #Strategies tried      : 1
% 8.13/3.22  
% 8.13/3.22  Timing (in seconds)
% 8.13/3.22  ----------------------
% 8.13/3.22  Preprocessing        : 0.32
% 8.13/3.22  Parsing              : 0.17
% 8.13/3.22  CNF conversion       : 0.02
% 8.13/3.22  Main loop            : 2.14
% 8.13/3.22  Inferencing          : 0.47
% 8.13/3.22  Reduction            : 1.28
% 8.13/3.22  Demodulation         : 1.16
% 8.13/3.22  BG Simplification    : 0.07
% 8.13/3.22  Subsumption          : 0.24
% 8.13/3.22  Abstraction          : 0.10
% 8.13/3.22  MUC search           : 0.00
% 8.13/3.22  Cooper               : 0.00
% 8.13/3.22  Total                : 2.49
% 8.13/3.22  Index Insertion      : 0.00
% 8.13/3.22  Index Deletion       : 0.00
% 8.13/3.22  Index Matching       : 0.00
% 8.13/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
