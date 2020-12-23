%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:06 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 147 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :   51 ( 138 expanded)
%              Number of equality atoms :   44 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_120,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,A_65) = k5_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_136,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_20])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_207,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_218,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(resolution,[status(thm)],[c_22,c_207])).

tff(c_356,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_372,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k5_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_356])).

tff(c_390,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_372])).

tff(c_42,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1197,plain,(
    ! [A_128,B_129] : k3_xboole_0(k1_tarski(A_128),k2_tarski(A_128,B_129)) = k1_tarski(A_128) ),
    inference(resolution,[status(thm)],[c_42,c_207])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1206,plain,(
    ! [A_128,B_129] : k5_xboole_0(k1_tarski(A_128),k1_tarski(A_128)) = k4_xboole_0(k1_tarski(A_128),k2_tarski(A_128,B_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1197,c_12])).

tff(c_1214,plain,(
    ! [A_128,B_129] : k4_xboole_0(k1_tarski(A_128),k2_tarski(A_128,B_129)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_1206])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1121,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k3_xboole_0(B_127,A_126)) = k4_xboole_0(A_126,B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_356])).

tff(c_538,plain,(
    ! [A_90,B_91,C_92] : k5_xboole_0(k5_xboole_0(A_90,B_91),C_92) = k5_xboole_0(A_90,k5_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_575,plain,(
    ! [A_15,C_92] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_92)) = k5_xboole_0(k1_xboole_0,C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_538])).

tff(c_623,plain,(
    ! [A_15,C_92] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_92)) = C_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_575])).

tff(c_1136,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k4_xboole_0(A_126,B_127)) = k3_xboole_0(B_127,A_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_623])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2110,plain,(
    ! [C_158,A_159,B_160] : k5_xboole_0(C_158,k5_xboole_0(A_159,B_160)) = k5_xboole_0(A_159,k5_xboole_0(B_160,C_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_4])).

tff(c_2502,plain,(
    ! [A_161,C_162] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_161,C_162)) = k5_xboole_0(C_162,A_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2110])).

tff(c_2590,plain,(
    ! [A_126,B_127] : k5_xboole_0(k4_xboole_0(A_126,B_127),A_126) = k5_xboole_0(k1_xboole_0,k3_xboole_0(B_127,A_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_2502])).

tff(c_2667,plain,(
    ! [A_126,B_127] : k5_xboole_0(k4_xboole_0(A_126,B_127),A_126) = k3_xboole_0(B_127,A_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2590])).

tff(c_26,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4887,plain,(
    ! [A_194,B_195,C_196] : k5_xboole_0(A_194,k5_xboole_0(k4_xboole_0(B_195,A_194),C_196)) = k5_xboole_0(k2_xboole_0(A_194,B_195),C_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_538])).

tff(c_4967,plain,(
    ! [B_127,A_126] : k5_xboole_0(k2_xboole_0(B_127,A_126),A_126) = k5_xboole_0(B_127,k3_xboole_0(B_127,A_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2667,c_4887])).

tff(c_5106,plain,(
    ! [B_197,A_198] : k5_xboole_0(k2_xboole_0(B_197,A_198),A_198) = k4_xboole_0(B_197,A_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4967])).

tff(c_723,plain,(
    ! [A_100,C_101] : k5_xboole_0(A_100,k5_xboole_0(A_100,C_101)) = C_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_575])).

tff(c_800,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k5_xboole_0(B_108,A_107)) = B_108 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_723])).

tff(c_833,plain,(
    ! [A_15,C_92] : k5_xboole_0(k5_xboole_0(A_15,C_92),C_92) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_800])).

tff(c_7125,plain,(
    ! [B_224,A_225] : k5_xboole_0(k4_xboole_0(B_224,A_225),A_225) = k2_xboole_0(B_224,A_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_5106,c_833])).

tff(c_7233,plain,(
    ! [A_128,B_129] : k2_xboole_0(k1_tarski(A_128),k2_tarski(A_128,B_129)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_128,B_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_7125])).

tff(c_7281,plain,(
    ! [A_128,B_129] : k2_xboole_0(k1_tarski(A_128),k2_tarski(A_128,B_129)) = k2_tarski(A_128,B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_7233])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7281,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.62/3.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/3.19  
% 7.62/3.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/3.19  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.62/3.19  
% 7.62/3.19  %Foreground sorts:
% 7.62/3.19  
% 7.62/3.19  
% 7.62/3.19  %Background operators:
% 7.62/3.19  
% 7.62/3.19  
% 7.62/3.19  %Foreground operators:
% 7.62/3.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/3.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.62/3.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.62/3.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.62/3.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.62/3.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.62/3.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.62/3.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.62/3.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.62/3.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.62/3.19  tff('#skF_2', type, '#skF_2': $i).
% 7.62/3.19  tff('#skF_1', type, '#skF_1': $i).
% 7.62/3.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.62/3.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/3.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/3.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/3.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.62/3.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.62/3.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/3.19  
% 7.81/3.20  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.81/3.20  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.81/3.20  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.81/3.20  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.81/3.20  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.81/3.20  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.81/3.20  tff(f_69, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.81/3.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.81/3.20  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.81/3.20  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.81/3.20  tff(f_72, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.81/3.20  tff(c_120, plain, (![B_64, A_65]: (k5_xboole_0(B_64, A_65)=k5_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.81/3.20  tff(c_20, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.81/3.20  tff(c_136, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_120, c_20])).
% 7.81/3.20  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.81/3.20  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.81/3.20  tff(c_207, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.81/3.20  tff(c_218, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(resolution, [status(thm)], [c_22, c_207])).
% 7.81/3.20  tff(c_356, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.81/3.20  tff(c_372, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k5_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_218, c_356])).
% 7.81/3.20  tff(c_390, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_372])).
% 7.81/3.20  tff(c_42, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.81/3.20  tff(c_1197, plain, (![A_128, B_129]: (k3_xboole_0(k1_tarski(A_128), k2_tarski(A_128, B_129))=k1_tarski(A_128))), inference(resolution, [status(thm)], [c_42, c_207])).
% 7.81/3.20  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.81/3.20  tff(c_1206, plain, (![A_128, B_129]: (k5_xboole_0(k1_tarski(A_128), k1_tarski(A_128))=k4_xboole_0(k1_tarski(A_128), k2_tarski(A_128, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_1197, c_12])).
% 7.81/3.20  tff(c_1214, plain, (![A_128, B_129]: (k4_xboole_0(k1_tarski(A_128), k2_tarski(A_128, B_129))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_390, c_1206])).
% 7.81/3.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.81/3.20  tff(c_1121, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k3_xboole_0(B_127, A_126))=k4_xboole_0(A_126, B_127))), inference(superposition, [status(thm), theory('equality')], [c_2, c_356])).
% 7.81/3.20  tff(c_538, plain, (![A_90, B_91, C_92]: (k5_xboole_0(k5_xboole_0(A_90, B_91), C_92)=k5_xboole_0(A_90, k5_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.81/3.20  tff(c_575, plain, (![A_15, C_92]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_92))=k5_xboole_0(k1_xboole_0, C_92))), inference(superposition, [status(thm), theory('equality')], [c_390, c_538])).
% 7.81/3.20  tff(c_623, plain, (![A_15, C_92]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_92))=C_92)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_575])).
% 7.81/3.20  tff(c_1136, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k4_xboole_0(A_126, B_127))=k3_xboole_0(B_127, A_126))), inference(superposition, [status(thm), theory('equality')], [c_1121, c_623])).
% 7.81/3.20  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.81/3.20  tff(c_2110, plain, (![C_158, A_159, B_160]: (k5_xboole_0(C_158, k5_xboole_0(A_159, B_160))=k5_xboole_0(A_159, k5_xboole_0(B_160, C_158)))), inference(superposition, [status(thm), theory('equality')], [c_538, c_4])).
% 7.81/3.20  tff(c_2502, plain, (![A_161, C_162]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_161, C_162))=k5_xboole_0(C_162, A_161))), inference(superposition, [status(thm), theory('equality')], [c_136, c_2110])).
% 7.81/3.20  tff(c_2590, plain, (![A_126, B_127]: (k5_xboole_0(k4_xboole_0(A_126, B_127), A_126)=k5_xboole_0(k1_xboole_0, k3_xboole_0(B_127, A_126)))), inference(superposition, [status(thm), theory('equality')], [c_1136, c_2502])).
% 7.81/3.20  tff(c_2667, plain, (![A_126, B_127]: (k5_xboole_0(k4_xboole_0(A_126, B_127), A_126)=k3_xboole_0(B_127, A_126))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2590])).
% 7.81/3.20  tff(c_26, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.81/3.20  tff(c_4887, plain, (![A_194, B_195, C_196]: (k5_xboole_0(A_194, k5_xboole_0(k4_xboole_0(B_195, A_194), C_196))=k5_xboole_0(k2_xboole_0(A_194, B_195), C_196))), inference(superposition, [status(thm), theory('equality')], [c_26, c_538])).
% 7.81/3.20  tff(c_4967, plain, (![B_127, A_126]: (k5_xboole_0(k2_xboole_0(B_127, A_126), A_126)=k5_xboole_0(B_127, k3_xboole_0(B_127, A_126)))), inference(superposition, [status(thm), theory('equality')], [c_2667, c_4887])).
% 7.81/3.20  tff(c_5106, plain, (![B_197, A_198]: (k5_xboole_0(k2_xboole_0(B_197, A_198), A_198)=k4_xboole_0(B_197, A_198))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4967])).
% 7.81/3.20  tff(c_723, plain, (![A_100, C_101]: (k5_xboole_0(A_100, k5_xboole_0(A_100, C_101))=C_101)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_575])).
% 7.81/3.20  tff(c_800, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k5_xboole_0(B_108, A_107))=B_108)), inference(superposition, [status(thm), theory('equality')], [c_4, c_723])).
% 7.81/3.20  tff(c_833, plain, (![A_15, C_92]: (k5_xboole_0(k5_xboole_0(A_15, C_92), C_92)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_623, c_800])).
% 7.81/3.20  tff(c_7125, plain, (![B_224, A_225]: (k5_xboole_0(k4_xboole_0(B_224, A_225), A_225)=k2_xboole_0(B_224, A_225))), inference(superposition, [status(thm), theory('equality')], [c_5106, c_833])).
% 7.81/3.20  tff(c_7233, plain, (![A_128, B_129]: (k2_xboole_0(k1_tarski(A_128), k2_tarski(A_128, B_129))=k5_xboole_0(k1_xboole_0, k2_tarski(A_128, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_1214, c_7125])).
% 7.81/3.20  tff(c_7281, plain, (![A_128, B_129]: (k2_xboole_0(k1_tarski(A_128), k2_tarski(A_128, B_129))=k2_tarski(A_128, B_129))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_7233])).
% 7.81/3.20  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.81/3.20  tff(c_12108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7281, c_44])).
% 7.81/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/3.20  
% 7.81/3.20  Inference rules
% 7.81/3.20  ----------------------
% 7.81/3.20  #Ref     : 0
% 7.81/3.20  #Sup     : 3014
% 7.81/3.20  #Fact    : 0
% 7.81/3.20  #Define  : 0
% 7.81/3.20  #Split   : 0
% 7.81/3.20  #Chain   : 0
% 7.81/3.20  #Close   : 0
% 7.81/3.20  
% 7.81/3.20  Ordering : KBO
% 7.81/3.20  
% 7.81/3.20  Simplification rules
% 7.81/3.20  ----------------------
% 7.81/3.20  #Subsume      : 187
% 7.81/3.20  #Demod        : 3346
% 7.81/3.20  #Tautology    : 1697
% 7.81/3.21  #SimpNegUnit  : 0
% 7.81/3.21  #BackRed      : 1
% 7.81/3.21  
% 7.81/3.21  #Partial instantiations: 0
% 7.81/3.21  #Strategies tried      : 1
% 7.81/3.21  
% 7.81/3.21  Timing (in seconds)
% 7.81/3.21  ----------------------
% 7.81/3.21  Preprocessing        : 0.31
% 7.81/3.21  Parsing              : 0.17
% 7.81/3.21  CNF conversion       : 0.02
% 7.81/3.21  Main loop            : 2.13
% 7.81/3.21  Inferencing          : 0.52
% 7.81/3.21  Reduction            : 1.21
% 7.81/3.21  Demodulation         : 1.10
% 7.81/3.21  BG Simplification    : 0.06
% 7.81/3.21  Subsumption          : 0.24
% 7.81/3.21  Abstraction          : 0.11
% 7.81/3.21  MUC search           : 0.00
% 7.81/3.21  Cooper               : 0.00
% 7.81/3.21  Total                : 2.47
% 7.81/3.21  Index Insertion      : 0.00
% 7.81/3.21  Index Deletion       : 0.00
% 7.81/3.21  Index Matching       : 0.00
% 7.81/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
