%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:59 EST 2020

% Result     : Theorem 5.85s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 313 expanded)
%              Number of leaves         :   38 ( 121 expanded)
%              Depth                    :   17
%              Number of atoms          :   84 ( 340 expanded)
%              Number of equality atoms :   60 ( 260 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_58,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k2_xboole_0(A_73,B_74)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_99,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_355,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k4_xboole_0(B_108,A_107)) = k2_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_370,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_355])).

tff(c_376,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_370])).

tff(c_52,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_275,plain,(
    ! [A_101,B_102] :
      ( k4_xboole_0(A_101,B_102) = k1_xboole_0
      | ~ r1_tarski(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1302,plain,(
    ! [A_164,B_165] :
      ( k4_xboole_0(k1_tarski(A_164),B_165) = k1_xboole_0
      | ~ r2_hidden(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_52,c_275])).

tff(c_34,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1321,plain,(
    ! [B_165,A_164] :
      ( k2_xboole_0(B_165,k1_tarski(A_164)) = k5_xboole_0(B_165,k1_xboole_0)
      | ~ r2_hidden(A_164,B_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_34])).

tff(c_1349,plain,(
    ! [B_165,A_164] :
      ( k2_xboole_0(B_165,k1_tarski(A_164)) = B_165
      | ~ r2_hidden(A_164,B_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_1321])).

tff(c_26,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_20,B_21] : k3_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_474,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k3_xboole_0(A_113,B_114)) = k4_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_489,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k5_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_474])).

tff(c_495,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_489])).

tff(c_751,plain,(
    ! [A_131,B_132,C_133] : k5_xboole_0(k5_xboole_0(A_131,B_132),C_133) = k5_xboole_0(A_131,k5_xboole_0(B_132,C_133)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3720,plain,(
    ! [A_231,B_232,C_233] : k5_xboole_0(A_231,k5_xboole_0(k4_xboole_0(B_232,A_231),C_233)) = k5_xboole_0(k2_xboole_0(A_231,B_232),C_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_751])).

tff(c_3812,plain,(
    ! [A_231,B_232] : k5_xboole_0(k2_xboole_0(A_231,B_232),k4_xboole_0(B_232,A_231)) = k5_xboole_0(A_231,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_3720])).

tff(c_3851,plain,(
    ! [A_234,B_235] : k5_xboole_0(k2_xboole_0(A_234,B_235),k4_xboole_0(B_235,A_234)) = A_234 ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_3812])).

tff(c_786,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k5_xboole_0(B_132,k5_xboole_0(A_131,B_132))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_751])).

tff(c_30,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_516,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_xboole_0(A_116,B_117)
      | ~ r2_hidden(C_118,k3_xboole_0(A_116,B_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_547,plain,(
    ! [A_122,B_123] :
      ( ~ r1_xboole_0(A_122,B_123)
      | k3_xboole_0(A_122,B_123) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_516])).

tff(c_551,plain,(
    ! [A_28] : k3_xboole_0(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_547])).

tff(c_552,plain,(
    ! [A_124] : k3_xboole_0(A_124,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_547])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_560,plain,(
    ! [A_124] : k5_xboole_0(A_124,k1_xboole_0) = k4_xboole_0(A_124,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_18])).

tff(c_705,plain,(
    ! [A_130] : k4_xboole_0(A_130,k1_xboole_0) = A_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_560])).

tff(c_28,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_711,plain,(
    ! [A_130] : k2_xboole_0(k3_xboole_0(A_130,k1_xboole_0),A_130) = A_130 ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_28])).

tff(c_743,plain,(
    ! [A_130] : k2_xboole_0(k1_xboole_0,A_130) = A_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_711])).

tff(c_714,plain,(
    ! [A_130] : k5_xboole_0(k1_xboole_0,A_130) = k2_xboole_0(k1_xboole_0,A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_34])).

tff(c_949,plain,(
    ! [A_130] : k5_xboole_0(k1_xboole_0,A_130) = A_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_714])).

tff(c_782,plain,(
    ! [A_20,C_133] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_133)) = k5_xboole_0(k1_xboole_0,C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_751])).

tff(c_2410,plain,(
    ! [A_207,C_208] : k5_xboole_0(A_207,k5_xboole_0(A_207,C_208)) = C_208 ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_782])).

tff(c_2447,plain,(
    ! [B_132,A_131] : k5_xboole_0(B_132,k5_xboole_0(A_131,B_132)) = k5_xboole_0(A_131,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_2410])).

tff(c_2491,plain,(
    ! [B_132,A_131] : k5_xboole_0(B_132,k5_xboole_0(A_131,B_132)) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_2447])).

tff(c_3863,plain,(
    ! [B_235,A_234] : k5_xboole_0(k4_xboole_0(B_235,A_234),A_234) = k2_xboole_0(A_234,B_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_3851,c_2491])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4548,plain,(
    ! [A_244,B_245,C_246] : k5_xboole_0(A_244,k5_xboole_0(k3_xboole_0(A_244,B_245),C_246)) = k5_xboole_0(k4_xboole_0(A_244,B_245),C_246) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_751])).

tff(c_4669,plain,(
    ! [A_244,B_245] : k5_xboole_0(k4_xboole_0(A_244,B_245),k3_xboole_0(A_244,B_245)) = k5_xboole_0(A_244,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_4548])).

tff(c_4714,plain,(
    ! [A_247,B_248] : k5_xboole_0(k4_xboole_0(A_247,B_248),k3_xboole_0(A_247,B_248)) = A_247 ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_4669])).

tff(c_4851,plain,(
    ! [A_249,B_250] : k5_xboole_0(k4_xboole_0(A_249,B_250),k3_xboole_0(B_250,A_249)) = A_249 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4714])).

tff(c_7964,plain,(
    ! [B_295,A_296] : k5_xboole_0(k3_xboole_0(B_295,A_296),A_296) = k4_xboole_0(A_296,B_295) ),
    inference(superposition,[status(thm),theory(equality)],[c_4851,c_2491])).

tff(c_789,plain,(
    ! [A_16,B_17,C_133] : k5_xboole_0(A_16,k5_xboole_0(k3_xboole_0(A_16,B_17),C_133)) = k5_xboole_0(k4_xboole_0(A_16,B_17),C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_751])).

tff(c_7984,plain,(
    ! [B_295,A_296] : k5_xboole_0(k4_xboole_0(B_295,A_296),A_296) = k5_xboole_0(B_295,k4_xboole_0(A_296,B_295)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7964,c_789])).

tff(c_8089,plain,(
    ! [B_295,A_296] : k2_xboole_0(B_295,A_296) = k2_xboole_0(A_296,B_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3863,c_34,c_7984])).

tff(c_56,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8119,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_56])).

tff(c_8341,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_8119])).

tff(c_8345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:07:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.85/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.23  
% 5.85/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.85/2.24  
% 5.85/2.24  %Foreground sorts:
% 5.85/2.24  
% 5.85/2.24  
% 5.85/2.24  %Background operators:
% 5.85/2.24  
% 5.85/2.24  
% 5.85/2.24  %Foreground operators:
% 5.85/2.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.85/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.85/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.85/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.85/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.85/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.85/2.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.85/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.85/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.85/2.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.85/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.85/2.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.85/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.85/2.24  tff('#skF_3', type, '#skF_3': $i).
% 5.85/2.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.85/2.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.85/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.85/2.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.85/2.24  tff('#skF_4', type, '#skF_4': $i).
% 5.85/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.85/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.85/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.85/2.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.85/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.85/2.24  
% 5.85/2.25  tff(f_102, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 5.85/2.25  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.85/2.25  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.85/2.25  tff(f_77, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.85/2.25  tff(f_95, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.85/2.25  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.85/2.25  tff(f_63, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.85/2.25  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.85/2.25  tff(f_75, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.85/2.25  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.85/2.25  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.85/2.25  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.85/2.25  tff(f_71, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.85/2.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.85/2.25  tff(c_58, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.85/2.25  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.85/2.25  tff(c_92, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k2_xboole_0(A_73, B_74))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.85/2.25  tff(c_99, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_92])).
% 5.85/2.25  tff(c_355, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k4_xboole_0(B_108, A_107))=k2_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.85/2.25  tff(c_370, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_99, c_355])).
% 5.85/2.25  tff(c_376, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_370])).
% 5.85/2.25  tff(c_52, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.85/2.25  tff(c_275, plain, (![A_101, B_102]: (k4_xboole_0(A_101, B_102)=k1_xboole_0 | ~r1_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.85/2.25  tff(c_1302, plain, (![A_164, B_165]: (k4_xboole_0(k1_tarski(A_164), B_165)=k1_xboole_0 | ~r2_hidden(A_164, B_165))), inference(resolution, [status(thm)], [c_52, c_275])).
% 5.85/2.25  tff(c_34, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.85/2.25  tff(c_1321, plain, (![B_165, A_164]: (k2_xboole_0(B_165, k1_tarski(A_164))=k5_xboole_0(B_165, k1_xboole_0) | ~r2_hidden(A_164, B_165))), inference(superposition, [status(thm), theory('equality')], [c_1302, c_34])).
% 5.85/2.25  tff(c_1349, plain, (![B_165, A_164]: (k2_xboole_0(B_165, k1_tarski(A_164))=B_165 | ~r2_hidden(A_164, B_165))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_1321])).
% 5.85/2.25  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.85/2.25  tff(c_22, plain, (![A_20, B_21]: (k3_xboole_0(A_20, k2_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.85/2.25  tff(c_474, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k3_xboole_0(A_113, B_114))=k4_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.85/2.25  tff(c_489, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k5_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_22, c_474])).
% 5.85/2.25  tff(c_495, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_489])).
% 5.85/2.25  tff(c_751, plain, (![A_131, B_132, C_133]: (k5_xboole_0(k5_xboole_0(A_131, B_132), C_133)=k5_xboole_0(A_131, k5_xboole_0(B_132, C_133)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.85/2.25  tff(c_3720, plain, (![A_231, B_232, C_233]: (k5_xboole_0(A_231, k5_xboole_0(k4_xboole_0(B_232, A_231), C_233))=k5_xboole_0(k2_xboole_0(A_231, B_232), C_233))), inference(superposition, [status(thm), theory('equality')], [c_34, c_751])).
% 5.85/2.25  tff(c_3812, plain, (![A_231, B_232]: (k5_xboole_0(k2_xboole_0(A_231, B_232), k4_xboole_0(B_232, A_231))=k5_xboole_0(A_231, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_495, c_3720])).
% 5.85/2.25  tff(c_3851, plain, (![A_234, B_235]: (k5_xboole_0(k2_xboole_0(A_234, B_235), k4_xboole_0(B_235, A_234))=A_234)), inference(demodulation, [status(thm), theory('equality')], [c_376, c_3812])).
% 5.85/2.25  tff(c_786, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k5_xboole_0(B_132, k5_xboole_0(A_131, B_132)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_495, c_751])).
% 5.85/2.25  tff(c_30, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.85/2.25  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.85/2.25  tff(c_516, plain, (![A_116, B_117, C_118]: (~r1_xboole_0(A_116, B_117) | ~r2_hidden(C_118, k3_xboole_0(A_116, B_117)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.85/2.25  tff(c_547, plain, (![A_122, B_123]: (~r1_xboole_0(A_122, B_123) | k3_xboole_0(A_122, B_123)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_516])).
% 5.85/2.25  tff(c_551, plain, (![A_28]: (k3_xboole_0(A_28, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_547])).
% 5.85/2.25  tff(c_552, plain, (![A_124]: (k3_xboole_0(A_124, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_547])).
% 5.85/2.25  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.85/2.25  tff(c_560, plain, (![A_124]: (k5_xboole_0(A_124, k1_xboole_0)=k4_xboole_0(A_124, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_552, c_18])).
% 5.85/2.25  tff(c_705, plain, (![A_130]: (k4_xboole_0(A_130, k1_xboole_0)=A_130)), inference(demodulation, [status(thm), theory('equality')], [c_376, c_560])).
% 5.85/2.25  tff(c_28, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.85/2.25  tff(c_711, plain, (![A_130]: (k2_xboole_0(k3_xboole_0(A_130, k1_xboole_0), A_130)=A_130)), inference(superposition, [status(thm), theory('equality')], [c_705, c_28])).
% 5.85/2.25  tff(c_743, plain, (![A_130]: (k2_xboole_0(k1_xboole_0, A_130)=A_130)), inference(demodulation, [status(thm), theory('equality')], [c_551, c_711])).
% 5.85/2.25  tff(c_714, plain, (![A_130]: (k5_xboole_0(k1_xboole_0, A_130)=k2_xboole_0(k1_xboole_0, A_130))), inference(superposition, [status(thm), theory('equality')], [c_705, c_34])).
% 5.85/2.25  tff(c_949, plain, (![A_130]: (k5_xboole_0(k1_xboole_0, A_130)=A_130)), inference(demodulation, [status(thm), theory('equality')], [c_743, c_714])).
% 5.85/2.25  tff(c_782, plain, (![A_20, C_133]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_133))=k5_xboole_0(k1_xboole_0, C_133))), inference(superposition, [status(thm), theory('equality')], [c_495, c_751])).
% 5.85/2.25  tff(c_2410, plain, (![A_207, C_208]: (k5_xboole_0(A_207, k5_xboole_0(A_207, C_208))=C_208)), inference(demodulation, [status(thm), theory('equality')], [c_949, c_782])).
% 5.85/2.25  tff(c_2447, plain, (![B_132, A_131]: (k5_xboole_0(B_132, k5_xboole_0(A_131, B_132))=k5_xboole_0(A_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_786, c_2410])).
% 5.85/2.25  tff(c_2491, plain, (![B_132, A_131]: (k5_xboole_0(B_132, k5_xboole_0(A_131, B_132))=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_376, c_2447])).
% 5.85/2.25  tff(c_3863, plain, (![B_235, A_234]: (k5_xboole_0(k4_xboole_0(B_235, A_234), A_234)=k2_xboole_0(A_234, B_235))), inference(superposition, [status(thm), theory('equality')], [c_3851, c_2491])).
% 5.85/2.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.85/2.25  tff(c_4548, plain, (![A_244, B_245, C_246]: (k5_xboole_0(A_244, k5_xboole_0(k3_xboole_0(A_244, B_245), C_246))=k5_xboole_0(k4_xboole_0(A_244, B_245), C_246))), inference(superposition, [status(thm), theory('equality')], [c_18, c_751])).
% 5.85/2.25  tff(c_4669, plain, (![A_244, B_245]: (k5_xboole_0(k4_xboole_0(A_244, B_245), k3_xboole_0(A_244, B_245))=k5_xboole_0(A_244, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_495, c_4548])).
% 5.85/2.25  tff(c_4714, plain, (![A_247, B_248]: (k5_xboole_0(k4_xboole_0(A_247, B_248), k3_xboole_0(A_247, B_248))=A_247)), inference(demodulation, [status(thm), theory('equality')], [c_376, c_4669])).
% 5.85/2.25  tff(c_4851, plain, (![A_249, B_250]: (k5_xboole_0(k4_xboole_0(A_249, B_250), k3_xboole_0(B_250, A_249))=A_249)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4714])).
% 5.85/2.25  tff(c_7964, plain, (![B_295, A_296]: (k5_xboole_0(k3_xboole_0(B_295, A_296), A_296)=k4_xboole_0(A_296, B_295))), inference(superposition, [status(thm), theory('equality')], [c_4851, c_2491])).
% 5.85/2.25  tff(c_789, plain, (![A_16, B_17, C_133]: (k5_xboole_0(A_16, k5_xboole_0(k3_xboole_0(A_16, B_17), C_133))=k5_xboole_0(k4_xboole_0(A_16, B_17), C_133))), inference(superposition, [status(thm), theory('equality')], [c_18, c_751])).
% 5.85/2.25  tff(c_7984, plain, (![B_295, A_296]: (k5_xboole_0(k4_xboole_0(B_295, A_296), A_296)=k5_xboole_0(B_295, k4_xboole_0(A_296, B_295)))), inference(superposition, [status(thm), theory('equality')], [c_7964, c_789])).
% 5.85/2.25  tff(c_8089, plain, (![B_295, A_296]: (k2_xboole_0(B_295, A_296)=k2_xboole_0(A_296, B_295))), inference(demodulation, [status(thm), theory('equality')], [c_3863, c_34, c_7984])).
% 5.85/2.25  tff(c_56, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.85/2.25  tff(c_8119, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_56])).
% 5.85/2.25  tff(c_8341, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1349, c_8119])).
% 5.85/2.25  tff(c_8345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_8341])).
% 5.85/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.25  
% 5.85/2.25  Inference rules
% 5.85/2.25  ----------------------
% 5.85/2.25  #Ref     : 0
% 5.85/2.25  #Sup     : 2044
% 5.85/2.25  #Fact    : 0
% 5.85/2.25  #Define  : 0
% 5.85/2.25  #Split   : 0
% 5.85/2.25  #Chain   : 0
% 5.85/2.25  #Close   : 0
% 5.85/2.25  
% 5.85/2.25  Ordering : KBO
% 5.85/2.25  
% 5.85/2.25  Simplification rules
% 5.85/2.25  ----------------------
% 5.85/2.25  #Subsume      : 158
% 5.85/2.25  #Demod        : 2090
% 5.85/2.25  #Tautology    : 1299
% 5.85/2.25  #SimpNegUnit  : 12
% 5.85/2.25  #BackRed      : 2
% 5.85/2.25  
% 5.85/2.25  #Partial instantiations: 0
% 5.85/2.25  #Strategies tried      : 1
% 5.85/2.25  
% 5.85/2.25  Timing (in seconds)
% 5.85/2.25  ----------------------
% 5.85/2.26  Preprocessing        : 0.34
% 5.85/2.26  Parsing              : 0.19
% 5.85/2.26  CNF conversion       : 0.02
% 5.85/2.26  Main loop            : 1.14
% 5.85/2.26  Inferencing          : 0.35
% 5.85/2.26  Reduction            : 0.52
% 5.85/2.26  Demodulation         : 0.44
% 5.85/2.26  BG Simplification    : 0.04
% 5.85/2.26  Subsumption          : 0.16
% 5.85/2.26  Abstraction          : 0.06
% 5.85/2.26  MUC search           : 0.00
% 5.85/2.26  Cooper               : 0.00
% 5.85/2.26  Total                : 1.51
% 5.85/2.26  Index Insertion      : 0.00
% 5.85/2.26  Index Deletion       : 0.00
% 5.85/2.26  Index Matching       : 0.00
% 5.85/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
