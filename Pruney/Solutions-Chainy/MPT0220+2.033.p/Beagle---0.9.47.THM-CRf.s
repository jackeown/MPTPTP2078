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
% DateTime   : Thu Dec  3 09:48:08 EST 2020

% Result     : Theorem 11.16s
% Output     : CNFRefutation 11.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 155 expanded)
%              Number of leaves         :   31 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :   57 ( 138 expanded)
%              Number of equality atoms :   52 ( 133 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_111,plain,(
    ! [B_59,A_60] : k5_xboole_0(B_59,A_60) = k5_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [A_60] : k5_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_217,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_224,plain,(
    ! [B_67] : k4_xboole_0(k1_xboole_0,B_67) = k3_xboole_0(k1_xboole_0,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_127])).

tff(c_245,plain,(
    ! [B_68] : k3_xboole_0(k1_xboole_0,B_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_224])).

tff(c_266,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_245])).

tff(c_281,plain,(
    ! [B_69] : k3_xboole_0(B_69,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_245])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_289,plain,(
    ! [B_69] : k5_xboole_0(B_69,k1_xboole_0) = k4_xboole_0(B_69,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_8])).

tff(c_360,plain,(
    ! [B_72] : k4_xboole_0(B_72,k1_xboole_0) = B_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_289])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_366,plain,(
    ! [B_72] : k4_xboole_0(B_72,B_72) = k3_xboole_0(B_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_12])).

tff(c_379,plain,(
    ! [B_72] : k4_xboole_0(B_72,B_72) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_366])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_240,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_217])).

tff(c_514,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_240])).

tff(c_36,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_207,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_591,plain,(
    ! [A_85,B_86] : k3_xboole_0(k1_tarski(A_85),k2_tarski(A_85,B_86)) = k1_tarski(A_85) ),
    inference(resolution,[status(thm)],[c_36,c_207])).

tff(c_600,plain,(
    ! [A_85,B_86] : k5_xboole_0(k1_tarski(A_85),k1_tarski(A_85)) = k4_xboole_0(k1_tarski(A_85),k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_8])).

tff(c_608,plain,(
    ! [A_85,B_86] : k4_xboole_0(k1_tarski(A_85),k2_tarski(A_85,B_86)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_600])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_611,plain,(
    ! [A_87,B_88,C_89] : k5_xboole_0(k5_xboole_0(A_87,B_88),C_89) = k5_xboole_0(A_87,k5_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2303,plain,(
    ! [B_156,A_157,B_158] : k5_xboole_0(B_156,k5_xboole_0(A_157,B_158)) = k5_xboole_0(A_157,k5_xboole_0(B_158,B_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_611])).

tff(c_2677,plain,(
    ! [A_159,B_160] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_159,B_160)) = k5_xboole_0(B_160,A_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_2303])).

tff(c_2791,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2677])).

tff(c_2952,plain,(
    ! [B_163,A_164] : k5_xboole_0(k4_xboole_0(B_163,A_164),A_164) = k2_xboole_0(A_164,B_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2791])).

tff(c_3023,plain,(
    ! [A_85,B_86] : k2_xboole_0(k2_tarski(A_85,B_86),k1_tarski(A_85)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_2952])).

tff(c_12655,plain,(
    ! [A_257,B_258] : k2_xboole_0(k2_tarski(A_257,B_258),k1_tarski(A_257)) = k2_tarski(A_257,B_258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_3023])).

tff(c_2840,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2791])).

tff(c_237,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_2785,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_2677])).

tff(c_2838,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2785])).

tff(c_5494,plain,(
    ! [A_196,B_197,C_198] : k5_xboole_0(A_196,k5_xboole_0(k3_xboole_0(A_196,B_197),C_198)) = k5_xboole_0(k4_xboole_0(A_196,B_197),C_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_611])).

tff(c_5592,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2838,c_5494])).

tff(c_5711,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2840,c_20,c_5592])).

tff(c_12685,plain,(
    ! [A_257,B_258] : k2_xboole_0(k1_tarski(A_257),k2_tarski(A_257,B_258)) = k2_tarski(A_257,B_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_12655,c_5711])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12685,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.16/5.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.16/5.07  
% 11.16/5.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.16/5.07  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 11.16/5.07  
% 11.16/5.07  %Foreground sorts:
% 11.16/5.07  
% 11.16/5.07  
% 11.16/5.07  %Background operators:
% 11.16/5.07  
% 11.16/5.07  
% 11.16/5.07  %Foreground operators:
% 11.16/5.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.16/5.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.16/5.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.16/5.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.16/5.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.16/5.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.16/5.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.16/5.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.16/5.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.16/5.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.16/5.07  tff('#skF_2', type, '#skF_2': $i).
% 11.16/5.07  tff('#skF_1', type, '#skF_1': $i).
% 11.16/5.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.16/5.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.16/5.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.16/5.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.16/5.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.16/5.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.16/5.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.16/5.07  
% 11.20/5.09  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.20/5.09  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 11.20/5.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.20/5.09  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 11.20/5.09  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.20/5.09  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.20/5.09  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.20/5.09  tff(f_63, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 11.20/5.09  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.20/5.09  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.20/5.09  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.20/5.09  tff(f_66, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 11.20/5.09  tff(c_111, plain, (![B_59, A_60]: (k5_xboole_0(B_59, A_60)=k5_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.20/5.09  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.20/5.09  tff(c_127, plain, (![A_60]: (k5_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_111, c_16])).
% 11.20/5.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.20/5.09  tff(c_14, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.20/5.09  tff(c_217, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.20/5.09  tff(c_224, plain, (![B_67]: (k4_xboole_0(k1_xboole_0, B_67)=k3_xboole_0(k1_xboole_0, B_67))), inference(superposition, [status(thm), theory('equality')], [c_217, c_127])).
% 11.20/5.09  tff(c_245, plain, (![B_68]: (k3_xboole_0(k1_xboole_0, B_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_224])).
% 11.20/5.09  tff(c_266, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_245])).
% 11.20/5.09  tff(c_281, plain, (![B_69]: (k3_xboole_0(B_69, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_245])).
% 11.20/5.09  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.20/5.09  tff(c_289, plain, (![B_69]: (k5_xboole_0(B_69, k1_xboole_0)=k4_xboole_0(B_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_281, c_8])).
% 11.20/5.09  tff(c_360, plain, (![B_72]: (k4_xboole_0(B_72, k1_xboole_0)=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_289])).
% 11.20/5.09  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.20/5.09  tff(c_366, plain, (![B_72]: (k4_xboole_0(B_72, B_72)=k3_xboole_0(B_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_360, c_12])).
% 11.20/5.09  tff(c_379, plain, (![B_72]: (k4_xboole_0(B_72, B_72)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_266, c_366])).
% 11.20/5.09  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.20/5.09  tff(c_240, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_217])).
% 11.20/5.09  tff(c_514, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_379, c_240])).
% 11.20/5.09  tff(c_36, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.20/5.09  tff(c_207, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.20/5.09  tff(c_591, plain, (![A_85, B_86]: (k3_xboole_0(k1_tarski(A_85), k2_tarski(A_85, B_86))=k1_tarski(A_85))), inference(resolution, [status(thm)], [c_36, c_207])).
% 11.20/5.09  tff(c_600, plain, (![A_85, B_86]: (k5_xboole_0(k1_tarski(A_85), k1_tarski(A_85))=k4_xboole_0(k1_tarski(A_85), k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_591, c_8])).
% 11.20/5.09  tff(c_608, plain, (![A_85, B_86]: (k4_xboole_0(k1_tarski(A_85), k2_tarski(A_85, B_86))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_514, c_600])).
% 11.20/5.09  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.20/5.09  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.20/5.09  tff(c_611, plain, (![A_87, B_88, C_89]: (k5_xboole_0(k5_xboole_0(A_87, B_88), C_89)=k5_xboole_0(A_87, k5_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.20/5.09  tff(c_2303, plain, (![B_156, A_157, B_158]: (k5_xboole_0(B_156, k5_xboole_0(A_157, B_158))=k5_xboole_0(A_157, k5_xboole_0(B_158, B_156)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_611])).
% 11.20/5.09  tff(c_2677, plain, (![A_159, B_160]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_159, B_160))=k5_xboole_0(B_160, A_159))), inference(superposition, [status(thm), theory('equality')], [c_127, c_2303])).
% 11.20/5.09  tff(c_2791, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2677])).
% 11.20/5.09  tff(c_2952, plain, (![B_163, A_164]: (k5_xboole_0(k4_xboole_0(B_163, A_164), A_164)=k2_xboole_0(A_164, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2791])).
% 11.20/5.09  tff(c_3023, plain, (![A_85, B_86]: (k2_xboole_0(k2_tarski(A_85, B_86), k1_tarski(A_85))=k5_xboole_0(k1_xboole_0, k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_608, c_2952])).
% 11.20/5.09  tff(c_12655, plain, (![A_257, B_258]: (k2_xboole_0(k2_tarski(A_257, B_258), k1_tarski(A_257))=k2_tarski(A_257, B_258))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_3023])).
% 11.20/5.09  tff(c_2840, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2791])).
% 11.20/5.09  tff(c_237, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_217])).
% 11.20/5.09  tff(c_2785, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_237, c_2677])).
% 11.20/5.09  tff(c_2838, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2785])).
% 11.20/5.09  tff(c_5494, plain, (![A_196, B_197, C_198]: (k5_xboole_0(A_196, k5_xboole_0(k3_xboole_0(A_196, B_197), C_198))=k5_xboole_0(k4_xboole_0(A_196, B_197), C_198))), inference(superposition, [status(thm), theory('equality')], [c_8, c_611])).
% 11.20/5.09  tff(c_5592, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2838, c_5494])).
% 11.20/5.09  tff(c_5711, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2840, c_20, c_5592])).
% 11.20/5.09  tff(c_12685, plain, (![A_257, B_258]: (k2_xboole_0(k1_tarski(A_257), k2_tarski(A_257, B_258))=k2_tarski(A_257, B_258))), inference(superposition, [status(thm), theory('equality')], [c_12655, c_5711])).
% 11.20/5.09  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.20/5.09  tff(c_12726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12685, c_38])).
% 11.20/5.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.20/5.09  
% 11.20/5.09  Inference rules
% 11.20/5.09  ----------------------
% 11.20/5.09  #Ref     : 0
% 11.20/5.09  #Sup     : 3163
% 11.20/5.09  #Fact    : 0
% 11.20/5.09  #Define  : 0
% 11.20/5.09  #Split   : 0
% 11.20/5.09  #Chain   : 0
% 11.20/5.09  #Close   : 0
% 11.20/5.09  
% 11.20/5.09  Ordering : KBO
% 11.20/5.09  
% 11.20/5.09  Simplification rules
% 11.20/5.09  ----------------------
% 11.20/5.09  #Subsume      : 176
% 11.20/5.09  #Demod        : 3618
% 11.20/5.09  #Tautology    : 1853
% 11.20/5.09  #SimpNegUnit  : 0
% 11.20/5.09  #BackRed      : 1
% 11.20/5.09  
% 11.20/5.10  #Partial instantiations: 0
% 11.20/5.10  #Strategies tried      : 1
% 11.20/5.10  
% 11.20/5.10  Timing (in seconds)
% 11.20/5.10  ----------------------
% 11.20/5.10  Preprocessing        : 0.52
% 11.20/5.10  Parsing              : 0.27
% 11.20/5.10  CNF conversion       : 0.04
% 11.20/5.10  Main loop            : 3.74
% 11.20/5.10  Inferencing          : 0.77
% 11.20/5.10  Reduction            : 2.25
% 11.20/5.10  Demodulation         : 2.05
% 11.20/5.10  BG Simplification    : 0.13
% 11.20/5.10  Subsumption          : 0.41
% 11.20/5.10  Abstraction          : 0.17
% 11.20/5.10  MUC search           : 0.00
% 11.20/5.10  Cooper               : 0.00
% 11.20/5.10  Total                : 4.31
% 11.20/5.10  Index Insertion      : 0.00
% 11.20/5.10  Index Deletion       : 0.00
% 11.20/5.10  Index Matching       : 0.00
% 11.20/5.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
