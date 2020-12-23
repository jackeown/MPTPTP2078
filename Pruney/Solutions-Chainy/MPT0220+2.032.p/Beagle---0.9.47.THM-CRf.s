%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:08 EST 2020

% Result     : Theorem 13.39s
% Output     : CNFRefutation 13.51s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 122 expanded)
%              Number of leaves         :   32 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 107 expanded)
%              Number of equality atoms :   51 (  98 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [B_63,A_64] : k5_xboole_0(B_63,A_64) = k5_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_16])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_467,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k4_xboole_0(B_82,A_81)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_499,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k2_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_467])).

tff(c_505,plain,(
    ! [A_83] : k2_xboole_0(k1_xboole_0,A_83) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_499])).

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

tff(c_539,plain,(
    ! [A_88] : k3_xboole_0(k1_xboole_0,A_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_216])).

tff(c_572,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_539])).

tff(c_235,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_250,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_302,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_276])).

tff(c_305,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_302])).

tff(c_769,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_305])).

tff(c_38,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1340,plain,(
    ! [A_129,B_130] : k3_xboole_0(k1_tarski(A_129),k2_tarski(A_129,B_130)) = k1_tarski(A_129) ),
    inference(resolution,[status(thm)],[c_38,c_203])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1346,plain,(
    ! [A_129,B_130] : k5_xboole_0(k1_tarski(A_129),k1_tarski(A_129)) = k4_xboole_0(k1_tarski(A_129),k2_tarski(A_129,B_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_8])).

tff(c_1357,plain,(
    ! [A_131,B_132] : k4_xboole_0(k1_tarski(A_131),k2_tarski(A_131,B_132)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_1346])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1362,plain,(
    ! [A_131,B_132] : k2_xboole_0(k2_tarski(A_131,B_132),k1_tarski(A_131)) = k5_xboole_0(k2_tarski(A_131,B_132),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_22])).

tff(c_19248,plain,(
    ! [A_336,B_337] : k2_xboole_0(k2_tarski(A_336,B_337),k1_tarski(A_336)) = k2_tarski(A_336,B_337) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1362])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_671,plain,(
    ! [A_91,B_92,C_93] : k5_xboole_0(k5_xboole_0(A_91,B_92),C_93) = k5_xboole_0(A_91,k5_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1457,plain,(
    ! [B_135,A_136,B_137] : k5_xboole_0(B_135,k5_xboole_0(A_136,B_137)) = k5_xboole_0(A_136,k5_xboole_0(B_137,B_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_671])).

tff(c_1832,plain,(
    ! [A_140,B_141] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_140,B_141)) = k5_xboole_0(B_141,A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1457])).

tff(c_1928,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1832])).

tff(c_1971,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k2_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1928])).

tff(c_299,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_276])).

tff(c_1899,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_1832])).

tff(c_1963,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1899])).

tff(c_6383,plain,(
    ! [A_224,B_225,C_226] : k5_xboole_0(A_224,k5_xboole_0(k3_xboole_0(A_224,B_225),C_226)) = k5_xboole_0(k4_xboole_0(A_224,B_225),C_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_671])).

tff(c_6495,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_6383])).

tff(c_6600,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_22,c_6495])).

tff(c_19338,plain,(
    ! [A_336,B_337] : k2_xboole_0(k1_tarski(A_336),k2_tarski(A_336,B_337)) = k2_tarski(A_336,B_337) ),
    inference(superposition,[status(thm),theory(equality)],[c_19248,c_6600])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_19428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19338,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.39/6.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.51/6.44  
% 13.51/6.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.51/6.45  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 13.51/6.45  
% 13.51/6.45  %Foreground sorts:
% 13.51/6.45  
% 13.51/6.45  
% 13.51/6.45  %Background operators:
% 13.51/6.45  
% 13.51/6.45  
% 13.51/6.45  %Foreground operators:
% 13.51/6.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.51/6.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.51/6.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.51/6.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.51/6.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.51/6.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.51/6.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.51/6.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.51/6.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.51/6.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.51/6.45  tff('#skF_2', type, '#skF_2': $i).
% 13.51/6.45  tff('#skF_1', type, '#skF_1': $i).
% 13.51/6.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.51/6.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.51/6.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.51/6.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.51/6.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.51/6.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.51/6.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.51/6.45  
% 13.51/6.47  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.51/6.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.51/6.47  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.51/6.47  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 13.51/6.47  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.51/6.47  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.51/6.47  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.51/6.47  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.51/6.47  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 13.51/6.47  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.51/6.47  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 13.51/6.47  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.51/6.47  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 13.51/6.47  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.51/6.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.51/6.47  tff(c_116, plain, (![B_63, A_64]: (k5_xboole_0(B_63, A_64)=k5_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.51/6.47  tff(c_132, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_116, c_16])).
% 13.51/6.47  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.51/6.47  tff(c_467, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k4_xboole_0(B_82, A_81))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.51/6.47  tff(c_499, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k2_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_467])).
% 13.51/6.47  tff(c_505, plain, (![A_83]: (k2_xboole_0(k1_xboole_0, A_83)=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_499])).
% 13.51/6.47  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.51/6.47  tff(c_203, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.51/6.47  tff(c_216, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(resolution, [status(thm)], [c_18, c_203])).
% 13.51/6.47  tff(c_539, plain, (![A_88]: (k3_xboole_0(k1_xboole_0, A_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_505, c_216])).
% 13.51/6.47  tff(c_572, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_539])).
% 13.51/6.47  tff(c_235, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.51/6.47  tff(c_250, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_235])).
% 13.51/6.47  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.51/6.47  tff(c_276, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.51/6.47  tff(c_302, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_276])).
% 13.51/6.47  tff(c_305, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_302])).
% 13.51/6.47  tff(c_769, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_572, c_305])).
% 13.51/6.47  tff(c_38, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.51/6.47  tff(c_1340, plain, (![A_129, B_130]: (k3_xboole_0(k1_tarski(A_129), k2_tarski(A_129, B_130))=k1_tarski(A_129))), inference(resolution, [status(thm)], [c_38, c_203])).
% 13.51/6.47  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.51/6.47  tff(c_1346, plain, (![A_129, B_130]: (k5_xboole_0(k1_tarski(A_129), k1_tarski(A_129))=k4_xboole_0(k1_tarski(A_129), k2_tarski(A_129, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_1340, c_8])).
% 13.51/6.47  tff(c_1357, plain, (![A_131, B_132]: (k4_xboole_0(k1_tarski(A_131), k2_tarski(A_131, B_132))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_769, c_1346])).
% 13.51/6.47  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.51/6.47  tff(c_1362, plain, (![A_131, B_132]: (k2_xboole_0(k2_tarski(A_131, B_132), k1_tarski(A_131))=k5_xboole_0(k2_tarski(A_131, B_132), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1357, c_22])).
% 13.51/6.47  tff(c_19248, plain, (![A_336, B_337]: (k2_xboole_0(k2_tarski(A_336, B_337), k1_tarski(A_336))=k2_tarski(A_336, B_337))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1362])).
% 13.51/6.47  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.51/6.47  tff(c_671, plain, (![A_91, B_92, C_93]: (k5_xboole_0(k5_xboole_0(A_91, B_92), C_93)=k5_xboole_0(A_91, k5_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.51/6.47  tff(c_1457, plain, (![B_135, A_136, B_137]: (k5_xboole_0(B_135, k5_xboole_0(A_136, B_137))=k5_xboole_0(A_136, k5_xboole_0(B_137, B_135)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_671])).
% 13.51/6.47  tff(c_1832, plain, (![A_140, B_141]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_140, B_141))=k5_xboole_0(B_141, A_140))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1457])).
% 13.51/6.47  tff(c_1928, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1832])).
% 13.51/6.47  tff(c_1971, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k2_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1928])).
% 13.51/6.47  tff(c_299, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_276])).
% 13.51/6.47  tff(c_1899, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_299, c_1832])).
% 13.51/6.47  tff(c_1963, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1899])).
% 13.51/6.47  tff(c_6383, plain, (![A_224, B_225, C_226]: (k5_xboole_0(A_224, k5_xboole_0(k3_xboole_0(A_224, B_225), C_226))=k5_xboole_0(k4_xboole_0(A_224, B_225), C_226))), inference(superposition, [status(thm), theory('equality')], [c_8, c_671])).
% 13.51/6.47  tff(c_6495, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_1963, c_6383])).
% 13.51/6.47  tff(c_6600, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_22, c_6495])).
% 13.51/6.47  tff(c_19338, plain, (![A_336, B_337]: (k2_xboole_0(k1_tarski(A_336), k2_tarski(A_336, B_337))=k2_tarski(A_336, B_337))), inference(superposition, [status(thm), theory('equality')], [c_19248, c_6600])).
% 13.51/6.47  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.51/6.47  tff(c_19428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19338, c_40])).
% 13.51/6.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.51/6.47  
% 13.51/6.47  Inference rules
% 13.51/6.47  ----------------------
% 13.51/6.47  #Ref     : 0
% 13.51/6.47  #Sup     : 4829
% 13.51/6.47  #Fact    : 0
% 13.51/6.47  #Define  : 0
% 13.51/6.47  #Split   : 0
% 13.51/6.47  #Chain   : 0
% 13.51/6.47  #Close   : 0
% 13.51/6.47  
% 13.51/6.47  Ordering : KBO
% 13.51/6.47  
% 13.51/6.47  Simplification rules
% 13.51/6.47  ----------------------
% 13.51/6.47  #Subsume      : 254
% 13.51/6.47  #Demod        : 5928
% 13.51/6.47  #Tautology    : 3085
% 13.51/6.47  #SimpNegUnit  : 0
% 13.51/6.47  #BackRed      : 7
% 13.51/6.47  
% 13.51/6.47  #Partial instantiations: 0
% 13.51/6.47  #Strategies tried      : 1
% 13.51/6.47  
% 13.51/6.47  Timing (in seconds)
% 13.51/6.47  ----------------------
% 13.51/6.48  Preprocessing        : 0.49
% 13.51/6.48  Parsing              : 0.25
% 13.51/6.48  CNF conversion       : 0.03
% 13.51/6.48  Main loop            : 5.06
% 13.51/6.48  Inferencing          : 0.99
% 13.51/6.48  Reduction            : 3.07
% 13.51/6.48  Demodulation         : 2.79
% 13.51/6.48  BG Simplification    : 0.15
% 13.51/6.48  Subsumption          : 0.61
% 13.51/6.48  Abstraction          : 0.22
% 13.51/6.48  MUC search           : 0.00
% 13.51/6.48  Cooper               : 0.00
% 13.51/6.48  Total                : 5.60
% 13.51/6.48  Index Insertion      : 0.00
% 13.51/6.48  Index Deletion       : 0.00
% 13.51/6.48  Index Matching       : 0.00
% 13.51/6.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
