%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:06 EST 2020

% Result     : Theorem 8.33s
% Output     : CNFRefutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 143 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 ( 132 expanded)
%              Number of equality atoms :   49 ( 118 expanded)
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

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

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

tff(c_69,plain,(
    ! [B_56,A_57] : k5_xboole_0(B_56,A_57) = k5_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,(
    ! [A_57] : k5_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_20])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_538,plain,(
    ! [A_86,B_87,C_88] : k5_xboole_0(k5_xboole_0(A_86,B_87),C_88) = k5_xboole_0(A_86,k5_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2290,plain,(
    ! [A_157,A_155,B_156] : k5_xboole_0(A_157,k5_xboole_0(A_155,B_156)) = k5_xboole_0(A_155,k5_xboole_0(B_156,A_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_538])).

tff(c_2714,plain,(
    ! [A_158,A_159] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_158,A_159)) = k5_xboole_0(A_159,A_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2290])).

tff(c_2843,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2714])).

tff(c_2896,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2843])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_330,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_352,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_330])).

tff(c_2814,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_2714])).

tff(c_2888,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2814])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4498,plain,(
    ! [A_182,B_183,C_184] : k5_xboole_0(A_182,k5_xboole_0(k3_xboole_0(A_182,B_183),C_184)) = k5_xboole_0(k4_xboole_0(A_182,B_183),C_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_538])).

tff(c_4580,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2888,c_4498])).

tff(c_4709,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2896,c_24,c_4580])).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_196,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_208,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_196])).

tff(c_337,plain,(
    ! [B_74] : k4_xboole_0(k1_xboole_0,B_74) = k3_xboole_0(k1_xboole_0,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_85])).

tff(c_361,plain,(
    ! [B_74] : k4_xboole_0(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_337])).

tff(c_381,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_394,plain,(
    ! [B_74] : k5_xboole_0(B_74,k1_xboole_0) = k2_xboole_0(B_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_381])).

tff(c_408,plain,(
    ! [B_78] : k2_xboole_0(B_78,k1_xboole_0) = B_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_394])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_414,plain,(
    ! [B_78] : k4_xboole_0(B_78,B_78) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_18])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_207,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_196])).

tff(c_349,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_330])).

tff(c_615,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_349])).

tff(c_40,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1054,plain,(
    ! [A_113,B_114] : k3_xboole_0(k1_tarski(A_113),k2_tarski(A_113,B_114)) = k1_tarski(A_113) ),
    inference(resolution,[status(thm)],[c_40,c_196])).

tff(c_1060,plain,(
    ! [A_113,B_114] : k5_xboole_0(k1_tarski(A_113),k1_tarski(A_113)) = k4_xboole_0(k1_tarski(A_113),k2_tarski(A_113,B_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_12])).

tff(c_1068,plain,(
    ! [A_113,B_114] : k4_xboole_0(k1_tarski(A_113),k2_tarski(A_113,B_114)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_1060])).

tff(c_3021,plain,(
    ! [B_162,A_163] : k5_xboole_0(k4_xboole_0(B_162,A_163),A_163) = k2_xboole_0(A_163,B_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2843])).

tff(c_3083,plain,(
    ! [A_113,B_114] : k2_xboole_0(k2_tarski(A_113,B_114),k1_tarski(A_113)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_113,B_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_3021])).

tff(c_12578,plain,(
    ! [A_257,B_258] : k2_xboole_0(k2_tarski(A_257,B_258),k1_tarski(A_257)) = k2_tarski(A_257,B_258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3083])).

tff(c_12686,plain,(
    ! [A_257,B_258] : k2_xboole_0(k1_tarski(A_257),k2_tarski(A_257,B_258)) = k2_tarski(A_257,B_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_4709,c_12578])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12686,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:52:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.33/3.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/3.42  
% 8.33/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.53/3.42  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.53/3.42  
% 8.53/3.42  %Foreground sorts:
% 8.53/3.42  
% 8.53/3.42  
% 8.53/3.42  %Background operators:
% 8.53/3.42  
% 8.53/3.42  
% 8.53/3.42  %Foreground operators:
% 8.53/3.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.53/3.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.53/3.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.53/3.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.53/3.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.53/3.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.53/3.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.53/3.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.53/3.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.53/3.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.53/3.42  tff('#skF_2', type, '#skF_2': $i).
% 8.53/3.42  tff('#skF_1', type, '#skF_1': $i).
% 8.53/3.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.53/3.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.53/3.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.53/3.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.53/3.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.53/3.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.53/3.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.53/3.42  
% 8.53/3.44  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.53/3.44  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.53/3.44  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.53/3.44  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.53/3.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.53/3.44  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.53/3.44  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.53/3.44  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.53/3.44  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.53/3.44  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.53/3.44  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.53/3.44  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 8.53/3.44  tff(c_69, plain, (![B_56, A_57]: (k5_xboole_0(B_56, A_57)=k5_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.53/3.44  tff(c_20, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.53/3.44  tff(c_85, plain, (![A_57]: (k5_xboole_0(k1_xboole_0, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_69, c_20])).
% 8.53/3.44  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.53/3.44  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.53/3.44  tff(c_538, plain, (![A_86, B_87, C_88]: (k5_xboole_0(k5_xboole_0(A_86, B_87), C_88)=k5_xboole_0(A_86, k5_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.53/3.44  tff(c_2290, plain, (![A_157, A_155, B_156]: (k5_xboole_0(A_157, k5_xboole_0(A_155, B_156))=k5_xboole_0(A_155, k5_xboole_0(B_156, A_157)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_538])).
% 8.53/3.44  tff(c_2714, plain, (![A_158, A_159]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_158, A_159))=k5_xboole_0(A_159, A_158))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2290])).
% 8.53/3.44  tff(c_2843, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2714])).
% 8.53/3.44  tff(c_2896, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2843])).
% 8.53/3.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.53/3.44  tff(c_330, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.53/3.44  tff(c_352, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_330])).
% 8.53/3.44  tff(c_2814, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_352, c_2714])).
% 8.53/3.44  tff(c_2888, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2814])).
% 8.53/3.44  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.53/3.44  tff(c_4498, plain, (![A_182, B_183, C_184]: (k5_xboole_0(A_182, k5_xboole_0(k3_xboole_0(A_182, B_183), C_184))=k5_xboole_0(k4_xboole_0(A_182, B_183), C_184))), inference(superposition, [status(thm), theory('equality')], [c_12, c_538])).
% 8.53/3.44  tff(c_4580, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2888, c_4498])).
% 8.53/3.44  tff(c_4709, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2896, c_24, c_4580])).
% 8.53/3.44  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.53/3.44  tff(c_196, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.53/3.44  tff(c_208, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_196])).
% 8.53/3.44  tff(c_337, plain, (![B_74]: (k4_xboole_0(k1_xboole_0, B_74)=k3_xboole_0(k1_xboole_0, B_74))), inference(superposition, [status(thm), theory('equality')], [c_330, c_85])).
% 8.53/3.44  tff(c_361, plain, (![B_74]: (k4_xboole_0(k1_xboole_0, B_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_337])).
% 8.53/3.44  tff(c_381, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.53/3.44  tff(c_394, plain, (![B_74]: (k5_xboole_0(B_74, k1_xboole_0)=k2_xboole_0(B_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_361, c_381])).
% 8.53/3.44  tff(c_408, plain, (![B_78]: (k2_xboole_0(B_78, k1_xboole_0)=B_78)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_394])).
% 8.53/3.44  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.53/3.44  tff(c_414, plain, (![B_78]: (k4_xboole_0(B_78, B_78)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_408, c_18])).
% 8.53/3.44  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.53/3.44  tff(c_207, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_196])).
% 8.53/3.44  tff(c_349, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_207, c_330])).
% 8.53/3.44  tff(c_615, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_414, c_349])).
% 8.53/3.44  tff(c_40, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.53/3.44  tff(c_1054, plain, (![A_113, B_114]: (k3_xboole_0(k1_tarski(A_113), k2_tarski(A_113, B_114))=k1_tarski(A_113))), inference(resolution, [status(thm)], [c_40, c_196])).
% 8.53/3.44  tff(c_1060, plain, (![A_113, B_114]: (k5_xboole_0(k1_tarski(A_113), k1_tarski(A_113))=k4_xboole_0(k1_tarski(A_113), k2_tarski(A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_1054, c_12])).
% 8.53/3.44  tff(c_1068, plain, (![A_113, B_114]: (k4_xboole_0(k1_tarski(A_113), k2_tarski(A_113, B_114))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_615, c_1060])).
% 8.53/3.44  tff(c_3021, plain, (![B_162, A_163]: (k5_xboole_0(k4_xboole_0(B_162, A_163), A_163)=k2_xboole_0(A_163, B_162))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2843])).
% 8.53/3.44  tff(c_3083, plain, (![A_113, B_114]: (k2_xboole_0(k2_tarski(A_113, B_114), k1_tarski(A_113))=k5_xboole_0(k1_xboole_0, k2_tarski(A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_3021])).
% 8.53/3.44  tff(c_12578, plain, (![A_257, B_258]: (k2_xboole_0(k2_tarski(A_257, B_258), k1_tarski(A_257))=k2_tarski(A_257, B_258))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_3083])).
% 8.53/3.44  tff(c_12686, plain, (![A_257, B_258]: (k2_xboole_0(k1_tarski(A_257), k2_tarski(A_257, B_258))=k2_tarski(A_257, B_258))), inference(superposition, [status(thm), theory('equality')], [c_4709, c_12578])).
% 8.53/3.44  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.53/3.44  tff(c_12720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12686, c_42])).
% 8.53/3.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.53/3.44  
% 8.53/3.44  Inference rules
% 8.53/3.44  ----------------------
% 8.53/3.44  #Ref     : 0
% 8.53/3.44  #Sup     : 3182
% 8.53/3.44  #Fact    : 0
% 8.53/3.44  #Define  : 0
% 8.53/3.44  #Split   : 0
% 8.53/3.44  #Chain   : 0
% 8.53/3.44  #Close   : 0
% 8.53/3.44  
% 8.53/3.44  Ordering : KBO
% 8.53/3.44  
% 8.53/3.44  Simplification rules
% 8.53/3.44  ----------------------
% 8.53/3.44  #Subsume      : 201
% 8.53/3.44  #Demod        : 3430
% 8.53/3.44  #Tautology    : 1656
% 8.53/3.44  #SimpNegUnit  : 0
% 8.53/3.44  #BackRed      : 1
% 8.53/3.44  
% 8.53/3.44  #Partial instantiations: 0
% 8.53/3.44  #Strategies tried      : 1
% 8.53/3.44  
% 8.53/3.44  Timing (in seconds)
% 8.53/3.44  ----------------------
% 8.53/3.44  Preprocessing        : 0.34
% 8.53/3.44  Parsing              : 0.18
% 8.53/3.44  CNF conversion       : 0.02
% 8.53/3.44  Main loop            : 2.32
% 8.53/3.44  Inferencing          : 0.48
% 8.53/3.44  Reduction            : 1.42
% 8.53/3.45  Demodulation         : 1.30
% 8.53/3.45  BG Simplification    : 0.07
% 8.53/3.45  Subsumption          : 0.26
% 8.53/3.45  Abstraction          : 0.11
% 8.53/3.45  MUC search           : 0.00
% 8.53/3.45  Cooper               : 0.00
% 8.53/3.45  Total                : 2.69
% 8.53/3.45  Index Insertion      : 0.00
% 8.53/3.45  Index Deletion       : 0.00
% 8.53/3.45  Index Matching       : 0.00
% 8.53/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
