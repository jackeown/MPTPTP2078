%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:07 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 146 expanded)
%              Number of leaves         :   31 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 ( 133 expanded)
%              Number of equality atoms :   51 ( 123 expanded)
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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

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

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_75,plain,(
    ! [B_56,A_57] : k5_xboole_0(B_56,A_57) = k5_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_57] : k5_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_20])).

tff(c_222,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_249,plain,(
    ! [B_68] : k3_xboole_0(k1_xboole_0,B_68) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_261,plain,(
    ! [B_68] : k3_xboole_0(B_68,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_2])).

tff(c_338,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_351,plain,(
    ! [B_68] : k5_xboole_0(B_68,k1_xboole_0) = k4_xboole_0(B_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_338])).

tff(c_407,plain,(
    ! [B_77] : k4_xboole_0(B_77,k1_xboole_0) = B_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_351])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_416,plain,(
    ! [B_77] : k4_xboole_0(B_77,B_77) = k3_xboole_0(B_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_16])).

tff(c_430,plain,(
    ! [B_77] : k4_xboole_0(B_77,B_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_416])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_204,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_212,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_204])).

tff(c_357,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_338])).

tff(c_526,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_357])).

tff(c_40,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1032,plain,(
    ! [A_105,B_106] : k3_xboole_0(k1_tarski(A_105),k2_tarski(A_105,B_106)) = k1_tarski(A_105) ),
    inference(resolution,[status(thm)],[c_40,c_204])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1038,plain,(
    ! [A_105,B_106] : k5_xboole_0(k1_tarski(A_105),k1_tarski(A_105)) = k4_xboole_0(k1_tarski(A_105),k2_tarski(A_105,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_12])).

tff(c_1046,plain,(
    ! [A_105,B_106] : k4_xboole_0(k1_tarski(A_105),k2_tarski(A_105,B_106)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_1038])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_554,plain,(
    ! [A_85,B_86,C_87] : k5_xboole_0(k5_xboole_0(A_85,B_86),C_87) = k5_xboole_0(A_85,k5_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3037,plain,(
    ! [C_171,A_172,B_173] : k5_xboole_0(C_171,k5_xboole_0(A_172,B_173)) = k5_xboole_0(A_172,k5_xboole_0(B_173,C_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_4])).

tff(c_3485,plain,(
    ! [A_174,C_175] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_174,C_175)) = k5_xboole_0(C_175,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_3037])).

tff(c_3617,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3485])).

tff(c_3793,plain,(
    ! [B_178,A_179] : k5_xboole_0(k4_xboole_0(B_178,A_179),A_179) = k2_xboole_0(A_179,B_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3617])).

tff(c_3875,plain,(
    ! [A_105,B_106] : k2_xboole_0(k2_tarski(A_105,B_106),k1_tarski(A_105)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_105,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_3793])).

tff(c_12666,plain,(
    ! [A_261,B_262] : k2_xboole_0(k2_tarski(A_261,B_262),k1_tarski(A_261)) = k2_tarski(A_261,B_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3875])).

tff(c_3671,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3617])).

tff(c_360,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_338])).

tff(c_3588,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_3485])).

tff(c_3663,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3588])).

tff(c_6691,plain,(
    ! [A_215,B_216,C_217] : k5_xboole_0(A_215,k5_xboole_0(k3_xboole_0(A_215,B_216),C_217)) = k5_xboole_0(k4_xboole_0(A_215,B_216),C_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_554])).

tff(c_6799,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3663,c_6691])).

tff(c_6931,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3671,c_24,c_6799])).

tff(c_12693,plain,(
    ! [A_261,B_262] : k2_xboole_0(k1_tarski(A_261),k2_tarski(A_261,B_262)) = k2_tarski(A_261,B_262) ),
    inference(superposition,[status(thm),theory(equality)],[c_12666,c_6931])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12693,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:56:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.57/3.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/3.04  
% 7.57/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/3.04  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.57/3.04  
% 7.57/3.04  %Foreground sorts:
% 7.57/3.04  
% 7.57/3.04  
% 7.57/3.04  %Background operators:
% 7.57/3.04  
% 7.57/3.04  
% 7.57/3.04  %Foreground operators:
% 7.57/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/3.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.57/3.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.57/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.57/3.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.57/3.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.57/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.57/3.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.57/3.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.57/3.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.57/3.04  tff('#skF_2', type, '#skF_2': $i).
% 7.57/3.04  tff('#skF_1', type, '#skF_1': $i).
% 7.57/3.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.57/3.04  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.57/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/3.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.57/3.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.57/3.04  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.57/3.04  
% 7.70/3.05  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.70/3.05  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.70/3.05  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.70/3.05  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 7.70/3.05  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.70/3.05  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.70/3.05  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.70/3.05  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.70/3.05  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.70/3.05  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.70/3.05  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.70/3.05  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.70/3.05  tff(c_75, plain, (![B_56, A_57]: (k5_xboole_0(B_56, A_57)=k5_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.70/3.05  tff(c_20, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.70/3.05  tff(c_91, plain, (![A_57]: (k5_xboole_0(k1_xboole_0, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_75, c_20])).
% 7.70/3.05  tff(c_222, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.70/3.05  tff(c_18, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.70/3.05  tff(c_249, plain, (![B_68]: (k3_xboole_0(k1_xboole_0, B_68)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_222, c_18])).
% 7.70/3.05  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.70/3.05  tff(c_261, plain, (![B_68]: (k3_xboole_0(B_68, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_249, c_2])).
% 7.70/3.05  tff(c_338, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.70/3.05  tff(c_351, plain, (![B_68]: (k5_xboole_0(B_68, k1_xboole_0)=k4_xboole_0(B_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_261, c_338])).
% 7.70/3.05  tff(c_407, plain, (![B_77]: (k4_xboole_0(B_77, k1_xboole_0)=B_77)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_351])).
% 7.70/3.05  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.70/3.05  tff(c_416, plain, (![B_77]: (k4_xboole_0(B_77, B_77)=k3_xboole_0(B_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_407, c_16])).
% 7.70/3.05  tff(c_430, plain, (![B_77]: (k4_xboole_0(B_77, B_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_261, c_416])).
% 7.70/3.05  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.70/3.05  tff(c_204, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.70/3.05  tff(c_212, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_204])).
% 7.70/3.05  tff(c_357, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_212, c_338])).
% 7.70/3.05  tff(c_526, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_430, c_357])).
% 7.70/3.05  tff(c_40, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.70/3.05  tff(c_1032, plain, (![A_105, B_106]: (k3_xboole_0(k1_tarski(A_105), k2_tarski(A_105, B_106))=k1_tarski(A_105))), inference(resolution, [status(thm)], [c_40, c_204])).
% 7.70/3.05  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.70/3.05  tff(c_1038, plain, (![A_105, B_106]: (k5_xboole_0(k1_tarski(A_105), k1_tarski(A_105))=k4_xboole_0(k1_tarski(A_105), k2_tarski(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_12])).
% 7.70/3.05  tff(c_1046, plain, (![A_105, B_106]: (k4_xboole_0(k1_tarski(A_105), k2_tarski(A_105, B_106))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_526, c_1038])).
% 7.70/3.05  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.70/3.05  tff(c_554, plain, (![A_85, B_86, C_87]: (k5_xboole_0(k5_xboole_0(A_85, B_86), C_87)=k5_xboole_0(A_85, k5_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.70/3.05  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.70/3.05  tff(c_3037, plain, (![C_171, A_172, B_173]: (k5_xboole_0(C_171, k5_xboole_0(A_172, B_173))=k5_xboole_0(A_172, k5_xboole_0(B_173, C_171)))), inference(superposition, [status(thm), theory('equality')], [c_554, c_4])).
% 7.70/3.05  tff(c_3485, plain, (![A_174, C_175]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_174, C_175))=k5_xboole_0(C_175, A_174))), inference(superposition, [status(thm), theory('equality')], [c_91, c_3037])).
% 7.70/3.05  tff(c_3617, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3485])).
% 7.70/3.05  tff(c_3793, plain, (![B_178, A_179]: (k5_xboole_0(k4_xboole_0(B_178, A_179), A_179)=k2_xboole_0(A_179, B_178))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_3617])).
% 7.70/3.05  tff(c_3875, plain, (![A_105, B_106]: (k2_xboole_0(k2_tarski(A_105, B_106), k1_tarski(A_105))=k5_xboole_0(k1_xboole_0, k2_tarski(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_1046, c_3793])).
% 7.70/3.05  tff(c_12666, plain, (![A_261, B_262]: (k2_xboole_0(k2_tarski(A_261, B_262), k1_tarski(A_261))=k2_tarski(A_261, B_262))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_3875])).
% 7.70/3.05  tff(c_3671, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_3617])).
% 7.70/3.05  tff(c_360, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_338])).
% 7.70/3.05  tff(c_3588, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_360, c_3485])).
% 7.70/3.05  tff(c_3663, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_3588])).
% 7.70/3.05  tff(c_6691, plain, (![A_215, B_216, C_217]: (k5_xboole_0(A_215, k5_xboole_0(k3_xboole_0(A_215, B_216), C_217))=k5_xboole_0(k4_xboole_0(A_215, B_216), C_217))), inference(superposition, [status(thm), theory('equality')], [c_12, c_554])).
% 7.70/3.05  tff(c_6799, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_3663, c_6691])).
% 7.70/3.06  tff(c_6931, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_3671, c_24, c_6799])).
% 7.70/3.06  tff(c_12693, plain, (![A_261, B_262]: (k2_xboole_0(k1_tarski(A_261), k2_tarski(A_261, B_262))=k2_tarski(A_261, B_262))), inference(superposition, [status(thm), theory('equality')], [c_12666, c_6931])).
% 7.70/3.06  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.70/3.06  tff(c_12737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12693, c_42])).
% 7.70/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/3.06  
% 7.70/3.06  Inference rules
% 7.70/3.06  ----------------------
% 7.70/3.06  #Ref     : 0
% 7.70/3.06  #Sup     : 3166
% 7.70/3.06  #Fact    : 0
% 7.70/3.06  #Define  : 0
% 7.70/3.06  #Split   : 0
% 7.70/3.06  #Chain   : 0
% 7.70/3.06  #Close   : 0
% 7.70/3.06  
% 7.70/3.06  Ordering : KBO
% 7.70/3.06  
% 7.70/3.06  Simplification rules
% 7.70/3.06  ----------------------
% 7.70/3.06  #Subsume      : 180
% 7.70/3.06  #Demod        : 3626
% 7.70/3.06  #Tautology    : 1856
% 7.70/3.06  #SimpNegUnit  : 0
% 7.70/3.06  #BackRed      : 1
% 7.70/3.06  
% 7.70/3.06  #Partial instantiations: 0
% 7.70/3.06  #Strategies tried      : 1
% 7.70/3.06  
% 7.70/3.06  Timing (in seconds)
% 7.70/3.06  ----------------------
% 7.70/3.06  Preprocessing        : 0.33
% 7.70/3.06  Parsing              : 0.17
% 7.70/3.06  CNF conversion       : 0.02
% 7.70/3.06  Main loop            : 1.95
% 7.70/3.06  Inferencing          : 0.44
% 7.70/3.06  Reduction            : 1.16
% 7.70/3.06  Demodulation         : 1.05
% 7.70/3.06  BG Simplification    : 0.06
% 7.70/3.06  Subsumption          : 0.22
% 7.70/3.06  Abstraction          : 0.10
% 7.70/3.06  MUC search           : 0.00
% 7.70/3.06  Cooper               : 0.00
% 7.70/3.06  Total                : 2.31
% 7.70/3.06  Index Insertion      : 0.00
% 7.70/3.06  Index Deletion       : 0.00
% 7.70/3.06  Index Matching       : 0.00
% 7.70/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
