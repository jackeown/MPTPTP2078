%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:27 EST 2020

% Result     : Theorem 8.94s
% Output     : CNFRefutation 9.36s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 297 expanded)
%              Number of leaves         :   34 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 440 expanded)
%              Number of equality atoms :   73 ( 311 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_71,axiom,(
    ! [A,B,C,D] : k4_xboole_0(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A,C),B),k2_zfmisc_1(A,k4_xboole_0(B,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(c_36,plain,(
    ! [B_43] : k2_zfmisc_1(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3325,plain,(
    ! [A_240,B_241] : k5_xboole_0(A_240,k3_xboole_0(A_240,B_241)) = k4_xboole_0(A_240,B_241) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3340,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3325])).

tff(c_3348,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3340])).

tff(c_144,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | k4_xboole_0(A_70,B_71) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_156,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_106])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_130,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = k1_xboole_0
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_130])).

tff(c_2436,plain,(
    ! [A_204,C_205,B_206,D_207] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_204,C_205),B_206),k2_zfmisc_1(A_204,k4_xboole_0(B_206,D_207))) = k4_xboole_0(k2_zfmisc_1(A_204,B_206),k2_zfmisc_1(C_205,D_207)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2948,plain,(
    ! [A_221,C_222,B_223,D_224] : k3_xboole_0(k2_zfmisc_1(k4_xboole_0(A_221,C_222),B_223),k4_xboole_0(k2_zfmisc_1(A_221,B_223),k2_zfmisc_1(C_222,D_224))) = k2_zfmisc_1(k4_xboole_0(A_221,C_222),B_223) ),
    inference(superposition,[status(thm),theory(equality)],[c_2436,c_10])).

tff(c_3032,plain,(
    k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2'),k1_xboole_0) = k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2948])).

tff(c_3072,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3032])).

tff(c_32,plain,(
    ! [B_43,A_42] :
      ( k1_xboole_0 = B_43
      | k1_xboole_0 = A_42
      | k2_zfmisc_1(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3128,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3072,c_32])).

tff(c_3147,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_3128])).

tff(c_34,plain,(
    ! [A_42] : k2_zfmisc_1(A_42,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3176,plain,(
    ! [A_42] : k2_zfmisc_1(A_42,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3147,c_3147,c_34])).

tff(c_48,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3178,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3147,c_48])).

tff(c_3245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3176,c_3178])).

tff(c_3247,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3257,plain,(
    ! [A_228,B_229] :
      ( k3_xboole_0(A_228,B_229) = A_228
      | ~ r1_tarski(A_228,B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3261,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3247,c_3257])).

tff(c_5343,plain,(
    ! [A_342,C_343,B_344,D_345] : k3_xboole_0(k2_zfmisc_1(A_342,C_343),k2_zfmisc_1(B_344,D_345)) = k2_zfmisc_1(k3_xboole_0(A_342,B_344),k3_xboole_0(C_343,D_345)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3278,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_12])).

tff(c_5349,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5343,c_3278])).

tff(c_5386,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3261,c_5349])).

tff(c_40,plain,(
    ! [A_48,C_50,B_49] : k4_xboole_0(k2_zfmisc_1(A_48,C_50),k2_zfmisc_1(B_49,C_50)) = k2_zfmisc_1(k4_xboole_0(A_48,B_49),C_50) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5459,plain,(
    ! [B_348] : k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_348,k3_xboole_0('#skF_2','#skF_4'))) = k2_zfmisc_1(k4_xboole_0('#skF_1',B_348),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5386,c_40])).

tff(c_42,plain,(
    ! [C_50,A_48,B_49] : k4_xboole_0(k2_zfmisc_1(C_50,A_48),k2_zfmisc_1(C_50,B_49)) = k2_zfmisc_1(C_50,k4_xboole_0(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5466,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_1'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5459,c_42])).

tff(c_5489,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_4'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3348,c_5466])).

tff(c_5529,plain,
    ( k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5489,c_32])).

tff(c_5532,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5529])).

tff(c_5553,plain,(
    ! [B_43] : k2_zfmisc_1('#skF_1',B_43) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5532,c_5532,c_36])).

tff(c_5554,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5532,c_48])).

tff(c_5633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_5554])).

tff(c_5635,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5529])).

tff(c_3301,plain,(
    ! [A_236,B_237] :
      ( r1_tarski(A_236,B_237)
      | k4_xboole_0(A_236,B_237) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3246,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3313,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3301,c_3246])).

tff(c_6121,plain,(
    ! [A_377,C_378,B_379,D_380] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_377,C_378),B_379),k2_zfmisc_1(A_377,k4_xboole_0(B_379,D_380))) = k4_xboole_0(k2_zfmisc_1(A_377,B_379),k2_zfmisc_1(C_378,D_380)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6224,plain,(
    ! [A_1,B_379,D_380] : k4_xboole_0(k2_zfmisc_1(A_1,B_379),k2_zfmisc_1(A_1,D_380)) = k2_xboole_0(k2_zfmisc_1(k1_xboole_0,B_379),k2_zfmisc_1(A_1,k4_xboole_0(B_379,D_380))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3348,c_6121])).

tff(c_6265,plain,(
    ! [A_1,B_379,D_380] : k2_xboole_0(k1_xboole_0,k2_zfmisc_1(A_1,k4_xboole_0(B_379,D_380))) = k2_zfmisc_1(A_1,k4_xboole_0(B_379,D_380)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42,c_6224])).

tff(c_3288,plain,(
    ! [A_234,B_235] :
      ( k4_xboole_0(A_234,B_235) = k1_xboole_0
      | ~ r1_tarski(A_234,B_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3296,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3247,c_3288])).

tff(c_6230,plain,(
    ! [B_379,D_380] : k2_xboole_0(k2_zfmisc_1(k1_xboole_0,B_379),k2_zfmisc_1('#skF_1',k4_xboole_0(B_379,D_380))) = k4_xboole_0(k2_zfmisc_1('#skF_1',B_379),k2_zfmisc_1('#skF_3',D_380)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3296,c_6121])).

tff(c_6267,plain,(
    ! [B_379,D_380] : k4_xboole_0(k2_zfmisc_1('#skF_1',B_379),k2_zfmisc_1('#skF_3',D_380)) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1('#skF_1',k4_xboole_0(B_379,D_380))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6230])).

tff(c_12161,plain,(
    ! [B_3199,D_3200] : k4_xboole_0(k2_zfmisc_1('#skF_1',B_3199),k2_zfmisc_1('#skF_3',D_3200)) = k2_zfmisc_1('#skF_1',k4_xboole_0(B_3199,D_3200)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6265,c_6267])).

tff(c_3295,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_3288])).

tff(c_12272,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12161,c_3295])).

tff(c_12460,plain,
    ( k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12272,c_32])).

tff(c_12492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5635,c_3313,c_12460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.94/3.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.94/3.40  
% 8.94/3.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.94/3.40  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.94/3.40  
% 8.94/3.40  %Foreground sorts:
% 8.94/3.40  
% 8.94/3.40  
% 8.94/3.40  %Background operators:
% 8.94/3.40  
% 8.94/3.40  
% 8.94/3.40  %Foreground operators:
% 8.94/3.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.94/3.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.94/3.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.94/3.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.94/3.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.94/3.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.94/3.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.94/3.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.94/3.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.94/3.40  tff('#skF_2', type, '#skF_2': $i).
% 8.94/3.40  tff('#skF_3', type, '#skF_3': $i).
% 8.94/3.40  tff('#skF_1', type, '#skF_1': $i).
% 8.94/3.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.94/3.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.94/3.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.94/3.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.94/3.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.94/3.40  tff('#skF_4', type, '#skF_4': $i).
% 8.94/3.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.94/3.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.94/3.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.94/3.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.94/3.40  
% 9.36/3.41  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.36/3.41  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.36/3.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.36/3.41  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.36/3.41  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.36/3.41  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 9.36/3.41  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.36/3.41  tff(f_71, axiom, (![A, B, C, D]: (k4_xboole_0(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A, C), B), k2_zfmisc_1(A, k4_xboole_0(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_zfmisc_1)).
% 9.36/3.41  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 9.36/3.41  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.36/3.41  tff(f_65, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 9.36/3.41  tff(f_69, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 9.36/3.41  tff(c_36, plain, (![B_43]: (k2_zfmisc_1(k1_xboole_0, B_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.36/3.41  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.36/3.41  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.36/3.41  tff(c_3325, plain, (![A_240, B_241]: (k5_xboole_0(A_240, k3_xboole_0(A_240, B_241))=k4_xboole_0(A_240, B_241))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.36/3.41  tff(c_3340, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3325])).
% 9.36/3.41  tff(c_3348, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3340])).
% 9.36/3.41  tff(c_144, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | k4_xboole_0(A_70, B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.36/3.41  tff(c_46, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.36/3.41  tff(c_106, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 9.36/3.41  tff(c_156, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_106])).
% 9.36/3.41  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.36/3.41  tff(c_50, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.36/3.41  tff(c_130, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=k1_xboole_0 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.36/3.41  tff(c_134, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_130])).
% 9.36/3.41  tff(c_2436, plain, (![A_204, C_205, B_206, D_207]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_204, C_205), B_206), k2_zfmisc_1(A_204, k4_xboole_0(B_206, D_207)))=k4_xboole_0(k2_zfmisc_1(A_204, B_206), k2_zfmisc_1(C_205, D_207)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.36/3.41  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.36/3.41  tff(c_2948, plain, (![A_221, C_222, B_223, D_224]: (k3_xboole_0(k2_zfmisc_1(k4_xboole_0(A_221, C_222), B_223), k4_xboole_0(k2_zfmisc_1(A_221, B_223), k2_zfmisc_1(C_222, D_224)))=k2_zfmisc_1(k4_xboole_0(A_221, C_222), B_223))), inference(superposition, [status(thm), theory('equality')], [c_2436, c_10])).
% 9.36/3.41  tff(c_3032, plain, (k3_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'), k1_xboole_0)=k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_134, c_2948])).
% 9.36/3.41  tff(c_3072, plain, (k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3032])).
% 9.36/3.41  tff(c_32, plain, (![B_43, A_42]: (k1_xboole_0=B_43 | k1_xboole_0=A_42 | k2_zfmisc_1(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.36/3.41  tff(c_3128, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3072, c_32])).
% 9.36/3.41  tff(c_3147, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_156, c_3128])).
% 9.36/3.41  tff(c_34, plain, (![A_42]: (k2_zfmisc_1(A_42, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.36/3.41  tff(c_3176, plain, (![A_42]: (k2_zfmisc_1(A_42, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3147, c_3147, c_34])).
% 9.36/3.41  tff(c_48, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.36/3.41  tff(c_3178, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3147, c_48])).
% 9.36/3.41  tff(c_3245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3176, c_3178])).
% 9.36/3.41  tff(c_3247, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 9.36/3.41  tff(c_3257, plain, (![A_228, B_229]: (k3_xboole_0(A_228, B_229)=A_228 | ~r1_tarski(A_228, B_229))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.36/3.41  tff(c_3261, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_3247, c_3257])).
% 9.36/3.41  tff(c_5343, plain, (![A_342, C_343, B_344, D_345]: (k3_xboole_0(k2_zfmisc_1(A_342, C_343), k2_zfmisc_1(B_344, D_345))=k2_zfmisc_1(k3_xboole_0(A_342, B_344), k3_xboole_0(C_343, D_345)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.36/3.41  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.36/3.41  tff(c_3278, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_12])).
% 9.36/3.41  tff(c_5349, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5343, c_3278])).
% 9.36/3.41  tff(c_5386, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3261, c_5349])).
% 9.36/3.41  tff(c_40, plain, (![A_48, C_50, B_49]: (k4_xboole_0(k2_zfmisc_1(A_48, C_50), k2_zfmisc_1(B_49, C_50))=k2_zfmisc_1(k4_xboole_0(A_48, B_49), C_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.36/3.41  tff(c_5459, plain, (![B_348]: (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_348, k3_xboole_0('#skF_2', '#skF_4')))=k2_zfmisc_1(k4_xboole_0('#skF_1', B_348), k3_xboole_0('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5386, c_40])).
% 9.36/3.41  tff(c_42, plain, (![C_50, A_48, B_49]: (k4_xboole_0(k2_zfmisc_1(C_50, A_48), k2_zfmisc_1(C_50, B_49))=k2_zfmisc_1(C_50, k4_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.36/3.41  tff(c_5466, plain, (k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_1'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5459, c_42])).
% 9.36/3.41  tff(c_5489, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_4')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3348, c_5466])).
% 9.36/3.41  tff(c_5529, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5489, c_32])).
% 9.36/3.41  tff(c_5532, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_5529])).
% 9.36/3.41  tff(c_5553, plain, (![B_43]: (k2_zfmisc_1('#skF_1', B_43)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5532, c_5532, c_36])).
% 9.36/3.41  tff(c_5554, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5532, c_48])).
% 9.36/3.41  tff(c_5633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5553, c_5554])).
% 9.36/3.41  tff(c_5635, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_5529])).
% 9.36/3.41  tff(c_3301, plain, (![A_236, B_237]: (r1_tarski(A_236, B_237) | k4_xboole_0(A_236, B_237)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.36/3.41  tff(c_3246, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 9.36/3.41  tff(c_3313, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3301, c_3246])).
% 9.36/3.41  tff(c_6121, plain, (![A_377, C_378, B_379, D_380]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_377, C_378), B_379), k2_zfmisc_1(A_377, k4_xboole_0(B_379, D_380)))=k4_xboole_0(k2_zfmisc_1(A_377, B_379), k2_zfmisc_1(C_378, D_380)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.36/3.41  tff(c_6224, plain, (![A_1, B_379, D_380]: (k4_xboole_0(k2_zfmisc_1(A_1, B_379), k2_zfmisc_1(A_1, D_380))=k2_xboole_0(k2_zfmisc_1(k1_xboole_0, B_379), k2_zfmisc_1(A_1, k4_xboole_0(B_379, D_380))))), inference(superposition, [status(thm), theory('equality')], [c_3348, c_6121])).
% 9.36/3.41  tff(c_6265, plain, (![A_1, B_379, D_380]: (k2_xboole_0(k1_xboole_0, k2_zfmisc_1(A_1, k4_xboole_0(B_379, D_380)))=k2_zfmisc_1(A_1, k4_xboole_0(B_379, D_380)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_42, c_6224])).
% 9.36/3.41  tff(c_3288, plain, (![A_234, B_235]: (k4_xboole_0(A_234, B_235)=k1_xboole_0 | ~r1_tarski(A_234, B_235))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.36/3.41  tff(c_3296, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3247, c_3288])).
% 9.36/3.41  tff(c_6230, plain, (![B_379, D_380]: (k2_xboole_0(k2_zfmisc_1(k1_xboole_0, B_379), k2_zfmisc_1('#skF_1', k4_xboole_0(B_379, D_380)))=k4_xboole_0(k2_zfmisc_1('#skF_1', B_379), k2_zfmisc_1('#skF_3', D_380)))), inference(superposition, [status(thm), theory('equality')], [c_3296, c_6121])).
% 9.36/3.41  tff(c_6267, plain, (![B_379, D_380]: (k4_xboole_0(k2_zfmisc_1('#skF_1', B_379), k2_zfmisc_1('#skF_3', D_380))=k2_xboole_0(k1_xboole_0, k2_zfmisc_1('#skF_1', k4_xboole_0(B_379, D_380))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6230])).
% 9.36/3.41  tff(c_12161, plain, (![B_3199, D_3200]: (k4_xboole_0(k2_zfmisc_1('#skF_1', B_3199), k2_zfmisc_1('#skF_3', D_3200))=k2_zfmisc_1('#skF_1', k4_xboole_0(B_3199, D_3200)))), inference(demodulation, [status(thm), theory('equality')], [c_6265, c_6267])).
% 9.36/3.41  tff(c_3295, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_3288])).
% 9.36/3.41  tff(c_12272, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12161, c_3295])).
% 9.36/3.41  tff(c_12460, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12272, c_32])).
% 9.36/3.41  tff(c_12492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5635, c_3313, c_12460])).
% 9.36/3.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.36/3.41  
% 9.36/3.41  Inference rules
% 9.36/3.41  ----------------------
% 9.36/3.41  #Ref     : 0
% 9.36/3.41  #Sup     : 3118
% 9.36/3.41  #Fact    : 0
% 9.36/3.41  #Define  : 0
% 9.36/3.41  #Split   : 6
% 9.36/3.41  #Chain   : 0
% 9.36/3.41  #Close   : 0
% 9.36/3.41  
% 9.36/3.41  Ordering : KBO
% 9.36/3.41  
% 9.36/3.41  Simplification rules
% 9.36/3.41  ----------------------
% 9.36/3.41  #Subsume      : 85
% 9.36/3.41  #Demod        : 4610
% 9.36/3.41  #Tautology    : 1535
% 9.36/3.41  #SimpNegUnit  : 13
% 9.36/3.41  #BackRed      : 114
% 9.36/3.41  
% 9.36/3.41  #Partial instantiations: 232
% 9.36/3.41  #Strategies tried      : 1
% 9.36/3.41  
% 9.36/3.41  Timing (in seconds)
% 9.36/3.41  ----------------------
% 9.36/3.42  Preprocessing        : 0.35
% 9.36/3.42  Parsing              : 0.19
% 9.36/3.42  CNF conversion       : 0.02
% 9.36/3.42  Main loop            : 2.23
% 9.36/3.42  Inferencing          : 0.65
% 9.36/3.42  Reduction            : 1.10
% 9.36/3.42  Demodulation         : 0.92
% 9.36/3.42  BG Simplification    : 0.10
% 9.36/3.42  Subsumption          : 0.28
% 9.36/3.42  Abstraction          : 0.17
% 9.36/3.42  MUC search           : 0.00
% 9.36/3.42  Cooper               : 0.00
% 9.36/3.42  Total                : 2.62
% 9.36/3.42  Index Insertion      : 0.00
% 9.36/3.42  Index Deletion       : 0.00
% 9.36/3.42  Index Matching       : 0.00
% 9.36/3.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
