%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:29 EST 2020

% Result     : Theorem 23.27s
% Output     : CNFRefutation 23.27s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 184 expanded)
%              Number of leaves         :   30 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  136 ( 309 expanded)
%              Number of equality atoms :   58 ( 118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [B_38,A_39] : k3_xboole_0(B_38,A_39) = k3_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [B_38,A_39] : r1_tarski(k3_xboole_0(B_38,A_39),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_10])).

tff(c_16,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_281,plain,(
    ! [A_70,B_71] :
      ( k5_relat_1(k6_relat_1(A_70),B_71) = B_71
      | ~ r1_tarski(k1_relat_1(B_71),A_70)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_303,plain,(
    ! [B_72] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_72)),B_72) = B_72
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_8,c_281])).

tff(c_322,plain,(
    ! [A_21] :
      ( k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_21)) = k6_relat_1(A_21)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_303])).

tff(c_326,plain,(
    ! [A_21] : k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_21)) = k6_relat_1(A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_322])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( k5_relat_1(k6_relat_1(A_28),B_29) = k7_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_559,plain,(
    ! [A_86,B_87,C_88] :
      ( k5_relat_1(k5_relat_1(A_86,B_87),C_88) = k5_relat_1(A_86,k5_relat_1(B_87,C_88))
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_591,plain,(
    ! [A_28,B_29,C_88] :
      ( k5_relat_1(k6_relat_1(A_28),k5_relat_1(B_29,C_88)) = k5_relat_1(k7_relat_1(B_29,A_28),C_88)
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_559])).

tff(c_2473,plain,(
    ! [A_134,B_135,C_136] :
      ( k5_relat_1(k6_relat_1(A_134),k5_relat_1(B_135,C_136)) = k5_relat_1(k7_relat_1(B_135,A_134),C_136)
      | ~ v1_relat_1(C_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_591])).

tff(c_18708,plain,(
    ! [B_350,C_351,A_352] :
      ( k7_relat_1(k5_relat_1(B_350,C_351),A_352) = k5_relat_1(k7_relat_1(B_350,A_352),C_351)
      | ~ v1_relat_1(k5_relat_1(B_350,C_351))
      | ~ v1_relat_1(C_351)
      | ~ v1_relat_1(B_350) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2473,c_32])).

tff(c_18744,plain,(
    ! [A_21,A_352] :
      ( k7_relat_1(k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_21)),A_352) = k5_relat_1(k7_relat_1(k6_relat_1(A_21),A_352),k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_18708])).

tff(c_18783,plain,(
    ! [A_353,A_354] : k5_relat_1(k7_relat_1(k6_relat_1(A_353),A_354),k6_relat_1(A_353)) = k7_relat_1(k6_relat_1(A_353),A_354) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_16,c_326,c_18744])).

tff(c_293,plain,(
    ! [A_70,A_21] :
      ( k5_relat_1(k6_relat_1(A_70),k6_relat_1(A_21)) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_70)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_281])).

tff(c_301,plain,(
    ! [A_70,A_21] :
      ( k5_relat_1(k6_relat_1(A_70),k6_relat_1(A_21)) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_293])).

tff(c_2498,plain,(
    ! [A_70,A_134,A_21] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_70),A_134),k6_relat_1(A_21)) = k5_relat_1(k6_relat_1(A_134),k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_70))
      | ~ r1_tarski(A_21,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_2473])).

tff(c_2534,plain,(
    ! [A_70,A_134,A_21] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_70),A_134),k6_relat_1(A_21)) = k5_relat_1(k6_relat_1(A_134),k6_relat_1(A_21))
      | ~ r1_tarski(A_21,A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_2498])).

tff(c_18791,plain,(
    ! [A_354,A_353] :
      ( k5_relat_1(k6_relat_1(A_354),k6_relat_1(A_353)) = k7_relat_1(k6_relat_1(A_353),A_354)
      | ~ r1_tarski(A_353,A_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18783,c_2534])).

tff(c_18872,plain,(
    ! [A_354,A_353] : k5_relat_1(k6_relat_1(A_354),k6_relat_1(A_353)) = k7_relat_1(k6_relat_1(A_353),A_354) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18791])).

tff(c_24,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_522,plain,(
    ! [B_83,A_84] :
      ( k5_relat_1(B_83,k6_relat_1(A_84)) = B_83
      | ~ r1_tarski(k2_relat_1(B_83),A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_525,plain,(
    ! [A_21,A_84] :
      ( k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_84)) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_84)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_522])).

tff(c_782,plain,(
    ! [A_96,A_97] :
      ( k5_relat_1(k6_relat_1(A_96),k6_relat_1(A_97)) = k6_relat_1(A_96)
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_525])).

tff(c_803,plain,(
    ! [A_97,A_96] :
      ( k7_relat_1(k6_relat_1(A_97),A_96) = k6_relat_1(A_96)
      | ~ v1_relat_1(k6_relat_1(A_97))
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_32])).

tff(c_837,plain,(
    ! [A_97,A_96] :
      ( k7_relat_1(k6_relat_1(A_97),A_96) = k6_relat_1(A_96)
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_803])).

tff(c_2520,plain,(
    ! [A_28,A_134,B_29] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_28),A_134),B_29) = k5_relat_1(k6_relat_1(A_134),k7_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2473])).

tff(c_9915,plain,(
    ! [A_245,A_246,B_247] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_245),A_246),B_247) = k5_relat_1(k6_relat_1(A_246),k7_relat_1(B_247,A_245))
      | ~ v1_relat_1(B_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2520])).

tff(c_78749,plain,(
    ! [A_1030,B_1031,A_1032] :
      ( k5_relat_1(k6_relat_1(A_1030),k7_relat_1(B_1031,A_1032)) = k5_relat_1(k6_relat_1(A_1030),B_1031)
      | ~ v1_relat_1(B_1031)
      | ~ r1_tarski(A_1030,A_1032) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_9915])).

tff(c_375,plain,(
    ! [B_75,A_76] :
      ( k3_xboole_0(B_75,k2_zfmisc_1(A_76,k2_relat_1(B_75))) = k7_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_413,plain,(
    ! [A_21,A_76] :
      ( k3_xboole_0(k6_relat_1(A_21),k2_zfmisc_1(A_76,A_21)) = k7_relat_1(k6_relat_1(A_21),A_76)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_375])).

tff(c_2391,plain,(
    ! [A_132,A_133] : k3_xboole_0(k6_relat_1(A_132),k2_zfmisc_1(A_133,A_132)) = k7_relat_1(k6_relat_1(A_132),A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_413])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2444,plain,(
    ! [A_132,A_133] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_132),A_133))
      | ~ v1_relat_1(k6_relat_1(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2391,c_18])).

tff(c_2471,plain,(
    ! [A_132,A_133] : v1_relat_1(k7_relat_1(k6_relat_1(A_132),A_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2444])).

tff(c_181,plain,(
    ! [B_58,A_59] :
      ( k3_xboole_0(k1_relat_1(B_58),A_59) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_222,plain,(
    ! [A_21,A_59] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_21),A_59)) = k3_xboole_0(A_21,A_59)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_181])).

tff(c_226,plain,(
    ! [A_21,A_59] : k1_relat_1(k7_relat_1(k6_relat_1(A_21),A_59)) = k3_xboole_0(A_21,A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_222])).

tff(c_315,plain,(
    ! [A_21,A_59] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_21,A_59)),k7_relat_1(k6_relat_1(A_21),A_59)) = k7_relat_1(k6_relat_1(A_21),A_59)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_21),A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_303])).

tff(c_19641,plain,(
    ! [A_360,A_361] : k5_relat_1(k6_relat_1(k3_xboole_0(A_360,A_361)),k7_relat_1(k6_relat_1(A_360),A_361)) = k7_relat_1(k6_relat_1(A_360),A_361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2471,c_315])).

tff(c_19830,plain,(
    ! [B_2,A_1] : k5_relat_1(k6_relat_1(k3_xboole_0(B_2,A_1)),k7_relat_1(k6_relat_1(A_1),B_2)) = k7_relat_1(k6_relat_1(A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19641])).

tff(c_78779,plain,(
    ! [A_1032,A_1] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_1032,A_1)),k6_relat_1(A_1)) = k7_relat_1(k6_relat_1(A_1),A_1032)
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ r1_tarski(k3_xboole_0(A_1032,A_1),A_1032) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78749,c_19830])).

tff(c_79194,plain,(
    ! [A_1033,A_1034] : k7_relat_1(k6_relat_1(A_1033),k3_xboole_0(A_1034,A_1033)) = k7_relat_1(k6_relat_1(A_1033),A_1034) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16,c_18872,c_78779])).

tff(c_79468,plain,(
    ! [A_1033,A_1034] :
      ( k7_relat_1(k6_relat_1(A_1033),A_1034) = k6_relat_1(k3_xboole_0(A_1034,A_1033))
      | ~ r1_tarski(k3_xboole_0(A_1034,A_1033),A_1033) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79194,c_837])).

tff(c_79780,plain,(
    ! [A_1033,A_1034] : k7_relat_1(k6_relat_1(A_1033),A_1034) = k6_relat_1(k3_xboole_0(A_1034,A_1033)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_79468])).

tff(c_153,plain,(
    ! [A_52,B_53] :
      ( k5_relat_1(k6_relat_1(A_52),B_53) = k7_relat_1(B_53,A_52)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_159,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_36])).

tff(c_165,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_159])).

tff(c_79881,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79780,c_165])).

tff(c_79903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_79881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.27/14.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.27/14.38  
% 23.27/14.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.27/14.38  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 23.27/14.38  
% 23.27/14.38  %Foreground sorts:
% 23.27/14.38  
% 23.27/14.38  
% 23.27/14.38  %Background operators:
% 23.27/14.38  
% 23.27/14.38  
% 23.27/14.38  %Foreground operators:
% 23.27/14.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.27/14.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 23.27/14.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 23.27/14.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.27/14.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.27/14.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.27/14.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.27/14.38  tff('#skF_2', type, '#skF_2': $i).
% 23.27/14.38  tff('#skF_1', type, '#skF_1': $i).
% 23.27/14.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.27/14.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.27/14.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.27/14.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 23.27/14.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.27/14.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.27/14.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.27/14.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 23.27/14.38  
% 23.27/14.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 23.27/14.40  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 23.27/14.40  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 23.27/14.40  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.27/14.40  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 23.27/14.40  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 23.27/14.40  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 23.27/14.40  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 23.27/14.40  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 23.27/14.40  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 23.27/14.40  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 23.27/14.40  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 23.27/14.40  tff(f_86, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 23.27/14.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.27/14.40  tff(c_59, plain, (![B_38, A_39]: (k3_xboole_0(B_38, A_39)=k3_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.27/14.40  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.27/14.40  tff(c_74, plain, (![B_38, A_39]: (r1_tarski(k3_xboole_0(B_38, A_39), A_39))), inference(superposition, [status(thm), theory('equality')], [c_59, c_10])).
% 23.27/14.40  tff(c_16, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.27/14.40  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.27/14.40  tff(c_22, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.27/14.40  tff(c_281, plain, (![A_70, B_71]: (k5_relat_1(k6_relat_1(A_70), B_71)=B_71 | ~r1_tarski(k1_relat_1(B_71), A_70) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_65])).
% 23.27/14.40  tff(c_303, plain, (![B_72]: (k5_relat_1(k6_relat_1(k1_relat_1(B_72)), B_72)=B_72 | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_8, c_281])).
% 23.27/14.40  tff(c_322, plain, (![A_21]: (k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_21))=k6_relat_1(A_21) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_303])).
% 23.27/14.40  tff(c_326, plain, (![A_21]: (k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_21))=k6_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_322])).
% 23.27/14.40  tff(c_32, plain, (![A_28, B_29]: (k5_relat_1(k6_relat_1(A_28), B_29)=k7_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_79])).
% 23.27/14.40  tff(c_559, plain, (![A_86, B_87, C_88]: (k5_relat_1(k5_relat_1(A_86, B_87), C_88)=k5_relat_1(A_86, k5_relat_1(B_87, C_88)) | ~v1_relat_1(C_88) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.27/14.40  tff(c_591, plain, (![A_28, B_29, C_88]: (k5_relat_1(k6_relat_1(A_28), k5_relat_1(B_29, C_88))=k5_relat_1(k7_relat_1(B_29, A_28), C_88) | ~v1_relat_1(C_88) | ~v1_relat_1(B_29) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_32, c_559])).
% 23.27/14.40  tff(c_2473, plain, (![A_134, B_135, C_136]: (k5_relat_1(k6_relat_1(A_134), k5_relat_1(B_135, C_136))=k5_relat_1(k7_relat_1(B_135, A_134), C_136) | ~v1_relat_1(C_136) | ~v1_relat_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_591])).
% 23.27/14.40  tff(c_18708, plain, (![B_350, C_351, A_352]: (k7_relat_1(k5_relat_1(B_350, C_351), A_352)=k5_relat_1(k7_relat_1(B_350, A_352), C_351) | ~v1_relat_1(k5_relat_1(B_350, C_351)) | ~v1_relat_1(C_351) | ~v1_relat_1(B_350))), inference(superposition, [status(thm), theory('equality')], [c_2473, c_32])).
% 23.27/14.40  tff(c_18744, plain, (![A_21, A_352]: (k7_relat_1(k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_21)), A_352)=k5_relat_1(k7_relat_1(k6_relat_1(A_21), A_352), k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_326, c_18708])).
% 23.27/14.40  tff(c_18783, plain, (![A_353, A_354]: (k5_relat_1(k7_relat_1(k6_relat_1(A_353), A_354), k6_relat_1(A_353))=k7_relat_1(k6_relat_1(A_353), A_354))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_16, c_326, c_18744])).
% 23.27/14.40  tff(c_293, plain, (![A_70, A_21]: (k5_relat_1(k6_relat_1(A_70), k6_relat_1(A_21))=k6_relat_1(A_21) | ~r1_tarski(A_21, A_70) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_281])).
% 23.27/14.40  tff(c_301, plain, (![A_70, A_21]: (k5_relat_1(k6_relat_1(A_70), k6_relat_1(A_21))=k6_relat_1(A_21) | ~r1_tarski(A_21, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_293])).
% 23.27/14.40  tff(c_2498, plain, (![A_70, A_134, A_21]: (k5_relat_1(k7_relat_1(k6_relat_1(A_70), A_134), k6_relat_1(A_21))=k5_relat_1(k6_relat_1(A_134), k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_70)) | ~r1_tarski(A_21, A_70))), inference(superposition, [status(thm), theory('equality')], [c_301, c_2473])).
% 23.27/14.40  tff(c_2534, plain, (![A_70, A_134, A_21]: (k5_relat_1(k7_relat_1(k6_relat_1(A_70), A_134), k6_relat_1(A_21))=k5_relat_1(k6_relat_1(A_134), k6_relat_1(A_21)) | ~r1_tarski(A_21, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_2498])).
% 23.27/14.40  tff(c_18791, plain, (![A_354, A_353]: (k5_relat_1(k6_relat_1(A_354), k6_relat_1(A_353))=k7_relat_1(k6_relat_1(A_353), A_354) | ~r1_tarski(A_353, A_353))), inference(superposition, [status(thm), theory('equality')], [c_18783, c_2534])).
% 23.27/14.40  tff(c_18872, plain, (![A_354, A_353]: (k5_relat_1(k6_relat_1(A_354), k6_relat_1(A_353))=k7_relat_1(k6_relat_1(A_353), A_354))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18791])).
% 23.27/14.40  tff(c_24, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.27/14.40  tff(c_522, plain, (![B_83, A_84]: (k5_relat_1(B_83, k6_relat_1(A_84))=B_83 | ~r1_tarski(k2_relat_1(B_83), A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_71])).
% 23.27/14.40  tff(c_525, plain, (![A_21, A_84]: (k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_84))=k6_relat_1(A_21) | ~r1_tarski(A_21, A_84) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_522])).
% 23.27/14.40  tff(c_782, plain, (![A_96, A_97]: (k5_relat_1(k6_relat_1(A_96), k6_relat_1(A_97))=k6_relat_1(A_96) | ~r1_tarski(A_96, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_525])).
% 23.27/14.40  tff(c_803, plain, (![A_97, A_96]: (k7_relat_1(k6_relat_1(A_97), A_96)=k6_relat_1(A_96) | ~v1_relat_1(k6_relat_1(A_97)) | ~r1_tarski(A_96, A_97))), inference(superposition, [status(thm), theory('equality')], [c_782, c_32])).
% 23.27/14.40  tff(c_837, plain, (![A_97, A_96]: (k7_relat_1(k6_relat_1(A_97), A_96)=k6_relat_1(A_96) | ~r1_tarski(A_96, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_803])).
% 23.27/14.40  tff(c_2520, plain, (![A_28, A_134, B_29]: (k5_relat_1(k7_relat_1(k6_relat_1(A_28), A_134), B_29)=k5_relat_1(k6_relat_1(A_134), k7_relat_1(B_29, A_28)) | ~v1_relat_1(B_29) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2473])).
% 23.27/14.40  tff(c_9915, plain, (![A_245, A_246, B_247]: (k5_relat_1(k7_relat_1(k6_relat_1(A_245), A_246), B_247)=k5_relat_1(k6_relat_1(A_246), k7_relat_1(B_247, A_245)) | ~v1_relat_1(B_247))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2520])).
% 23.27/14.40  tff(c_78749, plain, (![A_1030, B_1031, A_1032]: (k5_relat_1(k6_relat_1(A_1030), k7_relat_1(B_1031, A_1032))=k5_relat_1(k6_relat_1(A_1030), B_1031) | ~v1_relat_1(B_1031) | ~r1_tarski(A_1030, A_1032))), inference(superposition, [status(thm), theory('equality')], [c_837, c_9915])).
% 23.27/14.40  tff(c_375, plain, (![B_75, A_76]: (k3_xboole_0(B_75, k2_zfmisc_1(A_76, k2_relat_1(B_75)))=k7_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.27/14.40  tff(c_413, plain, (![A_21, A_76]: (k3_xboole_0(k6_relat_1(A_21), k2_zfmisc_1(A_76, A_21))=k7_relat_1(k6_relat_1(A_21), A_76) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_375])).
% 23.27/14.40  tff(c_2391, plain, (![A_132, A_133]: (k3_xboole_0(k6_relat_1(A_132), k2_zfmisc_1(A_133, A_132))=k7_relat_1(k6_relat_1(A_132), A_133))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_413])).
% 23.27/14.40  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k3_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.27/14.40  tff(c_2444, plain, (![A_132, A_133]: (v1_relat_1(k7_relat_1(k6_relat_1(A_132), A_133)) | ~v1_relat_1(k6_relat_1(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_2391, c_18])).
% 23.27/14.40  tff(c_2471, plain, (![A_132, A_133]: (v1_relat_1(k7_relat_1(k6_relat_1(A_132), A_133)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2444])).
% 23.27/14.40  tff(c_181, plain, (![B_58, A_59]: (k3_xboole_0(k1_relat_1(B_58), A_59)=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.27/14.40  tff(c_222, plain, (![A_21, A_59]: (k1_relat_1(k7_relat_1(k6_relat_1(A_21), A_59))=k3_xboole_0(A_21, A_59) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_181])).
% 23.27/14.40  tff(c_226, plain, (![A_21, A_59]: (k1_relat_1(k7_relat_1(k6_relat_1(A_21), A_59))=k3_xboole_0(A_21, A_59))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_222])).
% 23.27/14.40  tff(c_315, plain, (![A_21, A_59]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_21, A_59)), k7_relat_1(k6_relat_1(A_21), A_59))=k7_relat_1(k6_relat_1(A_21), A_59) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_21), A_59)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_303])).
% 23.27/14.40  tff(c_19641, plain, (![A_360, A_361]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_360, A_361)), k7_relat_1(k6_relat_1(A_360), A_361))=k7_relat_1(k6_relat_1(A_360), A_361))), inference(demodulation, [status(thm), theory('equality')], [c_2471, c_315])).
% 23.27/14.40  tff(c_19830, plain, (![B_2, A_1]: (k5_relat_1(k6_relat_1(k3_xboole_0(B_2, A_1)), k7_relat_1(k6_relat_1(A_1), B_2))=k7_relat_1(k6_relat_1(A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_19641])).
% 23.27/14.40  tff(c_78779, plain, (![A_1032, A_1]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_1032, A_1)), k6_relat_1(A_1))=k7_relat_1(k6_relat_1(A_1), A_1032) | ~v1_relat_1(k6_relat_1(A_1)) | ~r1_tarski(k3_xboole_0(A_1032, A_1), A_1032))), inference(superposition, [status(thm), theory('equality')], [c_78749, c_19830])).
% 23.27/14.40  tff(c_79194, plain, (![A_1033, A_1034]: (k7_relat_1(k6_relat_1(A_1033), k3_xboole_0(A_1034, A_1033))=k7_relat_1(k6_relat_1(A_1033), A_1034))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16, c_18872, c_78779])).
% 23.27/14.40  tff(c_79468, plain, (![A_1033, A_1034]: (k7_relat_1(k6_relat_1(A_1033), A_1034)=k6_relat_1(k3_xboole_0(A_1034, A_1033)) | ~r1_tarski(k3_xboole_0(A_1034, A_1033), A_1033))), inference(superposition, [status(thm), theory('equality')], [c_79194, c_837])).
% 23.27/14.40  tff(c_79780, plain, (![A_1033, A_1034]: (k7_relat_1(k6_relat_1(A_1033), A_1034)=k6_relat_1(k3_xboole_0(A_1034, A_1033)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_79468])).
% 23.27/14.40  tff(c_153, plain, (![A_52, B_53]: (k5_relat_1(k6_relat_1(A_52), B_53)=k7_relat_1(B_53, A_52) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_79])).
% 23.27/14.40  tff(c_36, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.27/14.40  tff(c_159, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_36])).
% 23.27/14.40  tff(c_165, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_159])).
% 23.27/14.40  tff(c_79881, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79780, c_165])).
% 23.27/14.40  tff(c_79903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_79881])).
% 23.27/14.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.27/14.40  
% 23.27/14.40  Inference rules
% 23.27/14.40  ----------------------
% 23.27/14.40  #Ref     : 0
% 23.27/14.40  #Sup     : 19906
% 23.27/14.40  #Fact    : 0
% 23.27/14.40  #Define  : 0
% 23.27/14.40  #Split   : 2
% 23.27/14.40  #Chain   : 0
% 23.27/14.40  #Close   : 0
% 23.27/14.40  
% 23.27/14.40  Ordering : KBO
% 23.27/14.40  
% 23.27/14.40  Simplification rules
% 23.27/14.40  ----------------------
% 23.27/14.40  #Subsume      : 4690
% 23.27/14.40  #Demod        : 16760
% 23.27/14.40  #Tautology    : 5938
% 23.27/14.40  #SimpNegUnit  : 0
% 23.27/14.40  #BackRed      : 69
% 23.27/14.40  
% 23.27/14.40  #Partial instantiations: 0
% 23.27/14.40  #Strategies tried      : 1
% 23.27/14.40  
% 23.27/14.40  Timing (in seconds)
% 23.27/14.40  ----------------------
% 23.27/14.40  Preprocessing        : 0.33
% 23.27/14.40  Parsing              : 0.17
% 23.27/14.40  CNF conversion       : 0.02
% 23.27/14.40  Main loop            : 13.30
% 23.27/14.40  Inferencing          : 2.08
% 23.27/14.40  Reduction            : 7.15
% 23.27/14.40  Demodulation         : 6.45
% 23.27/14.40  BG Simplification    : 0.33
% 23.27/14.40  Subsumption          : 3.11
% 23.27/14.40  Abstraction          : 0.55
% 23.27/14.41  MUC search           : 0.00
% 23.27/14.41  Cooper               : 0.00
% 23.27/14.41  Total                : 13.66
% 23.27/14.41  Index Insertion      : 0.00
% 23.27/14.41  Index Deletion       : 0.00
% 23.27/14.41  Index Matching       : 0.00
% 23.27/14.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
