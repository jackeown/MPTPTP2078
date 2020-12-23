%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:47 EST 2020

% Result     : Theorem 24.00s
% Output     : CNFRefutation 24.48s
% Verified   : 
% Statistics : Number of formulae       :  337 (3946 expanded)
%              Number of leaves         :   28 (1239 expanded)
%              Depth                    :   33
%              Number of atoms          :  574 (8544 expanded)
%              Number of equality atoms :   94 (4484 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_33])).

tff(c_28,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_54,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_28])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] : k2_zfmisc_1(k2_zfmisc_1(A_17,B_18),C_19) = k3_zfmisc_1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( v1_xboole_0(k2_zfmisc_1(A_4,B_5))
      | ~ v1_xboole_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_29,B_30] :
      ( v1_xboole_0(k2_zfmisc_1(A_29,B_30))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_2])).

tff(c_87,plain,(
    ! [A_34,B_35] :
      ( k2_zfmisc_1(A_34,B_35) = '#skF_1'
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_55,c_38])).

tff(c_94,plain,(
    ! [A_6,B_7,B_35] :
      ( k2_zfmisc_1(k2_zfmisc_1(A_6,B_7),B_35) = '#skF_1'
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_820,plain,(
    ! [A_92,B_93,B_94] :
      ( k3_zfmisc_1(A_92,B_93,B_94) = '#skF_1'
      | ~ v1_xboole_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_94])).

tff(c_1507,plain,(
    ! [A_143,B_144,B_145,B_146] :
      ( k3_zfmisc_1(k2_zfmisc_1(A_143,B_144),B_145,B_146) = '#skF_1'
      | ~ v1_xboole_0(B_144) ) ),
    inference(resolution,[status(thm)],[c_12,c_820])).

tff(c_437,plain,(
    ! [A_53,B_54,C_55] : k2_zfmisc_1(k2_zfmisc_1(A_53,B_54),C_55) = k3_zfmisc_1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_15,B_16))
      | v1_xboole_0(B_16)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_460,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_53,B_54,C_55))
      | v1_xboole_0(C_55)
      | v1_xboole_0(k2_zfmisc_1(A_53,B_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_20])).

tff(c_1519,plain,(
    ! [B_146,A_143,B_144,B_145] :
      ( ~ v1_xboole_0('#skF_1')
      | v1_xboole_0(B_146)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_143,B_144),B_145))
      | ~ v1_xboole_0(B_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_460])).

tff(c_1590,plain,(
    ! [B_146,A_143,B_144,B_145] :
      ( v1_xboole_0(B_146)
      | v1_xboole_0(k3_zfmisc_1(A_143,B_144,B_145))
      | ~ v1_xboole_0(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4,c_1519])).

tff(c_1833,plain,(
    ! [A_143,B_144,B_145] :
      ( v1_xboole_0(k3_zfmisc_1(A_143,B_144,B_145))
      | ~ v1_xboole_0(B_144) ) ),
    inference(splitLeft,[status(thm)],[c_1590])).

tff(c_552,plain,(
    ! [A_62,B_63,C_64,D_65] : k2_zfmisc_1(k3_zfmisc_1(A_62,B_63,C_64),D_65) = k4_zfmisc_1(A_62,B_63,C_64,D_65) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_582,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( v1_xboole_0(k4_zfmisc_1(A_62,B_63,C_64,D_65))
      | ~ v1_xboole_0(k3_zfmisc_1(A_62,B_63,C_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_14])).

tff(c_30,plain,(
    k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_991,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( v1_xboole_0(k4_zfmisc_1(A_116,B_117,C_118,D_119))
      | ~ v1_xboole_0(k3_zfmisc_1(A_116,B_117,C_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_14])).

tff(c_1023,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_991])).

tff(c_1270,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1023])).

tff(c_848,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( v1_xboole_0(k4_zfmisc_1(A_98,B_99,C_100,D_101))
      | ~ v1_xboole_0(D_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_12])).

tff(c_876,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_848])).

tff(c_888,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_2969,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( ~ v1_xboole_0(k4_zfmisc_1(A_220,B_221,C_222,D_223))
      | v1_xboole_0(D_223)
      | v1_xboole_0(k3_zfmisc_1(A_220,B_221,C_222)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_20])).

tff(c_2999,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | v1_xboole_0('#skF_9')
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2969])).

tff(c_3015,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1270,c_888,c_2999])).

tff(c_3026,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_582,c_3015])).

tff(c_3037,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1833,c_3026])).

tff(c_26,plain,
    ( '#skF_5' != '#skF_9'
    | '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_zfmisc_1(k3_zfmisc_1(A_20,B_21,C_22),D_23) = k4_zfmisc_1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_473,plain,(
    ! [A_17,B_18,C_19,C_55] : k3_zfmisc_1(k2_zfmisc_1(A_17,B_18),C_19,C_55) = k2_zfmisc_1(k3_zfmisc_1(A_17,B_18,C_19),C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_437])).

tff(c_1612,plain,(
    ! [A_17,B_18,C_19,C_55] : k3_zfmisc_1(k2_zfmisc_1(A_17,B_18),C_19,C_55) = k4_zfmisc_1(A_17,B_18,C_19,C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_473])).

tff(c_1834,plain,(
    ! [A_164,B_165,B_166] :
      ( v1_xboole_0(k3_zfmisc_1(A_164,B_165,B_166))
      | ~ v1_xboole_0(B_165) ) ),
    inference(splitLeft,[status(thm)],[c_1590])).

tff(c_1864,plain,(
    ! [A_17,B_18,C_19,C_55] :
      ( v1_xboole_0(k4_zfmisc_1(A_17,B_18,C_19,C_55))
      | ~ v1_xboole_0(C_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1612,c_1834])).

tff(c_3025,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1864,c_3015])).

tff(c_467,plain,(
    ! [A_53,B_54,C_55] :
      ( v1_xboole_0(k3_zfmisc_1(A_53,B_54,C_55))
      | ~ v1_xboole_0(k2_zfmisc_1(A_53,B_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_14])).

tff(c_1277,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_467,c_1270])).

tff(c_3038,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_467,c_3026])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_776,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( ~ r1_tarski(k2_zfmisc_1(A_88,B_89),k2_zfmisc_1(C_90,D_91))
      | r1_tarski(B_89,D_91)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3635,plain,(
    ! [B_243,B_244,A_245,C_242,A_247,D_246] :
      ( ~ r1_tarski(k2_zfmisc_1(A_245,B_244),k4_zfmisc_1(A_247,B_243,C_242,D_246))
      | r1_tarski(B_244,D_246)
      | v1_xboole_0(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_776])).

tff(c_3741,plain,(
    ! [A_249,B_250] :
      ( ~ r1_tarski(k2_zfmisc_1(A_249,B_250),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(B_250,'#skF_9')
      | v1_xboole_0(A_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3635])).

tff(c_4651,plain,(
    ! [A_302,B_303,C_304,D_305] :
      ( ~ r1_tarski(k4_zfmisc_1(A_302,B_303,C_304,D_305),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(D_305,'#skF_9')
      | v1_xboole_0(k3_zfmisc_1(A_302,B_303,C_304)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3741])).

tff(c_4686,plain,
    ( r1_tarski('#skF_5','#skF_9')
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_4651])).

tff(c_4708,plain,(
    r1_tarski('#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_3026,c_4686])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4715,plain,
    ( '#skF_5' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_4708,c_6])).

tff(c_4716,plain,(
    ~ r1_tarski('#skF_9','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4715])).

tff(c_4764,plain,(
    ! [D_312,B_311,C_314,A_313,D_310,C_309] :
      ( ~ r1_tarski(k4_zfmisc_1(A_313,B_311,C_309,D_312),k2_zfmisc_1(C_314,D_310))
      | r1_tarski(D_312,D_310)
      | v1_xboole_0(k3_zfmisc_1(A_313,B_311,C_309)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_776])).

tff(c_18306,plain,(
    ! [B_707,A_708,A_706,B_704,C_701,C_703,D_702,D_705] :
      ( ~ r1_tarski(k4_zfmisc_1(A_708,B_707,C_703,D_702),k4_zfmisc_1(A_706,B_704,C_701,D_705))
      | r1_tarski(D_702,D_705)
      | v1_xboole_0(k3_zfmisc_1(A_708,B_707,C_703)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4764])).

tff(c_18410,plain,(
    ! [A_706,B_704,C_701,D_705] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k4_zfmisc_1(A_706,B_704,C_701,D_705))
      | r1_tarski('#skF_9',D_705)
      | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_18306])).

tff(c_18840,plain,(
    ! [A_715,B_716,C_717,D_718] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k4_zfmisc_1(A_715,B_716,C_717,D_718))
      | r1_tarski('#skF_9',D_718) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1270,c_18410])).

tff(c_18901,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_18840])).

tff(c_18910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4716,c_18901])).

tff(c_18911,plain,(
    '#skF_5' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4715])).

tff(c_18919,plain,(
    k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18911,c_30])).

tff(c_624,plain,(
    ! [B_69,A_70,D_71,C_72] :
      ( ~ r1_tarski(k2_zfmisc_1(B_69,A_70),k2_zfmisc_1(D_71,C_72))
      | r1_tarski(B_69,D_71)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_630,plain,(
    ! [C_22,D_23,A_70,A_20,B_21,B_69] :
      ( ~ r1_tarski(k2_zfmisc_1(B_69,A_70),k4_zfmisc_1(A_20,B_21,C_22,D_23))
      | r1_tarski(B_69,k3_zfmisc_1(A_20,B_21,C_22))
      | v1_xboole_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_624])).

tff(c_19677,plain,(
    ! [B_755,A_756] :
      ( ~ r1_tarski(k2_zfmisc_1(B_755,A_756),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(B_755,k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
      | v1_xboole_0(A_756) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18919,c_630])).

tff(c_27981,plain,(
    ! [A_985,B_986,C_987,D_988] :
      ( ~ r1_tarski(k4_zfmisc_1(A_985,B_986,C_987,D_988),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(k3_zfmisc_1(A_985,B_986,C_987),k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
      | v1_xboole_0(D_988) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_19677])).

tff(c_28035,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_27981])).

tff(c_28066,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_888,c_28035])).

tff(c_2679,plain,(
    ! [A_202,B_204,B_203,A_205,C_201] :
      ( ~ r1_tarski(k2_zfmisc_1(A_205,B_204),k3_zfmisc_1(A_202,B_203,C_201))
      | r1_tarski(B_204,C_201)
      | v1_xboole_0(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_776])).

tff(c_2724,plain,(
    ! [A_202,B_203,C_19,B_18,A_17,C_201] :
      ( ~ r1_tarski(k3_zfmisc_1(A_17,B_18,C_19),k3_zfmisc_1(A_202,B_203,C_201))
      | r1_tarski(C_19,C_201)
      | v1_xboole_0(k2_zfmisc_1(A_17,B_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2679])).

tff(c_28069,plain,
    ( r1_tarski('#skF_4','#skF_8')
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28066,c_2724])).

tff(c_28077,plain,(
    r1_tarski('#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_3038,c_28069])).

tff(c_28086,plain,
    ( '#skF_8' = '#skF_4'
    | ~ r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_28077,c_6])).

tff(c_28087,plain,(
    ~ r1_tarski('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28086])).

tff(c_18982,plain,(
    ! [B_725,A_727,B_724,A_723,C_722,D_726] :
      ( ~ r1_tarski(k2_zfmisc_1(B_724,A_723),k4_zfmisc_1(A_727,B_725,C_722,D_726))
      | r1_tarski(B_724,k3_zfmisc_1(A_727,B_725,C_722))
      | v1_xboole_0(A_723) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_624])).

tff(c_39338,plain,(
    ! [A_1262,B_1259,A_1257,B_1258,D_1260,C_1256,D_1261,C_1263] :
      ( ~ r1_tarski(k4_zfmisc_1(A_1262,B_1259,C_1256,D_1261),k4_zfmisc_1(A_1257,B_1258,C_1263,D_1260))
      | r1_tarski(k3_zfmisc_1(A_1262,B_1259,C_1256),k3_zfmisc_1(A_1257,B_1258,C_1263))
      | v1_xboole_0(D_1261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_18982])).

tff(c_39419,plain,(
    ! [A_1257,B_1258,C_1263,D_1260] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_1257,B_1258,C_1263,D_1260))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k3_zfmisc_1(A_1257,B_1258,C_1263))
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18919,c_39338])).

tff(c_40809,plain,(
    ! [A_1278,B_1279,C_1280,D_1281] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_1278,B_1279,C_1280,D_1281))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k3_zfmisc_1(A_1278,B_1279,C_1280)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_888,c_39419])).

tff(c_40890,plain,(
    r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_40809])).

tff(c_40896,plain,
    ( r1_tarski('#skF_8','#skF_4')
    | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40890,c_2724])).

tff(c_40908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1277,c_28087,c_40896])).

tff(c_40909,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28086])).

tff(c_40912,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_6','#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40909,c_28066])).

tff(c_4179,plain,(
    ! [A_274,C_273,C_277,B_275,D_276] :
      ( ~ r1_tarski(k3_zfmisc_1(A_274,B_275,C_273),k2_zfmisc_1(D_276,C_277))
      | r1_tarski(k2_zfmisc_1(A_274,B_275),D_276)
      | v1_xboole_0(C_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_624])).

tff(c_44324,plain,(
    ! [B_1384,A_1379,C_1383,C_1380,B_1382,A_1381] :
      ( ~ r1_tarski(k3_zfmisc_1(A_1379,B_1384,C_1383),k3_zfmisc_1(A_1381,B_1382,C_1380))
      | r1_tarski(k2_zfmisc_1(A_1379,B_1384),k2_zfmisc_1(A_1381,B_1382))
      | v1_xboole_0(C_1383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4179])).

tff(c_44343,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40912,c_44324])).

tff(c_44460,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_3025,c_44343])).

tff(c_16,plain,(
    ! [B_12,A_8,D_14,C_13] :
      ( ~ r1_tarski(k2_zfmisc_1(B_12,A_8),k2_zfmisc_1(D_14,C_13))
      | r1_tarski(B_12,D_14)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44507,plain,
    ( r1_tarski('#skF_2','#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44460,c_16])).

tff(c_44516,plain,(
    r1_tarski('#skF_2','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_3037,c_44507])).

tff(c_44529,plain,
    ( '#skF_6' = '#skF_2'
    | ~ r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_44516,c_6])).

tff(c_44534,plain,(
    ~ r1_tarski('#skF_6','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_44529])).

tff(c_1285,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_1277])).

tff(c_3046,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_3038])).

tff(c_18,plain,(
    ! [A_8,B_12,C_13,D_14] :
      ( ~ r1_tarski(k2_zfmisc_1(A_8,B_12),k2_zfmisc_1(C_13,D_14))
      | r1_tarski(B_12,D_14)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44504,plain,
    ( r1_tarski('#skF_3','#skF_7')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44460,c_18])).

tff(c_44513,plain,(
    r1_tarski('#skF_3','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3046,c_44504])).

tff(c_44524,plain,
    ( '#skF_7' = '#skF_3'
    | ~ r1_tarski('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_44513,c_6])).

tff(c_44539,plain,(
    ~ r1_tarski('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44524])).

tff(c_40917,plain,(
    k4_zfmisc_1('#skF_6','#skF_7','#skF_4','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40909,c_18919])).

tff(c_51839,plain,(
    ! [C_1548,B_1544,B_1543,D_1545,A_1542,C_1541,A_1547,D_1546] :
      ( ~ r1_tarski(k4_zfmisc_1(A_1547,B_1544,C_1541,D_1546),k4_zfmisc_1(A_1542,B_1543,C_1548,D_1545))
      | r1_tarski(k3_zfmisc_1(A_1547,B_1544,C_1541),k3_zfmisc_1(A_1542,B_1543,C_1548))
      | v1_xboole_0(D_1546) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_18982])).

tff(c_51874,plain,(
    ! [A_1542,B_1543,C_1548,D_1545] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_1542,B_1543,C_1548,D_1545))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_4'),k3_zfmisc_1(A_1542,B_1543,C_1548))
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40917,c_51839])).

tff(c_52796,plain,(
    ! [A_1561,B_1562,C_1563,D_1564] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_1561,B_1562,C_1563,D_1564))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_4'),k3_zfmisc_1(A_1561,B_1562,C_1563)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_888,c_51874])).

tff(c_52877,plain,(
    r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_4'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_52796])).

tff(c_4234,plain,(
    ! [A_274,C_273,C_19,B_275,B_18,A_17] :
      ( ~ r1_tarski(k3_zfmisc_1(A_274,B_275,C_273),k3_zfmisc_1(A_17,B_18,C_19))
      | r1_tarski(k2_zfmisc_1(A_274,B_275),k2_zfmisc_1(A_17,B_18))
      | v1_xboole_0(C_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4179])).

tff(c_52880,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_6','#skF_7'),k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52877,c_4234])).

tff(c_52891,plain,(
    r1_tarski(k2_zfmisc_1('#skF_6','#skF_7'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_3025,c_52880])).

tff(c_52910,plain,
    ( r1_tarski('#skF_7','#skF_3')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52891,c_18])).

tff(c_52922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1285,c_44539,c_52910])).

tff(c_52923,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44524])).

tff(c_52929,plain,(
    k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52923,c_40917])).

tff(c_19889,plain,(
    ! [A_767,C_764,B_765,C_762,D_766,D_763] :
      ( ~ r1_tarski(k4_zfmisc_1(A_767,B_765,C_762,D_766),k2_zfmisc_1(D_763,C_764))
      | r1_tarski(k3_zfmisc_1(A_767,B_765,C_762),D_763)
      | v1_xboole_0(D_766) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_624])).

tff(c_58965,plain,(
    ! [D_1702,B_1701,A_1703,A_1698,D_1700,C_1704,B_1699,C_1697] :
      ( ~ r1_tarski(k4_zfmisc_1(A_1698,B_1699,C_1704,D_1700),k4_zfmisc_1(A_1703,B_1701,C_1697,D_1702))
      | r1_tarski(k3_zfmisc_1(A_1698,B_1699,C_1704),k3_zfmisc_1(A_1703,B_1701,C_1697))
      | v1_xboole_0(D_1700) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_19889])).

tff(c_58990,plain,(
    ! [A_1703,B_1701,C_1697,D_1702] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_1703,B_1701,C_1697,D_1702))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_3','#skF_4'),k3_zfmisc_1(A_1703,B_1701,C_1697))
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52929,c_58965])).

tff(c_60160,plain,(
    ! [A_1719,B_1720,C_1721,D_1722] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_1719,B_1720,C_1721,D_1722))
      | r1_tarski(k3_zfmisc_1('#skF_6','#skF_3','#skF_4'),k3_zfmisc_1(A_1719,B_1720,C_1721)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_888,c_58990])).

tff(c_60241,plain,(
    r1_tarski(k3_zfmisc_1('#skF_6','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_60160])).

tff(c_60244,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_6','#skF_3'),k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60241,c_4234])).

tff(c_60255,plain,(
    r1_tarski(k2_zfmisc_1('#skF_6','#skF_3'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_3025,c_60244])).

tff(c_60277,plain,
    ( r1_tarski('#skF_6','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60255,c_16])).

tff(c_60289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3037,c_44534,c_60277])).

tff(c_60290,plain,(
    ! [B_146] : v1_xboole_0(B_146) ),
    inference(splitRight,[status(thm)],[c_1590])).

tff(c_1286,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_1277])).

tff(c_60360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60290,c_1286])).

tff(c_60361,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1023])).

tff(c_60465,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60361,c_38])).

tff(c_60476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_60465])).

tff(c_60478,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_60497,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_60478,c_38])).

tff(c_60514,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60497,c_54])).

tff(c_60477,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_60629,plain,(
    ! [A_1728] :
      ( A_1728 = '#skF_9'
      | ~ v1_xboole_0(A_1728) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60497,c_38])).

tff(c_60648,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_60477,c_60629])).

tff(c_60764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60514,c_60648])).

tff(c_60765,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4'
    | '#skF_5' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_60787,plain,(
    '#skF_5' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_60765])).

tff(c_61216,plain,(
    ! [A_1767,B_1768,C_1769,D_1770] : k2_zfmisc_1(k3_zfmisc_1(A_1767,B_1768,C_1769),D_1770) = k4_zfmisc_1(A_1767,B_1768,C_1769,D_1770) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61246,plain,(
    ! [A_1767,B_1768,C_1769,D_1770] :
      ( v1_xboole_0(k4_zfmisc_1(A_1767,B_1768,C_1769,D_1770))
      | ~ v1_xboole_0(k3_zfmisc_1(A_1767,B_1768,C_1769)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61216,c_14])).

tff(c_60766,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_60895,plain,(
    k4_zfmisc_1('#skF_2','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60766,c_30])).

tff(c_62100,plain,(
    ! [A_1845,B_1846,C_1847,D_1848] :
      ( v1_xboole_0(k4_zfmisc_1(A_1845,B_1846,C_1847,D_1848))
      | ~ v1_xboole_0(k3_zfmisc_1(A_1845,B_1846,C_1847)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61216,c_14])).

tff(c_62132,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60895,c_62100])).

tff(c_62356,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_62132])).

tff(c_61536,plain,(
    ! [A_1804,B_1805,C_1806,D_1807] :
      ( v1_xboole_0(k4_zfmisc_1(A_1804,B_1805,C_1806,D_1807))
      | ~ v1_xboole_0(D_1807) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61216,c_12])).

tff(c_61562,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_60895,c_61536])).

tff(c_61607,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_61562])).

tff(c_63946,plain,(
    ! [A_1927,B_1928,C_1929,D_1930] :
      ( ~ v1_xboole_0(k4_zfmisc_1(A_1927,B_1928,C_1929,D_1930))
      | v1_xboole_0(D_1930)
      | v1_xboole_0(k3_zfmisc_1(A_1927,B_1928,C_1929)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61216,c_20])).

tff(c_63979,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
    | v1_xboole_0('#skF_9')
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60895,c_63946])).

tff(c_63997,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62356,c_61607,c_63979])).

tff(c_64025,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_61246,c_63997])).

tff(c_61439,plain,(
    ! [A_1791,B_1792,C_1793,D_1794] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1791,B_1792),k2_zfmisc_1(C_1793,D_1794))
      | r1_tarski(B_1792,D_1794)
      | v1_xboole_0(A_1791) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64340,plain,(
    ! [A_1955,B_1954,A_1958,D_1957,B_1956,C_1953] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1955,B_1954),k4_zfmisc_1(A_1958,B_1956,C_1953,D_1957))
      | r1_tarski(B_1954,D_1957)
      | v1_xboole_0(A_1955) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_61439])).

tff(c_64554,plain,(
    ! [A_1966,B_1967] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1966,B_1967),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(B_1967,'#skF_9')
      | v1_xboole_0(A_1966) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60895,c_64340])).

tff(c_65326,plain,(
    ! [A_2009,B_2010,C_2011,D_2012] :
      ( ~ r1_tarski(k4_zfmisc_1(A_2009,B_2010,C_2011,D_2012),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | r1_tarski(D_2012,'#skF_9')
      | v1_xboole_0(k3_zfmisc_1(A_2009,B_2010,C_2011)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_64554])).

tff(c_65361,plain,
    ( r1_tarski('#skF_5','#skF_9')
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_65326])).

tff(c_65383,plain,(
    r1_tarski('#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_64025,c_65361])).

tff(c_65388,plain,
    ( '#skF_5' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_65383,c_6])).

tff(c_65393,plain,(
    ~ r1_tarski('#skF_9','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60787,c_65388])).

tff(c_66502,plain,(
    ! [D_2059,B_2058,A_2060,D_2061,C_2057,C_2056] :
      ( ~ r1_tarski(k4_zfmisc_1(A_2060,B_2058,C_2056,D_2059),k2_zfmisc_1(C_2057,D_2061))
      | r1_tarski(D_2059,D_2061)
      | v1_xboole_0(k3_zfmisc_1(A_2060,B_2058,C_2056)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_61439])).

tff(c_66572,plain,(
    ! [C_2057,D_2061] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(C_2057,D_2061))
      | r1_tarski('#skF_9',D_2061)
      | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60895,c_66502])).

tff(c_66606,plain,(
    ! [C_2062,D_2063] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1(C_2062,D_2063))
      | r1_tarski('#skF_9',D_2063) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62356,c_66572])).

tff(c_76411,plain,(
    ! [A_2343,B_2344,C_2345,D_2346] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'),k4_zfmisc_1(A_2343,B_2344,C_2345,D_2346))
      | r1_tarski('#skF_9',D_2346) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_66606])).

tff(c_76466,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_76411])).

tff(c_76475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65393,c_76466])).

tff(c_76476,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_62132])).

tff(c_76541,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_76476,c_38])).

tff(c_76552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_76541])).

tff(c_76554,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_61562])).

tff(c_76576,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_76554,c_38])).

tff(c_76594,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76576,c_54])).

tff(c_76553,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_61562])).

tff(c_76595,plain,(
    ! [A_1] :
      ( A_1 = '#skF_9'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76576,c_38])).

tff(c_76852,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_76553,c_76595])).

tff(c_76856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76594,c_76852])).

tff(c_76858,plain,(
    '#skF_5' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_60765])).

tff(c_76859,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76858,c_54])).

tff(c_132324,plain,(
    ! [A_3760,B_3761,C_3762] : k2_zfmisc_1(k2_zfmisc_1(A_3760,B_3761),C_3762) = k3_zfmisc_1(A_3760,B_3761,C_3762) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_132347,plain,(
    ! [A_3760,B_3761,C_3762] :
      ( v1_xboole_0(k3_zfmisc_1(A_3760,B_3761,C_3762))
      | ~ v1_xboole_0(k2_zfmisc_1(A_3760,B_3761)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132324,c_14])).

tff(c_77216,plain,(
    ! [A_2381,B_2382,C_2383] : k2_zfmisc_1(k2_zfmisc_1(A_2381,B_2382),C_2383) = k3_zfmisc_1(A_2381,B_2382,C_2383) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_77246,plain,(
    ! [A_2381,B_2382,C_2383] :
      ( v1_xboole_0(k3_zfmisc_1(A_2381,B_2382,C_2383))
      | ~ v1_xboole_0(k2_zfmisc_1(A_2381,B_2382)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77216,c_14])).

tff(c_76972,plain,(
    k4_zfmisc_1('#skF_2','#skF_7','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76858,c_60766,c_30])).

tff(c_77293,plain,(
    ! [A_2386,B_2387,C_2388,D_2389] : k2_zfmisc_1(k3_zfmisc_1(A_2386,B_2387,C_2388),D_2389) = k4_zfmisc_1(A_2386,B_2387,C_2388,D_2389) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_77769,plain,(
    ! [A_2444,B_2445,C_2446,D_2447] :
      ( v1_xboole_0(k4_zfmisc_1(A_2444,B_2445,C_2446,D_2447))
      | ~ v1_xboole_0(k3_zfmisc_1(A_2444,B_2445,C_2446)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77293,c_14])).

tff(c_77801,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76972,c_77769])).

tff(c_78048,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_77801])).

tff(c_78055,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_7')) ),
    inference(resolution,[status(thm)],[c_77246,c_78048])).

tff(c_78063,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_78055])).

tff(c_76857,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_60765])).

tff(c_76864,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_76857])).

tff(c_77252,plain,(
    ! [A_17,B_18,C_19,C_2383] : k3_zfmisc_1(k2_zfmisc_1(A_17,B_18),C_19,C_2383) = k2_zfmisc_1(k3_zfmisc_1(A_17,B_18,C_19),C_2383) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77216])).

tff(c_78503,plain,(
    ! [A_17,B_18,C_19,C_2383] : k3_zfmisc_1(k2_zfmisc_1(A_17,B_18),C_19,C_2383) = k4_zfmisc_1(A_17,B_18,C_19,C_2383) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_77252])).

tff(c_76865,plain,(
    ! [A_2362,B_2363] :
      ( k2_zfmisc_1(A_2362,B_2363) = '#skF_1'
      | ~ v1_xboole_0(A_2362) ) ),
    inference(resolution,[status(thm)],[c_55,c_38])).

tff(c_76872,plain,(
    ! [A_6,B_7,B_2363] :
      ( k2_zfmisc_1(k2_zfmisc_1(A_6,B_7),B_2363) = '#skF_1'
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_76865])).

tff(c_77650,plain,(
    ! [A_2427,B_2428,B_2429] :
      ( k3_zfmisc_1(A_2427,B_2428,B_2429) = '#skF_1'
      | ~ v1_xboole_0(A_2427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_76872])).

tff(c_78390,plain,(
    ! [A_2475,B_2476,B_2477,B_2478] :
      ( k3_zfmisc_1(k2_zfmisc_1(A_2475,B_2476),B_2477,B_2478) = '#skF_1'
      | ~ v1_xboole_0(B_2476) ) ),
    inference(resolution,[status(thm)],[c_12,c_77650])).

tff(c_77239,plain,(
    ! [A_2381,B_2382,C_2383] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_2381,B_2382,C_2383))
      | v1_xboole_0(C_2383)
      | v1_xboole_0(k2_zfmisc_1(A_2381,B_2382)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77216,c_20])).

tff(c_78405,plain,(
    ! [B_2478,A_2475,B_2476,B_2477] :
      ( ~ v1_xboole_0('#skF_1')
      | v1_xboole_0(B_2478)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_2475,B_2476),B_2477))
      | ~ v1_xboole_0(B_2476) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78390,c_77239])).

tff(c_78480,plain,(
    ! [B_2478,A_2475,B_2476,B_2477] :
      ( v1_xboole_0(B_2478)
      | v1_xboole_0(k3_zfmisc_1(A_2475,B_2476,B_2477))
      | ~ v1_xboole_0(B_2476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4,c_78405])).

tff(c_78732,plain,(
    ! [A_2494,B_2495,B_2496] :
      ( v1_xboole_0(k3_zfmisc_1(A_2494,B_2495,B_2496))
      | ~ v1_xboole_0(B_2495) ) ),
    inference(splitLeft,[status(thm)],[c_78480])).

tff(c_78762,plain,(
    ! [A_17,B_18,C_19,C_2383] :
      ( v1_xboole_0(k4_zfmisc_1(A_17,B_18,C_19,C_2383))
      | ~ v1_xboole_0(C_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78503,c_78732])).

tff(c_79600,plain,(
    ! [A_2533,B_2534,C_2535,D_2536] :
      ( ~ v1_xboole_0(k4_zfmisc_1(A_2533,B_2534,C_2535,D_2536))
      | v1_xboole_0(D_2536)
      | v1_xboole_0(k3_zfmisc_1(A_2533,B_2534,C_2535)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77293,c_20])).

tff(c_79630,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | v1_xboole_0('#skF_9')
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76972,c_79600])).

tff(c_79646,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | v1_xboole_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_78048,c_79630])).

tff(c_79647,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_79646])).

tff(c_79657,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78762,c_79647])).

tff(c_77323,plain,(
    ! [A_2386,B_2387,C_2388,D_2389] :
      ( v1_xboole_0(k4_zfmisc_1(A_2386,B_2387,C_2388,D_2389))
      | ~ v1_xboole_0(k3_zfmisc_1(A_2386,B_2387,C_2388)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77293,c_14])).

tff(c_79658,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_77323,c_79647])).

tff(c_79674,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_77246,c_79658])).

tff(c_77326,plain,(
    ! [A_2386,B_2387,C_2388,D_2389] :
      ( v1_xboole_0(k4_zfmisc_1(A_2386,B_2387,C_2388,D_2389))
      | ~ v1_xboole_0(D_2389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77293,c_12])).

tff(c_79659,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_77326,c_79647])).

tff(c_77395,plain,(
    ! [B_2394,A_2395,D_2396,C_2397] :
      ( ~ r1_tarski(k2_zfmisc_1(B_2394,A_2395),k2_zfmisc_1(D_2396,C_2397))
      | r1_tarski(B_2394,D_2396)
      | v1_xboole_0(A_2395) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_82684,plain,(
    ! [B_2679,B_2680,A_2682,C_2677,A_2678,D_2681] :
      ( ~ r1_tarski(k2_zfmisc_1(B_2679,A_2678),k4_zfmisc_1(A_2682,B_2680,C_2677,D_2681))
      | r1_tarski(B_2679,k3_zfmisc_1(A_2682,B_2680,C_2677))
      | v1_xboole_0(A_2678) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_77395])).

tff(c_83073,plain,(
    ! [B_2691,A_2692] :
      ( ~ r1_tarski(k2_zfmisc_1(B_2691,A_2692),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(B_2691,k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
      | v1_xboole_0(A_2692) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76972,c_82684])).

tff(c_83629,plain,(
    ! [A_2710,B_2711,C_2712,D_2713] :
      ( ~ r1_tarski(k4_zfmisc_1(A_2710,B_2711,C_2712,D_2713),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(k3_zfmisc_1(A_2710,B_2711,C_2712),k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
      | v1_xboole_0(D_2713) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_83073])).

tff(c_83679,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_83629])).

tff(c_83711,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_79659,c_83679])).

tff(c_77516,plain,(
    ! [A_2410,B_2411,C_2412,D_2413] :
      ( ~ r1_tarski(k2_zfmisc_1(A_2410,B_2411),k2_zfmisc_1(C_2412,D_2413))
      | r1_tarski(B_2411,D_2413)
      | v1_xboole_0(A_2410) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79992,plain,(
    ! [B_2551,B_2548,A_2550,A_2549,C_2547] :
      ( ~ r1_tarski(k2_zfmisc_1(A_2549,B_2548),k3_zfmisc_1(A_2550,B_2551,C_2547))
      | r1_tarski(B_2548,C_2547)
      | v1_xboole_0(A_2549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77516])).

tff(c_88463,plain,(
    ! [B_2825,C_2823,A_2827,B_2826,A_2824,C_2828] :
      ( ~ r1_tarski(k3_zfmisc_1(A_2824,B_2825,C_2823),k3_zfmisc_1(A_2827,B_2826,C_2828))
      | r1_tarski(C_2823,C_2828)
      | v1_xboole_0(k2_zfmisc_1(A_2824,B_2825)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_79992])).

tff(c_88498,plain,
    ( r1_tarski('#skF_4','#skF_8')
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_83711,c_88463])).

tff(c_88588,plain,(
    r1_tarski('#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_79674,c_88498])).

tff(c_88619,plain,
    ( '#skF_8' = '#skF_4'
    | ~ r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_88588,c_6])).

tff(c_88620,plain,(
    ~ r1_tarski('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_88619])).

tff(c_82386,plain,(
    ! [B_2668,C_2667,C_2666,A_2670,D_2671,D_2669] :
      ( ~ r1_tarski(k4_zfmisc_1(A_2670,B_2668,C_2666,D_2669),k2_zfmisc_1(D_2671,C_2667))
      | r1_tarski(k3_zfmisc_1(A_2670,B_2668,C_2666),D_2671)
      | v1_xboole_0(D_2669) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_77395])).

tff(c_105882,plain,(
    ! [C_3196,A_3201,C_3203,B_3199,B_3202,A_3198,D_3197,D_3200] :
      ( ~ r1_tarski(k4_zfmisc_1(A_3198,B_3202,C_3203,D_3197),k4_zfmisc_1(A_3201,B_3199,C_3196,D_3200))
      | r1_tarski(k3_zfmisc_1(A_3198,B_3202,C_3203),k3_zfmisc_1(A_3201,B_3199,C_3196))
      | v1_xboole_0(D_3197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_82386])).

tff(c_106038,plain,(
    ! [A_3201,B_3199,C_3196,D_3200] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_3201,B_3199,C_3196,D_3200))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k3_zfmisc_1(A_3201,B_3199,C_3196))
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76972,c_105882])).

tff(c_106101,plain,(
    ! [A_3204,B_3205,C_3206,D_3207] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_3204,B_3205,C_3206,D_3207))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k3_zfmisc_1(A_3204,B_3205,C_3206)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79659,c_106038])).

tff(c_106199,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_106101])).

tff(c_80043,plain,(
    ! [B_2551,C_19,B_18,A_17,A_2550,C_2547] :
      ( ~ r1_tarski(k3_zfmisc_1(A_17,B_18,C_19),k3_zfmisc_1(A_2550,B_2551,C_2547))
      | r1_tarski(C_19,C_2547)
      | v1_xboole_0(k2_zfmisc_1(A_17,B_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_79992])).

tff(c_106205,plain,
    ( r1_tarski('#skF_8','#skF_4')
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_7')) ),
    inference(resolution,[status(thm)],[c_106199,c_80043])).

tff(c_106217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78055,c_88620,c_106205])).

tff(c_106218,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_88619])).

tff(c_106221,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106218,c_83711])).

tff(c_81477,plain,(
    ! [C_2627,A_2629,A_2628,B_2630,B_2631] :
      ( ~ r1_tarski(k2_zfmisc_1(B_2631,A_2628),k3_zfmisc_1(A_2629,B_2630,C_2627))
      | r1_tarski(B_2631,k2_zfmisc_1(A_2629,B_2630))
      | v1_xboole_0(A_2628) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77395])).

tff(c_111034,plain,(
    ! [C_3339,C_3335,A_3337,B_3338,A_3336,B_3340] :
      ( ~ r1_tarski(k3_zfmisc_1(A_3337,B_3338,C_3335),k3_zfmisc_1(A_3336,B_3340,C_3339))
      | r1_tarski(k2_zfmisc_1(A_3337,B_3338),k2_zfmisc_1(A_3336,B_3340))
      | v1_xboole_0(C_3335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_81477])).

tff(c_111059,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_2','#skF_7'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_106221,c_111034])).

tff(c_111178,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_2','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_79657,c_111059])).

tff(c_111222,plain,
    ( r1_tarski('#skF_3','#skF_7')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_111178,c_18])).

tff(c_111231,plain,(
    r1_tarski('#skF_3','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78063,c_111222])).

tff(c_111240,plain,
    ( '#skF_7' = '#skF_3'
    | ~ r1_tarski('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_111231,c_6])).

tff(c_111245,plain,(
    ~ r1_tarski('#skF_7','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76864,c_111240])).

tff(c_82456,plain,(
    ! [D_2671,C_2667] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(D_2671,C_2667))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_2671)
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76972,c_82386])).

tff(c_82486,plain,(
    ! [D_2672,C_2673] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k2_zfmisc_1(D_2672,C_2673))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),D_2672) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79659,c_82456])).

tff(c_82513,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_20,B_21,C_22,D_23))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_8'),k3_zfmisc_1(A_20,B_21,C_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_82486])).

tff(c_131337,plain,(
    ! [A_3720,B_3721,C_3722,D_3723] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_3720,B_3721,C_3722,D_3723))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_4'),k3_zfmisc_1(A_3720,B_3721,C_3722)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106218,c_82513])).

tff(c_131442,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_7','#skF_4'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_131337])).

tff(c_81542,plain,(
    ! [C_2627,A_2629,B_2630,C_19,B_18,A_17] :
      ( ~ r1_tarski(k3_zfmisc_1(A_17,B_18,C_19),k3_zfmisc_1(A_2629,B_2630,C_2627))
      | r1_tarski(k2_zfmisc_1(A_17,B_18),k2_zfmisc_1(A_2629,B_2630))
      | v1_xboole_0(C_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_81477])).

tff(c_131445,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_7'),k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_131442,c_81542])).

tff(c_131456,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_7'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_79657,c_131445])).

tff(c_131475,plain,
    ( r1_tarski('#skF_7','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_131456,c_18])).

tff(c_131487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78063,c_111245,c_131475])).

tff(c_131488,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_79646])).

tff(c_131520,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_131488,c_38])).

tff(c_131552,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131520,c_76859])).

tff(c_131489,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_79646])).

tff(c_131555,plain,(
    ! [A_1] :
      ( A_1 = '#skF_9'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131520,c_38])).

tff(c_131908,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_131489,c_131555])).

tff(c_131915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131552,c_131908])).

tff(c_131916,plain,(
    ! [B_2478] : v1_xboole_0(B_2478) ),
    inference(splitRight,[status(thm)],[c_78480])).

tff(c_78064,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_78055])).

tff(c_131984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131916,c_78064])).

tff(c_131985,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_77801])).

tff(c_132050,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_131985,c_38])).

tff(c_132061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76859,c_132050])).

tff(c_132063,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76857])).

tff(c_132102,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_8','#skF_9') = k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132063,c_60766,c_76858,c_30])).

tff(c_132424,plain,(
    ! [A_3769,B_3770,C_3771,D_3772] : k2_zfmisc_1(k3_zfmisc_1(A_3769,B_3770,C_3771),D_3772) = k4_zfmisc_1(A_3769,B_3770,C_3771,D_3772) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_133609,plain,(
    ! [A_3857,B_3858,C_3859,D_3860] :
      ( v1_xboole_0(k4_zfmisc_1(A_3857,B_3858,C_3859,D_3860))
      | ~ v1_xboole_0(k3_zfmisc_1(A_3857,B_3858,C_3859)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132424,c_14])).

tff(c_133641,plain,
    ( v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_132102,c_133609])).

tff(c_133752,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_133641])).

tff(c_133763,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_132347,c_133752])).

tff(c_132062,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76857])).

tff(c_132450,plain,(
    ! [A_3769,B_3770,C_3771,D_3772] :
      ( v1_xboole_0(k4_zfmisc_1(A_3769,B_3770,C_3771,D_3772))
      | ~ v1_xboole_0(D_3772) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132424,c_12])).

tff(c_135648,plain,(
    ! [A_3950,B_3951,C_3952,D_3953] :
      ( ~ v1_xboole_0(k4_zfmisc_1(A_3950,B_3951,C_3952,D_3953))
      | v1_xboole_0(D_3953)
      | v1_xboole_0(k3_zfmisc_1(A_3950,B_3951,C_3952)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132424,c_20])).

tff(c_135690,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | v1_xboole_0('#skF_9')
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_132102,c_135648])).

tff(c_135714,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
    | v1_xboole_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_133752,c_135690])).

tff(c_135715,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_135714])).

tff(c_135727,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_132450,c_135715])).

tff(c_132523,plain,(
    ! [B_3782,A_3783,D_3784,C_3785] :
      ( ~ r1_tarski(k2_zfmisc_1(B_3782,A_3783),k2_zfmisc_1(D_3784,C_3785))
      | r1_tarski(B_3782,D_3784)
      | v1_xboole_0(A_3783) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_137988,plain,(
    ! [A_4065,A_4062,B_4063,C_4060,D_4064,B_4061] :
      ( ~ r1_tarski(k2_zfmisc_1(B_4061,A_4062),k4_zfmisc_1(A_4065,B_4063,C_4060,D_4064))
      | r1_tarski(B_4061,k3_zfmisc_1(A_4065,B_4063,C_4060))
      | v1_xboole_0(A_4062) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_132523])).

tff(c_138103,plain,(
    ! [B_4066,A_4067] :
      ( ~ r1_tarski(k2_zfmisc_1(B_4066,A_4067),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(B_4066,k3_zfmisc_1('#skF_2','#skF_3','#skF_8'))
      | v1_xboole_0(A_4067) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132102,c_137988])).

tff(c_139171,plain,(
    ! [A_4101,B_4102,C_4103,D_4104] :
      ( ~ r1_tarski(k4_zfmisc_1(A_4101,B_4102,C_4103,D_4104),k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'))
      | r1_tarski(k3_zfmisc_1(A_4101,B_4102,C_4103),k3_zfmisc_1('#skF_2','#skF_3','#skF_8'))
      | v1_xboole_0(D_4104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_138103])).

tff(c_139221,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_3','#skF_8'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_139171])).

tff(c_139253,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'),k3_zfmisc_1('#skF_2','#skF_3','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_135727,c_139221])).

tff(c_132631,plain,(
    ! [A_3795,B_3796,C_3797,D_3798] :
      ( ~ r1_tarski(k2_zfmisc_1(A_3795,B_3796),k2_zfmisc_1(C_3797,D_3798))
      | r1_tarski(B_3796,D_3798)
      | v1_xboole_0(A_3795) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136332,plain,(
    ! [C_3981,C_3978,B_3980,D_3982,A_3979] :
      ( ~ r1_tarski(k3_zfmisc_1(A_3979,B_3980,C_3978),k2_zfmisc_1(C_3981,D_3982))
      | r1_tarski(C_3978,D_3982)
      | v1_xboole_0(k2_zfmisc_1(A_3979,B_3980)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_132631])).

tff(c_143895,plain,(
    ! [B_4217,C_4220,B_4219,C_4215,A_4216,A_4218] :
      ( ~ r1_tarski(k3_zfmisc_1(A_4218,B_4219,C_4220),k3_zfmisc_1(A_4216,B_4217,C_4215))
      | r1_tarski(C_4220,C_4215)
      | v1_xboole_0(k2_zfmisc_1(A_4218,B_4219)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_136332])).

tff(c_143930,plain,
    ( r1_tarski('#skF_4','#skF_8')
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_139253,c_143895])).

tff(c_144020,plain,(
    r1_tarski('#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_133763,c_143930])).

tff(c_144049,plain,
    ( '#skF_8' = '#skF_4'
    | ~ r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_144020,c_6])).

tff(c_144054,plain,(
    ~ r1_tarski('#skF_8','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_132062,c_144049])).

tff(c_162821,plain,(
    ! [C_4607,D_4608,A_4613,B_4609,B_4610,A_4612,C_4606,D_4611] :
      ( ~ r1_tarski(k4_zfmisc_1(A_4612,B_4610,C_4606,D_4611),k4_zfmisc_1(A_4613,B_4609,C_4607,D_4608))
      | r1_tarski(k3_zfmisc_1(A_4612,B_4610,C_4606),k3_zfmisc_1(A_4613,B_4609,C_4607))
      | v1_xboole_0(D_4611) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_137988])).

tff(c_162965,plain,(
    ! [A_4613,B_4609,C_4607,D_4608] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_4613,B_4609,C_4607,D_4608))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),k3_zfmisc_1(A_4613,B_4609,C_4607))
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132102,c_162821])).

tff(c_163284,plain,(
    ! [A_4620,B_4621,C_4622,D_4623] :
      ( ~ r1_tarski(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9'),k4_zfmisc_1(A_4620,B_4621,C_4622,D_4623))
      | r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),k3_zfmisc_1(A_4620,B_4621,C_4622)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_135727,c_162965])).

tff(c_163376,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_3','#skF_8'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_163284])).

tff(c_136392,plain,(
    ! [C_3978,B_3980,C_19,B_18,A_17,A_3979] :
      ( ~ r1_tarski(k3_zfmisc_1(A_3979,B_3980,C_3978),k3_zfmisc_1(A_17,B_18,C_19))
      | r1_tarski(C_3978,C_19)
      | v1_xboole_0(k2_zfmisc_1(A_3979,B_3980)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_136332])).

tff(c_163382,plain,
    ( r1_tarski('#skF_8','#skF_4')
    | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_163376,c_136392])).

tff(c_163394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133763,c_144054,c_163382])).

tff(c_163395,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_135714])).

tff(c_163427,plain,(
    '#skF_1' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_163395,c_38])).

tff(c_163465,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163427,c_76859])).

tff(c_163396,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_135714])).

tff(c_163468,plain,(
    ! [A_1] :
      ( A_1 = '#skF_9'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163427,c_38])).

tff(c_163886,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_163396,c_163468])).

tff(c_163893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163465,c_163886])).

tff(c_163894,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_133641])).

tff(c_163977,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_9') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_163894,c_38])).

tff(c_163989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76859,c_163977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:16:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.00/14.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.27/14.27  
% 24.27/14.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.27/14.27  %$ r1_tarski > v1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 24.27/14.27  
% 24.27/14.27  %Foreground sorts:
% 24.27/14.27  
% 24.27/14.27  
% 24.27/14.27  %Background operators:
% 24.27/14.27  
% 24.27/14.27  
% 24.27/14.27  %Foreground operators:
% 24.27/14.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.27/14.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.27/14.27  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 24.27/14.27  tff('#skF_7', type, '#skF_7': $i).
% 24.27/14.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.27/14.27  tff('#skF_5', type, '#skF_5': $i).
% 24.27/14.27  tff('#skF_6', type, '#skF_6': $i).
% 24.27/14.27  tff('#skF_2', type, '#skF_2': $i).
% 24.27/14.27  tff('#skF_3', type, '#skF_3': $i).
% 24.27/14.27  tff('#skF_1', type, '#skF_1': $i).
% 24.27/14.27  tff('#skF_9', type, '#skF_9': $i).
% 24.27/14.27  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 24.27/14.27  tff('#skF_8', type, '#skF_8': $i).
% 24.27/14.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.27/14.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.27/14.27  tff('#skF_4', type, '#skF_4': $i).
% 24.27/14.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.27/14.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 24.27/14.27  
% 24.48/14.31  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 24.48/14.31  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 24.48/14.31  tff(f_81, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 24.48/14.31  tff(f_66, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 24.48/14.31  tff(f_41, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 24.48/14.31  tff(f_45, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 24.48/14.31  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_subset_1)).
% 24.48/14.31  tff(f_68, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 24.48/14.31  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.48/14.31  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 24.48/14.31  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.48/14.31  tff(c_33, plain, (![A_25]: (k1_xboole_0=A_25 | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.48/14.31  tff(c_37, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_33])).
% 24.48/14.31  tff(c_28, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.48/14.31  tff(c_54, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37, c_28])).
% 24.48/14.31  tff(c_22, plain, (![A_17, B_18, C_19]: (k2_zfmisc_1(k2_zfmisc_1(A_17, B_18), C_19)=k3_zfmisc_1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.48/14.31  tff(c_12, plain, (![A_4, B_5]: (v1_xboole_0(k2_zfmisc_1(A_4, B_5)) | ~v1_xboole_0(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 24.48/14.31  tff(c_14, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 24.48/14.31  tff(c_55, plain, (![A_29, B_30]: (v1_xboole_0(k2_zfmisc_1(A_29, B_30)) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 24.48/14.31  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.48/14.31  tff(c_38, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_2])).
% 24.48/14.31  tff(c_87, plain, (![A_34, B_35]: (k2_zfmisc_1(A_34, B_35)='#skF_1' | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_55, c_38])).
% 24.48/14.31  tff(c_94, plain, (![A_6, B_7, B_35]: (k2_zfmisc_1(k2_zfmisc_1(A_6, B_7), B_35)='#skF_1' | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_14, c_87])).
% 24.48/14.31  tff(c_820, plain, (![A_92, B_93, B_94]: (k3_zfmisc_1(A_92, B_93, B_94)='#skF_1' | ~v1_xboole_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_94])).
% 24.48/14.31  tff(c_1507, plain, (![A_143, B_144, B_145, B_146]: (k3_zfmisc_1(k2_zfmisc_1(A_143, B_144), B_145, B_146)='#skF_1' | ~v1_xboole_0(B_144))), inference(resolution, [status(thm)], [c_12, c_820])).
% 24.48/14.31  tff(c_437, plain, (![A_53, B_54, C_55]: (k2_zfmisc_1(k2_zfmisc_1(A_53, B_54), C_55)=k3_zfmisc_1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.48/14.31  tff(c_20, plain, (![A_15, B_16]: (~v1_xboole_0(k2_zfmisc_1(A_15, B_16)) | v1_xboole_0(B_16) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 24.48/14.31  tff(c_460, plain, (![A_53, B_54, C_55]: (~v1_xboole_0(k3_zfmisc_1(A_53, B_54, C_55)) | v1_xboole_0(C_55) | v1_xboole_0(k2_zfmisc_1(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_437, c_20])).
% 24.48/14.31  tff(c_1519, plain, (![B_146, A_143, B_144, B_145]: (~v1_xboole_0('#skF_1') | v1_xboole_0(B_146) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_143, B_144), B_145)) | ~v1_xboole_0(B_144))), inference(superposition, [status(thm), theory('equality')], [c_1507, c_460])).
% 24.48/14.31  tff(c_1590, plain, (![B_146, A_143, B_144, B_145]: (v1_xboole_0(B_146) | v1_xboole_0(k3_zfmisc_1(A_143, B_144, B_145)) | ~v1_xboole_0(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4, c_1519])).
% 24.48/14.31  tff(c_1833, plain, (![A_143, B_144, B_145]: (v1_xboole_0(k3_zfmisc_1(A_143, B_144, B_145)) | ~v1_xboole_0(B_144))), inference(splitLeft, [status(thm)], [c_1590])).
% 24.48/14.31  tff(c_552, plain, (![A_62, B_63, C_64, D_65]: (k2_zfmisc_1(k3_zfmisc_1(A_62, B_63, C_64), D_65)=k4_zfmisc_1(A_62, B_63, C_64, D_65))), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.48/14.31  tff(c_582, plain, (![A_62, B_63, C_64, D_65]: (v1_xboole_0(k4_zfmisc_1(A_62, B_63, C_64, D_65)) | ~v1_xboole_0(k3_zfmisc_1(A_62, B_63, C_64)))), inference(superposition, [status(thm), theory('equality')], [c_552, c_14])).
% 24.48/14.31  tff(c_30, plain, (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.48/14.31  tff(c_991, plain, (![A_116, B_117, C_118, D_119]: (v1_xboole_0(k4_zfmisc_1(A_116, B_117, C_118, D_119)) | ~v1_xboole_0(k3_zfmisc_1(A_116, B_117, C_118)))), inference(superposition, [status(thm), theory('equality')], [c_552, c_14])).
% 24.48/14.31  tff(c_1023, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_991])).
% 24.48/14.31  tff(c_1270, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_1023])).
% 24.48/14.31  tff(c_848, plain, (![A_98, B_99, C_100, D_101]: (v1_xboole_0(k4_zfmisc_1(A_98, B_99, C_100, D_101)) | ~v1_xboole_0(D_101))), inference(superposition, [status(thm), theory('equality')], [c_552, c_12])).
% 24.48/14.31  tff(c_876, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_30, c_848])).
% 24.48/14.31  tff(c_888, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_876])).
% 24.48/14.31  tff(c_2969, plain, (![A_220, B_221, C_222, D_223]: (~v1_xboole_0(k4_zfmisc_1(A_220, B_221, C_222, D_223)) | v1_xboole_0(D_223) | v1_xboole_0(k3_zfmisc_1(A_220, B_221, C_222)))), inference(superposition, [status(thm), theory('equality')], [c_552, c_20])).
% 24.48/14.31  tff(c_2999, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0('#skF_9') | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2969])).
% 24.48/14.31  tff(c_3015, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1270, c_888, c_2999])).
% 24.48/14.31  tff(c_3026, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_582, c_3015])).
% 24.48/14.31  tff(c_3037, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1833, c_3026])).
% 24.48/14.31  tff(c_26, plain, ('#skF_5'!='#skF_9' | '#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.48/14.31  tff(c_70, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 24.48/14.31  tff(c_24, plain, (![A_20, B_21, C_22, D_23]: (k2_zfmisc_1(k3_zfmisc_1(A_20, B_21, C_22), D_23)=k4_zfmisc_1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.48/14.31  tff(c_473, plain, (![A_17, B_18, C_19, C_55]: (k3_zfmisc_1(k2_zfmisc_1(A_17, B_18), C_19, C_55)=k2_zfmisc_1(k3_zfmisc_1(A_17, B_18, C_19), C_55))), inference(superposition, [status(thm), theory('equality')], [c_22, c_437])).
% 24.48/14.31  tff(c_1612, plain, (![A_17, B_18, C_19, C_55]: (k3_zfmisc_1(k2_zfmisc_1(A_17, B_18), C_19, C_55)=k4_zfmisc_1(A_17, B_18, C_19, C_55))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_473])).
% 24.48/14.31  tff(c_1834, plain, (![A_164, B_165, B_166]: (v1_xboole_0(k3_zfmisc_1(A_164, B_165, B_166)) | ~v1_xboole_0(B_165))), inference(splitLeft, [status(thm)], [c_1590])).
% 24.48/14.31  tff(c_1864, plain, (![A_17, B_18, C_19, C_55]: (v1_xboole_0(k4_zfmisc_1(A_17, B_18, C_19, C_55)) | ~v1_xboole_0(C_19))), inference(superposition, [status(thm), theory('equality')], [c_1612, c_1834])).
% 24.48/14.31  tff(c_3025, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1864, c_3015])).
% 24.48/14.31  tff(c_467, plain, (![A_53, B_54, C_55]: (v1_xboole_0(k3_zfmisc_1(A_53, B_54, C_55)) | ~v1_xboole_0(k2_zfmisc_1(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_437, c_14])).
% 24.48/14.31  tff(c_1277, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_467, c_1270])).
% 24.48/14.31  tff(c_3038, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_467, c_3026])).
% 24.48/14.31  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.48/14.31  tff(c_776, plain, (![A_88, B_89, C_90, D_91]: (~r1_tarski(k2_zfmisc_1(A_88, B_89), k2_zfmisc_1(C_90, D_91)) | r1_tarski(B_89, D_91) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.31  tff(c_3635, plain, (![B_243, B_244, A_245, C_242, A_247, D_246]: (~r1_tarski(k2_zfmisc_1(A_245, B_244), k4_zfmisc_1(A_247, B_243, C_242, D_246)) | r1_tarski(B_244, D_246) | v1_xboole_0(A_245))), inference(superposition, [status(thm), theory('equality')], [c_24, c_776])).
% 24.48/14.31  tff(c_3741, plain, (![A_249, B_250]: (~r1_tarski(k2_zfmisc_1(A_249, B_250), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(B_250, '#skF_9') | v1_xboole_0(A_249))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3635])).
% 24.48/14.31  tff(c_4651, plain, (![A_302, B_303, C_304, D_305]: (~r1_tarski(k4_zfmisc_1(A_302, B_303, C_304, D_305), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(D_305, '#skF_9') | v1_xboole_0(k3_zfmisc_1(A_302, B_303, C_304)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3741])).
% 24.48/14.31  tff(c_4686, plain, (r1_tarski('#skF_5', '#skF_9') | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_4651])).
% 24.48/14.31  tff(c_4708, plain, (r1_tarski('#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_3026, c_4686])).
% 24.48/14.31  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.48/14.31  tff(c_4715, plain, ('#skF_5'='#skF_9' | ~r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_4708, c_6])).
% 24.48/14.31  tff(c_4716, plain, (~r1_tarski('#skF_9', '#skF_5')), inference(splitLeft, [status(thm)], [c_4715])).
% 24.48/14.31  tff(c_4764, plain, (![D_312, B_311, C_314, A_313, D_310, C_309]: (~r1_tarski(k4_zfmisc_1(A_313, B_311, C_309, D_312), k2_zfmisc_1(C_314, D_310)) | r1_tarski(D_312, D_310) | v1_xboole_0(k3_zfmisc_1(A_313, B_311, C_309)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_776])).
% 24.48/14.31  tff(c_18306, plain, (![B_707, A_708, A_706, B_704, C_701, C_703, D_702, D_705]: (~r1_tarski(k4_zfmisc_1(A_708, B_707, C_703, D_702), k4_zfmisc_1(A_706, B_704, C_701, D_705)) | r1_tarski(D_702, D_705) | v1_xboole_0(k3_zfmisc_1(A_708, B_707, C_703)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4764])).
% 24.48/14.31  tff(c_18410, plain, (![A_706, B_704, C_701, D_705]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k4_zfmisc_1(A_706, B_704, C_701, D_705)) | r1_tarski('#skF_9', D_705) | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_30, c_18306])).
% 24.48/14.31  tff(c_18840, plain, (![A_715, B_716, C_717, D_718]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k4_zfmisc_1(A_715, B_716, C_717, D_718)) | r1_tarski('#skF_9', D_718))), inference(negUnitSimplification, [status(thm)], [c_1270, c_18410])).
% 24.48/14.31  tff(c_18901, plain, (r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_18840])).
% 24.48/14.31  tff(c_18910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4716, c_18901])).
% 24.48/14.31  tff(c_18911, plain, ('#skF_5'='#skF_9'), inference(splitRight, [status(thm)], [c_4715])).
% 24.48/14.31  tff(c_18919, plain, (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_18911, c_30])).
% 24.48/14.31  tff(c_624, plain, (![B_69, A_70, D_71, C_72]: (~r1_tarski(k2_zfmisc_1(B_69, A_70), k2_zfmisc_1(D_71, C_72)) | r1_tarski(B_69, D_71) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.31  tff(c_630, plain, (![C_22, D_23, A_70, A_20, B_21, B_69]: (~r1_tarski(k2_zfmisc_1(B_69, A_70), k4_zfmisc_1(A_20, B_21, C_22, D_23)) | r1_tarski(B_69, k3_zfmisc_1(A_20, B_21, C_22)) | v1_xboole_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_24, c_624])).
% 24.48/14.31  tff(c_19677, plain, (![B_755, A_756]: (~r1_tarski(k2_zfmisc_1(B_755, A_756), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(B_755, k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0(A_756))), inference(superposition, [status(thm), theory('equality')], [c_18919, c_630])).
% 24.48/14.31  tff(c_27981, plain, (![A_985, B_986, C_987, D_988]: (~r1_tarski(k4_zfmisc_1(A_985, B_986, C_987, D_988), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(k3_zfmisc_1(A_985, B_986, C_987), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0(D_988))), inference(superposition, [status(thm), theory('equality')], [c_24, c_19677])).
% 24.48/14.31  tff(c_28035, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_10, c_27981])).
% 24.48/14.31  tff(c_28066, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_888, c_28035])).
% 24.48/14.31  tff(c_2679, plain, (![A_202, B_204, B_203, A_205, C_201]: (~r1_tarski(k2_zfmisc_1(A_205, B_204), k3_zfmisc_1(A_202, B_203, C_201)) | r1_tarski(B_204, C_201) | v1_xboole_0(A_205))), inference(superposition, [status(thm), theory('equality')], [c_22, c_776])).
% 24.48/14.31  tff(c_2724, plain, (![A_202, B_203, C_19, B_18, A_17, C_201]: (~r1_tarski(k3_zfmisc_1(A_17, B_18, C_19), k3_zfmisc_1(A_202, B_203, C_201)) | r1_tarski(C_19, C_201) | v1_xboole_0(k2_zfmisc_1(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2679])).
% 24.48/14.31  tff(c_28069, plain, (r1_tarski('#skF_4', '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_28066, c_2724])).
% 24.48/14.31  tff(c_28077, plain, (r1_tarski('#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_3038, c_28069])).
% 24.48/14.31  tff(c_28086, plain, ('#skF_8'='#skF_4' | ~r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_28077, c_6])).
% 24.48/14.31  tff(c_28087, plain, (~r1_tarski('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_28086])).
% 24.48/14.31  tff(c_18982, plain, (![B_725, A_727, B_724, A_723, C_722, D_726]: (~r1_tarski(k2_zfmisc_1(B_724, A_723), k4_zfmisc_1(A_727, B_725, C_722, D_726)) | r1_tarski(B_724, k3_zfmisc_1(A_727, B_725, C_722)) | v1_xboole_0(A_723))), inference(superposition, [status(thm), theory('equality')], [c_24, c_624])).
% 24.48/14.31  tff(c_39338, plain, (![A_1262, B_1259, A_1257, B_1258, D_1260, C_1256, D_1261, C_1263]: (~r1_tarski(k4_zfmisc_1(A_1262, B_1259, C_1256, D_1261), k4_zfmisc_1(A_1257, B_1258, C_1263, D_1260)) | r1_tarski(k3_zfmisc_1(A_1262, B_1259, C_1256), k3_zfmisc_1(A_1257, B_1258, C_1263)) | v1_xboole_0(D_1261))), inference(superposition, [status(thm), theory('equality')], [c_24, c_18982])).
% 24.48/14.31  tff(c_39419, plain, (![A_1257, B_1258, C_1263, D_1260]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_1257, B_1258, C_1263, D_1260)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k3_zfmisc_1(A_1257, B_1258, C_1263)) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_18919, c_39338])).
% 24.48/14.31  tff(c_40809, plain, (![A_1278, B_1279, C_1280, D_1281]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_1278, B_1279, C_1280, D_1281)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k3_zfmisc_1(A_1278, B_1279, C_1280)))), inference(negUnitSimplification, [status(thm)], [c_888, c_39419])).
% 24.48/14.31  tff(c_40890, plain, (r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_40809])).
% 24.48/14.31  tff(c_40896, plain, (r1_tarski('#skF_8', '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_40890, c_2724])).
% 24.48/14.31  tff(c_40908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1277, c_28087, c_40896])).
% 24.48/14.31  tff(c_40909, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_28086])).
% 24.48/14.31  tff(c_40912, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40909, c_28066])).
% 24.48/14.31  tff(c_4179, plain, (![A_274, C_273, C_277, B_275, D_276]: (~r1_tarski(k3_zfmisc_1(A_274, B_275, C_273), k2_zfmisc_1(D_276, C_277)) | r1_tarski(k2_zfmisc_1(A_274, B_275), D_276) | v1_xboole_0(C_273))), inference(superposition, [status(thm), theory('equality')], [c_22, c_624])).
% 24.48/14.31  tff(c_44324, plain, (![B_1384, A_1379, C_1383, C_1380, B_1382, A_1381]: (~r1_tarski(k3_zfmisc_1(A_1379, B_1384, C_1383), k3_zfmisc_1(A_1381, B_1382, C_1380)) | r1_tarski(k2_zfmisc_1(A_1379, B_1384), k2_zfmisc_1(A_1381, B_1382)) | v1_xboole_0(C_1383))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4179])).
% 24.48/14.31  tff(c_44343, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_7')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40912, c_44324])).
% 24.48/14.31  tff(c_44460, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_3025, c_44343])).
% 24.48/14.31  tff(c_16, plain, (![B_12, A_8, D_14, C_13]: (~r1_tarski(k2_zfmisc_1(B_12, A_8), k2_zfmisc_1(D_14, C_13)) | r1_tarski(B_12, D_14) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.31  tff(c_44507, plain, (r1_tarski('#skF_2', '#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44460, c_16])).
% 24.48/14.31  tff(c_44516, plain, (r1_tarski('#skF_2', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_3037, c_44507])).
% 24.48/14.31  tff(c_44529, plain, ('#skF_6'='#skF_2' | ~r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_44516, c_6])).
% 24.48/14.31  tff(c_44534, plain, (~r1_tarski('#skF_6', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_44529])).
% 24.48/14.31  tff(c_1285, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_14, c_1277])).
% 24.48/14.31  tff(c_3046, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_3038])).
% 24.48/14.31  tff(c_18, plain, (![A_8, B_12, C_13, D_14]: (~r1_tarski(k2_zfmisc_1(A_8, B_12), k2_zfmisc_1(C_13, D_14)) | r1_tarski(B_12, D_14) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.31  tff(c_44504, plain, (r1_tarski('#skF_3', '#skF_7') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44460, c_18])).
% 24.48/14.31  tff(c_44513, plain, (r1_tarski('#skF_3', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3046, c_44504])).
% 24.48/14.31  tff(c_44524, plain, ('#skF_7'='#skF_3' | ~r1_tarski('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_44513, c_6])).
% 24.48/14.31  tff(c_44539, plain, (~r1_tarski('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_44524])).
% 24.48/14.31  tff(c_40917, plain, (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_4', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_40909, c_18919])).
% 24.48/14.31  tff(c_51839, plain, (![C_1548, B_1544, B_1543, D_1545, A_1542, C_1541, A_1547, D_1546]: (~r1_tarski(k4_zfmisc_1(A_1547, B_1544, C_1541, D_1546), k4_zfmisc_1(A_1542, B_1543, C_1548, D_1545)) | r1_tarski(k3_zfmisc_1(A_1547, B_1544, C_1541), k3_zfmisc_1(A_1542, B_1543, C_1548)) | v1_xboole_0(D_1546))), inference(superposition, [status(thm), theory('equality')], [c_24, c_18982])).
% 24.48/14.31  tff(c_51874, plain, (![A_1542, B_1543, C_1548, D_1545]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_1542, B_1543, C_1548, D_1545)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_4'), k3_zfmisc_1(A_1542, B_1543, C_1548)) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_40917, c_51839])).
% 24.48/14.31  tff(c_52796, plain, (![A_1561, B_1562, C_1563, D_1564]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_1561, B_1562, C_1563, D_1564)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_4'), k3_zfmisc_1(A_1561, B_1562, C_1563)))), inference(negUnitSimplification, [status(thm)], [c_888, c_51874])).
% 24.48/14.31  tff(c_52877, plain, (r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_52796])).
% 24.48/14.31  tff(c_4234, plain, (![A_274, C_273, C_19, B_275, B_18, A_17]: (~r1_tarski(k3_zfmisc_1(A_274, B_275, C_273), k3_zfmisc_1(A_17, B_18, C_19)) | r1_tarski(k2_zfmisc_1(A_274, B_275), k2_zfmisc_1(A_17, B_18)) | v1_xboole_0(C_273))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4179])).
% 24.48/14.31  tff(c_52880, plain, (r1_tarski(k2_zfmisc_1('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_52877, c_4234])).
% 24.48/14.31  tff(c_52891, plain, (r1_tarski(k2_zfmisc_1('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3025, c_52880])).
% 24.48/14.31  tff(c_52910, plain, (r1_tarski('#skF_7', '#skF_3') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_52891, c_18])).
% 24.48/14.31  tff(c_52922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1285, c_44539, c_52910])).
% 24.48/14.31  tff(c_52923, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_44524])).
% 24.48/14.31  tff(c_52929, plain, (k4_zfmisc_1('#skF_6', '#skF_3', '#skF_4', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_52923, c_40917])).
% 24.48/14.31  tff(c_19889, plain, (![A_767, C_764, B_765, C_762, D_766, D_763]: (~r1_tarski(k4_zfmisc_1(A_767, B_765, C_762, D_766), k2_zfmisc_1(D_763, C_764)) | r1_tarski(k3_zfmisc_1(A_767, B_765, C_762), D_763) | v1_xboole_0(D_766))), inference(superposition, [status(thm), theory('equality')], [c_24, c_624])).
% 24.48/14.31  tff(c_58965, plain, (![D_1702, B_1701, A_1703, A_1698, D_1700, C_1704, B_1699, C_1697]: (~r1_tarski(k4_zfmisc_1(A_1698, B_1699, C_1704, D_1700), k4_zfmisc_1(A_1703, B_1701, C_1697, D_1702)) | r1_tarski(k3_zfmisc_1(A_1698, B_1699, C_1704), k3_zfmisc_1(A_1703, B_1701, C_1697)) | v1_xboole_0(D_1700))), inference(superposition, [status(thm), theory('equality')], [c_24, c_19889])).
% 24.48/14.31  tff(c_58990, plain, (![A_1703, B_1701, C_1697, D_1702]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_1703, B_1701, C_1697, D_1702)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_3', '#skF_4'), k3_zfmisc_1(A_1703, B_1701, C_1697)) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_52929, c_58965])).
% 24.48/14.31  tff(c_60160, plain, (![A_1719, B_1720, C_1721, D_1722]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_1719, B_1720, C_1721, D_1722)) | r1_tarski(k3_zfmisc_1('#skF_6', '#skF_3', '#skF_4'), k3_zfmisc_1(A_1719, B_1720, C_1721)))), inference(negUnitSimplification, [status(thm)], [c_888, c_58990])).
% 24.48/14.31  tff(c_60241, plain, (r1_tarski(k3_zfmisc_1('#skF_6', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_60160])).
% 24.48/14.31  tff(c_60244, plain, (r1_tarski(k2_zfmisc_1('#skF_6', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_60241, c_4234])).
% 24.48/14.31  tff(c_60255, plain, (r1_tarski(k2_zfmisc_1('#skF_6', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3025, c_60244])).
% 24.48/14.31  tff(c_60277, plain, (r1_tarski('#skF_6', '#skF_2') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60255, c_16])).
% 24.48/14.31  tff(c_60289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3037, c_44534, c_60277])).
% 24.48/14.31  tff(c_60290, plain, (![B_146]: (v1_xboole_0(B_146))), inference(splitRight, [status(thm)], [c_1590])).
% 24.48/14.31  tff(c_1286, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_12, c_1277])).
% 24.48/14.31  tff(c_60360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60290, c_1286])).
% 24.48/14.31  tff(c_60361, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1023])).
% 24.48/14.31  tff(c_60465, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_1'), inference(resolution, [status(thm)], [c_60361, c_38])).
% 24.48/14.31  tff(c_60476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_60465])).
% 24.48/14.31  tff(c_60478, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_876])).
% 24.48/14.31  tff(c_60497, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_60478, c_38])).
% 24.48/14.31  tff(c_60514, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_60497, c_54])).
% 24.48/14.31  tff(c_60477, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_876])).
% 24.48/14.31  tff(c_60629, plain, (![A_1728]: (A_1728='#skF_9' | ~v1_xboole_0(A_1728))), inference(demodulation, [status(thm), theory('equality')], [c_60497, c_38])).
% 24.48/14.31  tff(c_60648, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_60477, c_60629])).
% 24.48/14.31  tff(c_60764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60514, c_60648])).
% 24.48/14.31  tff(c_60765, plain, ('#skF_7'!='#skF_3' | '#skF_8'!='#skF_4' | '#skF_5'!='#skF_9'), inference(splitRight, [status(thm)], [c_26])).
% 24.48/14.31  tff(c_60787, plain, ('#skF_5'!='#skF_9'), inference(splitLeft, [status(thm)], [c_60765])).
% 24.48/14.31  tff(c_61216, plain, (![A_1767, B_1768, C_1769, D_1770]: (k2_zfmisc_1(k3_zfmisc_1(A_1767, B_1768, C_1769), D_1770)=k4_zfmisc_1(A_1767, B_1768, C_1769, D_1770))), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.48/14.31  tff(c_61246, plain, (![A_1767, B_1768, C_1769, D_1770]: (v1_xboole_0(k4_zfmisc_1(A_1767, B_1768, C_1769, D_1770)) | ~v1_xboole_0(k3_zfmisc_1(A_1767, B_1768, C_1769)))), inference(superposition, [status(thm), theory('equality')], [c_61216, c_14])).
% 24.48/14.31  tff(c_60766, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 24.48/14.31  tff(c_60895, plain, (k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60766, c_30])).
% 24.48/14.31  tff(c_62100, plain, (![A_1845, B_1846, C_1847, D_1848]: (v1_xboole_0(k4_zfmisc_1(A_1845, B_1846, C_1847, D_1848)) | ~v1_xboole_0(k3_zfmisc_1(A_1845, B_1846, C_1847)))), inference(superposition, [status(thm), theory('equality')], [c_61216, c_14])).
% 24.48/14.31  tff(c_62132, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_60895, c_62100])).
% 24.48/14.31  tff(c_62356, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_62132])).
% 24.48/14.31  tff(c_61536, plain, (![A_1804, B_1805, C_1806, D_1807]: (v1_xboole_0(k4_zfmisc_1(A_1804, B_1805, C_1806, D_1807)) | ~v1_xboole_0(D_1807))), inference(superposition, [status(thm), theory('equality')], [c_61216, c_12])).
% 24.48/14.31  tff(c_61562, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_60895, c_61536])).
% 24.48/14.31  tff(c_61607, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_61562])).
% 24.48/14.31  tff(c_63946, plain, (![A_1927, B_1928, C_1929, D_1930]: (~v1_xboole_0(k4_zfmisc_1(A_1927, B_1928, C_1929, D_1930)) | v1_xboole_0(D_1930) | v1_xboole_0(k3_zfmisc_1(A_1927, B_1928, C_1929)))), inference(superposition, [status(thm), theory('equality')], [c_61216, c_20])).
% 24.48/14.31  tff(c_63979, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0('#skF_9') | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_60895, c_63946])).
% 24.48/14.31  tff(c_63997, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62356, c_61607, c_63979])).
% 24.48/14.31  tff(c_64025, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_61246, c_63997])).
% 24.48/14.31  tff(c_61439, plain, (![A_1791, B_1792, C_1793, D_1794]: (~r1_tarski(k2_zfmisc_1(A_1791, B_1792), k2_zfmisc_1(C_1793, D_1794)) | r1_tarski(B_1792, D_1794) | v1_xboole_0(A_1791))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.31  tff(c_64340, plain, (![A_1955, B_1954, A_1958, D_1957, B_1956, C_1953]: (~r1_tarski(k2_zfmisc_1(A_1955, B_1954), k4_zfmisc_1(A_1958, B_1956, C_1953, D_1957)) | r1_tarski(B_1954, D_1957) | v1_xboole_0(A_1955))), inference(superposition, [status(thm), theory('equality')], [c_24, c_61439])).
% 24.48/14.31  tff(c_64554, plain, (![A_1966, B_1967]: (~r1_tarski(k2_zfmisc_1(A_1966, B_1967), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(B_1967, '#skF_9') | v1_xboole_0(A_1966))), inference(superposition, [status(thm), theory('equality')], [c_60895, c_64340])).
% 24.48/14.31  tff(c_65326, plain, (![A_2009, B_2010, C_2011, D_2012]: (~r1_tarski(k4_zfmisc_1(A_2009, B_2010, C_2011, D_2012), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')) | r1_tarski(D_2012, '#skF_9') | v1_xboole_0(k3_zfmisc_1(A_2009, B_2010, C_2011)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_64554])).
% 24.48/14.31  tff(c_65361, plain, (r1_tarski('#skF_5', '#skF_9') | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_65326])).
% 24.48/14.32  tff(c_65383, plain, (r1_tarski('#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_64025, c_65361])).
% 24.48/14.32  tff(c_65388, plain, ('#skF_5'='#skF_9' | ~r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_65383, c_6])).
% 24.48/14.32  tff(c_65393, plain, (~r1_tarski('#skF_9', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60787, c_65388])).
% 24.48/14.32  tff(c_66502, plain, (![D_2059, B_2058, A_2060, D_2061, C_2057, C_2056]: (~r1_tarski(k4_zfmisc_1(A_2060, B_2058, C_2056, D_2059), k2_zfmisc_1(C_2057, D_2061)) | r1_tarski(D_2059, D_2061) | v1_xboole_0(k3_zfmisc_1(A_2060, B_2058, C_2056)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_61439])).
% 24.48/14.32  tff(c_66572, plain, (![C_2057, D_2061]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(C_2057, D_2061)) | r1_tarski('#skF_9', D_2061) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_60895, c_66502])).
% 24.48/14.32  tff(c_66606, plain, (![C_2062, D_2063]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1(C_2062, D_2063)) | r1_tarski('#skF_9', D_2063))), inference(negUnitSimplification, [status(thm)], [c_62356, c_66572])).
% 24.48/14.32  tff(c_76411, plain, (![A_2343, B_2344, C_2345, D_2346]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), k4_zfmisc_1(A_2343, B_2344, C_2345, D_2346)) | r1_tarski('#skF_9', D_2346))), inference(superposition, [status(thm), theory('equality')], [c_24, c_66606])).
% 24.48/14.32  tff(c_76466, plain, (r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_76411])).
% 24.48/14.32  tff(c_76475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65393, c_76466])).
% 24.48/14.32  tff(c_76476, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_62132])).
% 24.48/14.32  tff(c_76541, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_1'), inference(resolution, [status(thm)], [c_76476, c_38])).
% 24.48/14.32  tff(c_76552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_76541])).
% 24.48/14.32  tff(c_76554, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_61562])).
% 24.48/14.32  tff(c_76576, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_76554, c_38])).
% 24.48/14.32  tff(c_76594, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_76576, c_54])).
% 24.48/14.32  tff(c_76553, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_61562])).
% 24.48/14.32  tff(c_76595, plain, (![A_1]: (A_1='#skF_9' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_76576, c_38])).
% 24.48/14.32  tff(c_76852, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_76553, c_76595])).
% 24.48/14.32  tff(c_76856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76594, c_76852])).
% 24.48/14.32  tff(c_76858, plain, ('#skF_5'='#skF_9'), inference(splitRight, [status(thm)], [c_60765])).
% 24.48/14.32  tff(c_76859, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76858, c_54])).
% 24.48/14.32  tff(c_132324, plain, (![A_3760, B_3761, C_3762]: (k2_zfmisc_1(k2_zfmisc_1(A_3760, B_3761), C_3762)=k3_zfmisc_1(A_3760, B_3761, C_3762))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.48/14.32  tff(c_132347, plain, (![A_3760, B_3761, C_3762]: (v1_xboole_0(k3_zfmisc_1(A_3760, B_3761, C_3762)) | ~v1_xboole_0(k2_zfmisc_1(A_3760, B_3761)))), inference(superposition, [status(thm), theory('equality')], [c_132324, c_14])).
% 24.48/14.32  tff(c_77216, plain, (![A_2381, B_2382, C_2383]: (k2_zfmisc_1(k2_zfmisc_1(A_2381, B_2382), C_2383)=k3_zfmisc_1(A_2381, B_2382, C_2383))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.48/14.32  tff(c_77246, plain, (![A_2381, B_2382, C_2383]: (v1_xboole_0(k3_zfmisc_1(A_2381, B_2382, C_2383)) | ~v1_xboole_0(k2_zfmisc_1(A_2381, B_2382)))), inference(superposition, [status(thm), theory('equality')], [c_77216, c_14])).
% 24.48/14.32  tff(c_76972, plain, (k4_zfmisc_1('#skF_2', '#skF_7', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_76858, c_60766, c_30])).
% 24.48/14.32  tff(c_77293, plain, (![A_2386, B_2387, C_2388, D_2389]: (k2_zfmisc_1(k3_zfmisc_1(A_2386, B_2387, C_2388), D_2389)=k4_zfmisc_1(A_2386, B_2387, C_2388, D_2389))), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.48/14.32  tff(c_77769, plain, (![A_2444, B_2445, C_2446, D_2447]: (v1_xboole_0(k4_zfmisc_1(A_2444, B_2445, C_2446, D_2447)) | ~v1_xboole_0(k3_zfmisc_1(A_2444, B_2445, C_2446)))), inference(superposition, [status(thm), theory('equality')], [c_77293, c_14])).
% 24.48/14.32  tff(c_77801, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_76972, c_77769])).
% 24.48/14.32  tff(c_78048, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_77801])).
% 24.48/14.32  tff(c_78055, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_7'))), inference(resolution, [status(thm)], [c_77246, c_78048])).
% 24.48/14.32  tff(c_78063, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_78055])).
% 24.48/14.32  tff(c_76857, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_60765])).
% 24.48/14.32  tff(c_76864, plain, ('#skF_7'!='#skF_3'), inference(splitLeft, [status(thm)], [c_76857])).
% 24.48/14.32  tff(c_77252, plain, (![A_17, B_18, C_19, C_2383]: (k3_zfmisc_1(k2_zfmisc_1(A_17, B_18), C_19, C_2383)=k2_zfmisc_1(k3_zfmisc_1(A_17, B_18, C_19), C_2383))), inference(superposition, [status(thm), theory('equality')], [c_22, c_77216])).
% 24.48/14.32  tff(c_78503, plain, (![A_17, B_18, C_19, C_2383]: (k3_zfmisc_1(k2_zfmisc_1(A_17, B_18), C_19, C_2383)=k4_zfmisc_1(A_17, B_18, C_19, C_2383))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_77252])).
% 24.48/14.32  tff(c_76865, plain, (![A_2362, B_2363]: (k2_zfmisc_1(A_2362, B_2363)='#skF_1' | ~v1_xboole_0(A_2362))), inference(resolution, [status(thm)], [c_55, c_38])).
% 24.48/14.32  tff(c_76872, plain, (![A_6, B_7, B_2363]: (k2_zfmisc_1(k2_zfmisc_1(A_6, B_7), B_2363)='#skF_1' | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_14, c_76865])).
% 24.48/14.32  tff(c_77650, plain, (![A_2427, B_2428, B_2429]: (k3_zfmisc_1(A_2427, B_2428, B_2429)='#skF_1' | ~v1_xboole_0(A_2427))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_76872])).
% 24.48/14.32  tff(c_78390, plain, (![A_2475, B_2476, B_2477, B_2478]: (k3_zfmisc_1(k2_zfmisc_1(A_2475, B_2476), B_2477, B_2478)='#skF_1' | ~v1_xboole_0(B_2476))), inference(resolution, [status(thm)], [c_12, c_77650])).
% 24.48/14.32  tff(c_77239, plain, (![A_2381, B_2382, C_2383]: (~v1_xboole_0(k3_zfmisc_1(A_2381, B_2382, C_2383)) | v1_xboole_0(C_2383) | v1_xboole_0(k2_zfmisc_1(A_2381, B_2382)))), inference(superposition, [status(thm), theory('equality')], [c_77216, c_20])).
% 24.48/14.32  tff(c_78405, plain, (![B_2478, A_2475, B_2476, B_2477]: (~v1_xboole_0('#skF_1') | v1_xboole_0(B_2478) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_2475, B_2476), B_2477)) | ~v1_xboole_0(B_2476))), inference(superposition, [status(thm), theory('equality')], [c_78390, c_77239])).
% 24.48/14.32  tff(c_78480, plain, (![B_2478, A_2475, B_2476, B_2477]: (v1_xboole_0(B_2478) | v1_xboole_0(k3_zfmisc_1(A_2475, B_2476, B_2477)) | ~v1_xboole_0(B_2476))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4, c_78405])).
% 24.48/14.32  tff(c_78732, plain, (![A_2494, B_2495, B_2496]: (v1_xboole_0(k3_zfmisc_1(A_2494, B_2495, B_2496)) | ~v1_xboole_0(B_2495))), inference(splitLeft, [status(thm)], [c_78480])).
% 24.48/14.32  tff(c_78762, plain, (![A_17, B_18, C_19, C_2383]: (v1_xboole_0(k4_zfmisc_1(A_17, B_18, C_19, C_2383)) | ~v1_xboole_0(C_19))), inference(superposition, [status(thm), theory('equality')], [c_78503, c_78732])).
% 24.48/14.32  tff(c_79600, plain, (![A_2533, B_2534, C_2535, D_2536]: (~v1_xboole_0(k4_zfmisc_1(A_2533, B_2534, C_2535, D_2536)) | v1_xboole_0(D_2536) | v1_xboole_0(k3_zfmisc_1(A_2533, B_2534, C_2535)))), inference(superposition, [status(thm), theory('equality')], [c_77293, c_20])).
% 24.48/14.32  tff(c_79630, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | v1_xboole_0('#skF_9') | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_76972, c_79600])).
% 24.48/14.32  tff(c_79646, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | v1_xboole_0('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_78048, c_79630])).
% 24.48/14.32  tff(c_79647, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitLeft, [status(thm)], [c_79646])).
% 24.48/14.32  tff(c_79657, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78762, c_79647])).
% 24.48/14.32  tff(c_77323, plain, (![A_2386, B_2387, C_2388, D_2389]: (v1_xboole_0(k4_zfmisc_1(A_2386, B_2387, C_2388, D_2389)) | ~v1_xboole_0(k3_zfmisc_1(A_2386, B_2387, C_2388)))), inference(superposition, [status(thm), theory('equality')], [c_77293, c_14])).
% 24.48/14.32  tff(c_79658, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_77323, c_79647])).
% 24.48/14.32  tff(c_79674, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_77246, c_79658])).
% 24.48/14.32  tff(c_77326, plain, (![A_2386, B_2387, C_2388, D_2389]: (v1_xboole_0(k4_zfmisc_1(A_2386, B_2387, C_2388, D_2389)) | ~v1_xboole_0(D_2389))), inference(superposition, [status(thm), theory('equality')], [c_77293, c_12])).
% 24.48/14.32  tff(c_79659, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_77326, c_79647])).
% 24.48/14.32  tff(c_77395, plain, (![B_2394, A_2395, D_2396, C_2397]: (~r1_tarski(k2_zfmisc_1(B_2394, A_2395), k2_zfmisc_1(D_2396, C_2397)) | r1_tarski(B_2394, D_2396) | v1_xboole_0(A_2395))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.32  tff(c_82684, plain, (![B_2679, B_2680, A_2682, C_2677, A_2678, D_2681]: (~r1_tarski(k2_zfmisc_1(B_2679, A_2678), k4_zfmisc_1(A_2682, B_2680, C_2677, D_2681)) | r1_tarski(B_2679, k3_zfmisc_1(A_2682, B_2680, C_2677)) | v1_xboole_0(A_2678))), inference(superposition, [status(thm), theory('equality')], [c_24, c_77395])).
% 24.48/14.32  tff(c_83073, plain, (![B_2691, A_2692]: (~r1_tarski(k2_zfmisc_1(B_2691, A_2692), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(B_2691, k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0(A_2692))), inference(superposition, [status(thm), theory('equality')], [c_76972, c_82684])).
% 24.48/14.32  tff(c_83629, plain, (![A_2710, B_2711, C_2712, D_2713]: (~r1_tarski(k4_zfmisc_1(A_2710, B_2711, C_2712, D_2713), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(k3_zfmisc_1(A_2710, B_2711, C_2712), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0(D_2713))), inference(superposition, [status(thm), theory('equality')], [c_24, c_83073])).
% 24.48/14.32  tff(c_83679, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_10, c_83629])).
% 24.48/14.32  tff(c_83711, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_79659, c_83679])).
% 24.48/14.32  tff(c_77516, plain, (![A_2410, B_2411, C_2412, D_2413]: (~r1_tarski(k2_zfmisc_1(A_2410, B_2411), k2_zfmisc_1(C_2412, D_2413)) | r1_tarski(B_2411, D_2413) | v1_xboole_0(A_2410))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.32  tff(c_79992, plain, (![B_2551, B_2548, A_2550, A_2549, C_2547]: (~r1_tarski(k2_zfmisc_1(A_2549, B_2548), k3_zfmisc_1(A_2550, B_2551, C_2547)) | r1_tarski(B_2548, C_2547) | v1_xboole_0(A_2549))), inference(superposition, [status(thm), theory('equality')], [c_22, c_77516])).
% 24.48/14.32  tff(c_88463, plain, (![B_2825, C_2823, A_2827, B_2826, A_2824, C_2828]: (~r1_tarski(k3_zfmisc_1(A_2824, B_2825, C_2823), k3_zfmisc_1(A_2827, B_2826, C_2828)) | r1_tarski(C_2823, C_2828) | v1_xboole_0(k2_zfmisc_1(A_2824, B_2825)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_79992])).
% 24.48/14.32  tff(c_88498, plain, (r1_tarski('#skF_4', '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_83711, c_88463])).
% 24.48/14.32  tff(c_88588, plain, (r1_tarski('#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_79674, c_88498])).
% 24.48/14.32  tff(c_88619, plain, ('#skF_8'='#skF_4' | ~r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_88588, c_6])).
% 24.48/14.32  tff(c_88620, plain, (~r1_tarski('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_88619])).
% 24.48/14.32  tff(c_82386, plain, (![B_2668, C_2667, C_2666, A_2670, D_2671, D_2669]: (~r1_tarski(k4_zfmisc_1(A_2670, B_2668, C_2666, D_2669), k2_zfmisc_1(D_2671, C_2667)) | r1_tarski(k3_zfmisc_1(A_2670, B_2668, C_2666), D_2671) | v1_xboole_0(D_2669))), inference(superposition, [status(thm), theory('equality')], [c_24, c_77395])).
% 24.48/14.32  tff(c_105882, plain, (![C_3196, A_3201, C_3203, B_3199, B_3202, A_3198, D_3197, D_3200]: (~r1_tarski(k4_zfmisc_1(A_3198, B_3202, C_3203, D_3197), k4_zfmisc_1(A_3201, B_3199, C_3196, D_3200)) | r1_tarski(k3_zfmisc_1(A_3198, B_3202, C_3203), k3_zfmisc_1(A_3201, B_3199, C_3196)) | v1_xboole_0(D_3197))), inference(superposition, [status(thm), theory('equality')], [c_24, c_82386])).
% 24.48/14.32  tff(c_106038, plain, (![A_3201, B_3199, C_3196, D_3200]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_3201, B_3199, C_3196, D_3200)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k3_zfmisc_1(A_3201, B_3199, C_3196)) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_76972, c_105882])).
% 24.48/14.32  tff(c_106101, plain, (![A_3204, B_3205, C_3206, D_3207]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_3204, B_3205, C_3206, D_3207)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k3_zfmisc_1(A_3204, B_3205, C_3206)))), inference(negUnitSimplification, [status(thm)], [c_79659, c_106038])).
% 24.48/14.32  tff(c_106199, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_106101])).
% 24.48/14.32  tff(c_80043, plain, (![B_2551, C_19, B_18, A_17, A_2550, C_2547]: (~r1_tarski(k3_zfmisc_1(A_17, B_18, C_19), k3_zfmisc_1(A_2550, B_2551, C_2547)) | r1_tarski(C_19, C_2547) | v1_xboole_0(k2_zfmisc_1(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_79992])).
% 24.48/14.32  tff(c_106205, plain, (r1_tarski('#skF_8', '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_7'))), inference(resolution, [status(thm)], [c_106199, c_80043])).
% 24.48/14.32  tff(c_106217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78055, c_88620, c_106205])).
% 24.48/14.32  tff(c_106218, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_88619])).
% 24.48/14.32  tff(c_106221, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106218, c_83711])).
% 24.48/14.32  tff(c_81477, plain, (![C_2627, A_2629, A_2628, B_2630, B_2631]: (~r1_tarski(k2_zfmisc_1(B_2631, A_2628), k3_zfmisc_1(A_2629, B_2630, C_2627)) | r1_tarski(B_2631, k2_zfmisc_1(A_2629, B_2630)) | v1_xboole_0(A_2628))), inference(superposition, [status(thm), theory('equality')], [c_22, c_77395])).
% 24.48/14.32  tff(c_111034, plain, (![C_3339, C_3335, A_3337, B_3338, A_3336, B_3340]: (~r1_tarski(k3_zfmisc_1(A_3337, B_3338, C_3335), k3_zfmisc_1(A_3336, B_3340, C_3339)) | r1_tarski(k2_zfmisc_1(A_3337, B_3338), k2_zfmisc_1(A_3336, B_3340)) | v1_xboole_0(C_3335))), inference(superposition, [status(thm), theory('equality')], [c_22, c_81477])).
% 24.48/14.32  tff(c_111059, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_7')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_106221, c_111034])).
% 24.48/14.32  tff(c_111178, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_79657, c_111059])).
% 24.48/14.32  tff(c_111222, plain, (r1_tarski('#skF_3', '#skF_7') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_111178, c_18])).
% 24.48/14.32  tff(c_111231, plain, (r1_tarski('#skF_3', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78063, c_111222])).
% 24.48/14.32  tff(c_111240, plain, ('#skF_7'='#skF_3' | ~r1_tarski('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_111231, c_6])).
% 24.48/14.32  tff(c_111245, plain, (~r1_tarski('#skF_7', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76864, c_111240])).
% 24.48/14.32  tff(c_82456, plain, (![D_2671, C_2667]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(D_2671, C_2667)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_2671) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_76972, c_82386])).
% 24.48/14.32  tff(c_82486, plain, (![D_2672, C_2673]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k2_zfmisc_1(D_2672, C_2673)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), D_2672))), inference(negUnitSimplification, [status(thm)], [c_79659, c_82456])).
% 24.48/14.32  tff(c_82513, plain, (![A_20, B_21, C_22, D_23]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_20, B_21, C_22, D_23)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_8'), k3_zfmisc_1(A_20, B_21, C_22)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_82486])).
% 24.48/14.32  tff(c_131337, plain, (![A_3720, B_3721, C_3722, D_3723]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_3720, B_3721, C_3722, D_3723)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_4'), k3_zfmisc_1(A_3720, B_3721, C_3722)))), inference(demodulation, [status(thm), theory('equality')], [c_106218, c_82513])).
% 24.48/14.32  tff(c_131442, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_7', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_131337])).
% 24.48/14.32  tff(c_81542, plain, (![C_2627, A_2629, B_2630, C_19, B_18, A_17]: (~r1_tarski(k3_zfmisc_1(A_17, B_18, C_19), k3_zfmisc_1(A_2629, B_2630, C_2627)) | r1_tarski(k2_zfmisc_1(A_17, B_18), k2_zfmisc_1(A_2629, B_2630)) | v1_xboole_0(C_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_81477])).
% 24.48/14.32  tff(c_131445, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_7'), k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_131442, c_81542])).
% 24.48/14.32  tff(c_131456, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_7'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_79657, c_131445])).
% 24.48/14.32  tff(c_131475, plain, (r1_tarski('#skF_7', '#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_131456, c_18])).
% 24.48/14.32  tff(c_131487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78063, c_111245, c_131475])).
% 24.48/14.32  tff(c_131488, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_79646])).
% 24.48/14.32  tff(c_131520, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_131488, c_38])).
% 24.48/14.32  tff(c_131552, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_131520, c_76859])).
% 24.48/14.32  tff(c_131489, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitRight, [status(thm)], [c_79646])).
% 24.48/14.32  tff(c_131555, plain, (![A_1]: (A_1='#skF_9' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_131520, c_38])).
% 24.48/14.32  tff(c_131908, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_131489, c_131555])).
% 24.48/14.32  tff(c_131915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131552, c_131908])).
% 24.48/14.32  tff(c_131916, plain, (![B_2478]: (v1_xboole_0(B_2478))), inference(splitRight, [status(thm)], [c_78480])).
% 24.48/14.32  tff(c_78064, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_12, c_78055])).
% 24.48/14.32  tff(c_131984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131916, c_78064])).
% 24.48/14.32  tff(c_131985, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitRight, [status(thm)], [c_77801])).
% 24.48/14.32  tff(c_132050, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')='#skF_1'), inference(resolution, [status(thm)], [c_131985, c_38])).
% 24.48/14.32  tff(c_132061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76859, c_132050])).
% 24.48/14.32  tff(c_132063, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_76857])).
% 24.48/14.32  tff(c_132102, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_8', '#skF_9')=k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_132063, c_60766, c_76858, c_30])).
% 24.48/14.32  tff(c_132424, plain, (![A_3769, B_3770, C_3771, D_3772]: (k2_zfmisc_1(k3_zfmisc_1(A_3769, B_3770, C_3771), D_3772)=k4_zfmisc_1(A_3769, B_3770, C_3771, D_3772))), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.48/14.32  tff(c_133609, plain, (![A_3857, B_3858, C_3859, D_3860]: (v1_xboole_0(k4_zfmisc_1(A_3857, B_3858, C_3859, D_3860)) | ~v1_xboole_0(k3_zfmisc_1(A_3857, B_3858, C_3859)))), inference(superposition, [status(thm), theory('equality')], [c_132424, c_14])).
% 24.48/14.32  tff(c_133641, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_132102, c_133609])).
% 24.48/14.32  tff(c_133752, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(splitLeft, [status(thm)], [c_133641])).
% 24.48/14.32  tff(c_133763, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_132347, c_133752])).
% 24.48/14.32  tff(c_132062, plain, ('#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_76857])).
% 24.48/14.32  tff(c_132450, plain, (![A_3769, B_3770, C_3771, D_3772]: (v1_xboole_0(k4_zfmisc_1(A_3769, B_3770, C_3771, D_3772)) | ~v1_xboole_0(D_3772))), inference(superposition, [status(thm), theory('equality')], [c_132424, c_12])).
% 24.48/14.32  tff(c_135648, plain, (![A_3950, B_3951, C_3952, D_3953]: (~v1_xboole_0(k4_zfmisc_1(A_3950, B_3951, C_3952, D_3953)) | v1_xboole_0(D_3953) | v1_xboole_0(k3_zfmisc_1(A_3950, B_3951, C_3952)))), inference(superposition, [status(thm), theory('equality')], [c_132424, c_20])).
% 24.48/14.32  tff(c_135690, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | v1_xboole_0('#skF_9') | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_132102, c_135648])).
% 24.48/14.32  tff(c_135714, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | v1_xboole_0('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_133752, c_135690])).
% 24.48/14.32  tff(c_135715, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitLeft, [status(thm)], [c_135714])).
% 24.48/14.32  tff(c_135727, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_132450, c_135715])).
% 24.48/14.32  tff(c_132523, plain, (![B_3782, A_3783, D_3784, C_3785]: (~r1_tarski(k2_zfmisc_1(B_3782, A_3783), k2_zfmisc_1(D_3784, C_3785)) | r1_tarski(B_3782, D_3784) | v1_xboole_0(A_3783))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.32  tff(c_137988, plain, (![A_4065, A_4062, B_4063, C_4060, D_4064, B_4061]: (~r1_tarski(k2_zfmisc_1(B_4061, A_4062), k4_zfmisc_1(A_4065, B_4063, C_4060, D_4064)) | r1_tarski(B_4061, k3_zfmisc_1(A_4065, B_4063, C_4060)) | v1_xboole_0(A_4062))), inference(superposition, [status(thm), theory('equality')], [c_24, c_132523])).
% 24.48/14.32  tff(c_138103, plain, (![B_4066, A_4067]: (~r1_tarski(k2_zfmisc_1(B_4066, A_4067), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(B_4066, k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')) | v1_xboole_0(A_4067))), inference(superposition, [status(thm), theory('equality')], [c_132102, c_137988])).
% 24.48/14.32  tff(c_139171, plain, (![A_4101, B_4102, C_4103, D_4104]: (~r1_tarski(k4_zfmisc_1(A_4101, B_4102, C_4103, D_4104), k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')) | r1_tarski(k3_zfmisc_1(A_4101, B_4102, C_4103), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')) | v1_xboole_0(D_4104))), inference(superposition, [status(thm), theory('equality')], [c_24, c_138103])).
% 24.48/14.32  tff(c_139221, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_10, c_139171])).
% 24.48/14.32  tff(c_139253, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_135727, c_139221])).
% 24.48/14.32  tff(c_132631, plain, (![A_3795, B_3796, C_3797, D_3798]: (~r1_tarski(k2_zfmisc_1(A_3795, B_3796), k2_zfmisc_1(C_3797, D_3798)) | r1_tarski(B_3796, D_3798) | v1_xboole_0(A_3795))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.48/14.32  tff(c_136332, plain, (![C_3981, C_3978, B_3980, D_3982, A_3979]: (~r1_tarski(k3_zfmisc_1(A_3979, B_3980, C_3978), k2_zfmisc_1(C_3981, D_3982)) | r1_tarski(C_3978, D_3982) | v1_xboole_0(k2_zfmisc_1(A_3979, B_3980)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_132631])).
% 24.48/14.32  tff(c_143895, plain, (![B_4217, C_4220, B_4219, C_4215, A_4216, A_4218]: (~r1_tarski(k3_zfmisc_1(A_4218, B_4219, C_4220), k3_zfmisc_1(A_4216, B_4217, C_4215)) | r1_tarski(C_4220, C_4215) | v1_xboole_0(k2_zfmisc_1(A_4218, B_4219)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_136332])).
% 24.48/14.32  tff(c_143930, plain, (r1_tarski('#skF_4', '#skF_8') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_139253, c_143895])).
% 24.48/14.32  tff(c_144020, plain, (r1_tarski('#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_133763, c_143930])).
% 24.48/14.32  tff(c_144049, plain, ('#skF_8'='#skF_4' | ~r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_144020, c_6])).
% 24.48/14.32  tff(c_144054, plain, (~r1_tarski('#skF_8', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_132062, c_144049])).
% 24.48/14.32  tff(c_162821, plain, (![C_4607, D_4608, A_4613, B_4609, B_4610, A_4612, C_4606, D_4611]: (~r1_tarski(k4_zfmisc_1(A_4612, B_4610, C_4606, D_4611), k4_zfmisc_1(A_4613, B_4609, C_4607, D_4608)) | r1_tarski(k3_zfmisc_1(A_4612, B_4610, C_4606), k3_zfmisc_1(A_4613, B_4609, C_4607)) | v1_xboole_0(D_4611))), inference(superposition, [status(thm), theory('equality')], [c_24, c_137988])).
% 24.48/14.32  tff(c_162965, plain, (![A_4613, B_4609, C_4607, D_4608]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_4613, B_4609, C_4607, D_4608)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), k3_zfmisc_1(A_4613, B_4609, C_4607)) | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_132102, c_162821])).
% 24.48/14.32  tff(c_163284, plain, (![A_4620, B_4621, C_4622, D_4623]: (~r1_tarski(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'), k4_zfmisc_1(A_4620, B_4621, C_4622, D_4623)) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), k3_zfmisc_1(A_4620, B_4621, C_4622)))), inference(negUnitSimplification, [status(thm)], [c_135727, c_162965])).
% 24.48/14.32  tff(c_163376, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_8'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_163284])).
% 24.48/14.32  tff(c_136392, plain, (![C_3978, B_3980, C_19, B_18, A_17, A_3979]: (~r1_tarski(k3_zfmisc_1(A_3979, B_3980, C_3978), k3_zfmisc_1(A_17, B_18, C_19)) | r1_tarski(C_3978, C_19) | v1_xboole_0(k2_zfmisc_1(A_3979, B_3980)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_136332])).
% 24.48/14.32  tff(c_163382, plain, (r1_tarski('#skF_8', '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_163376, c_136392])).
% 24.48/14.32  tff(c_163394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133763, c_144054, c_163382])).
% 24.48/14.32  tff(c_163395, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_135714])).
% 24.48/14.32  tff(c_163427, plain, ('#skF_1'='#skF_9'), inference(resolution, [status(thm)], [c_163395, c_38])).
% 24.48/14.32  tff(c_163465, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_163427, c_76859])).
% 24.48/14.32  tff(c_163396, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitRight, [status(thm)], [c_135714])).
% 24.48/14.32  tff(c_163468, plain, (![A_1]: (A_1='#skF_9' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_163427, c_38])).
% 24.48/14.32  tff(c_163886, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_163396, c_163468])).
% 24.48/14.32  tff(c_163893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163465, c_163886])).
% 24.48/14.32  tff(c_163894, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9'))), inference(splitRight, [status(thm)], [c_133641])).
% 24.48/14.32  tff(c_163977, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_9')='#skF_1'), inference(resolution, [status(thm)], [c_163894, c_38])).
% 24.48/14.32  tff(c_163989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76859, c_163977])).
% 24.48/14.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.48/14.32  
% 24.48/14.32  Inference rules
% 24.48/14.32  ----------------------
% 24.48/14.32  #Ref     : 0
% 24.48/14.32  #Sup     : 41614
% 24.48/14.32  #Fact    : 0
% 24.48/14.32  #Define  : 0
% 24.48/14.32  #Split   : 144
% 24.48/14.32  #Chain   : 0
% 24.48/14.32  #Close   : 0
% 24.48/14.32  
% 24.48/14.32  Ordering : KBO
% 24.48/14.32  
% 24.48/14.32  Simplification rules
% 24.48/14.32  ----------------------
% 24.48/14.32  #Subsume      : 7118
% 24.48/14.32  #Demod        : 29660
% 24.48/14.32  #Tautology    : 23187
% 24.48/14.32  #SimpNegUnit  : 178
% 24.48/14.32  #BackRed      : 389
% 24.48/14.32  
% 24.48/14.32  #Partial instantiations: 0
% 24.48/14.32  #Strategies tried      : 1
% 24.48/14.32  
% 24.48/14.32  Timing (in seconds)
% 24.48/14.32  ----------------------
% 24.48/14.32  Preprocessing        : 0.30
% 24.48/14.32  Parsing              : 0.16
% 24.48/14.32  CNF conversion       : 0.02
% 24.48/14.32  Main loop            : 13.16
% 24.48/14.32  Inferencing          : 2.77
% 24.48/14.32  Reduction            : 3.96
% 24.48/14.32  Demodulation         : 2.92
% 24.48/14.32  BG Simplification    : 0.31
% 24.48/14.32  Subsumption          : 5.18
% 24.48/14.32  Abstraction          : 0.44
% 24.48/14.32  MUC search           : 0.00
% 24.48/14.32  Cooper               : 0.00
% 24.48/14.32  Total                : 13.57
% 24.48/14.32  Index Insertion      : 0.00
% 24.48/14.32  Index Deletion       : 0.00
% 24.48/14.32  Index Matching       : 0.00
% 24.48/14.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
