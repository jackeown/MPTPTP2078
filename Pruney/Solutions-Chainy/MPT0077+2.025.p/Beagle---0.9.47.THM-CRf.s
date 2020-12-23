%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:38 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 427 expanded)
%              Number of leaves         :   23 ( 145 expanded)
%              Depth                    :   12
%              Number of atoms          :  157 ( 638 expanded)
%              Number of equality atoms :  103 ( 316 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_130,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_129,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_134,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_147,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_147])).

tff(c_166,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_162])).

tff(c_381,plain,(
    ! [A_41,B_42,C_43] : k4_xboole_0(k4_xboole_0(A_41,B_42),C_43) = k4_xboole_0(A_41,k2_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1223,plain,(
    ! [C_60] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_60)) = k4_xboole_0('#skF_4',C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_381])).

tff(c_1239,plain,(
    ! [C_60] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_60)) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1223,c_18])).

tff(c_1270,plain,(
    ! [C_60] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_5',C_60)) = k3_xboole_0('#skF_4',C_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1239])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_376,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_380,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_376])).

tff(c_3186,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_380])).

tff(c_3189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_3186])).

tff(c_3191,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3201,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3191,c_30])).

tff(c_3202,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3201])).

tff(c_3206,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_3202])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_49])).

tff(c_3190,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3195,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3190,c_2])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3213,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3195,c_16])).

tff(c_3217,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3213])).

tff(c_82,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_82])).

tff(c_104,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_94])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [A_11,B_12] : k2_xboole_0(k2_xboole_0(A_11,B_12),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_4191,plain,(
    ! [A_11,B_12] : k2_xboole_0(k2_xboole_0(A_11,B_12),A_11) = k2_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_97])).

tff(c_3247,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k4_xboole_0(A_95,B_96),C_97) = k4_xboole_0(A_95,k2_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3328,plain,(
    ! [A_7,C_97] : k4_xboole_0(A_7,k2_xboole_0(k1_xboole_0,C_97)) = k4_xboole_0(A_7,C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3247])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3307,plain,(
    ! [A_13,B_14,C_97] : k4_xboole_0(A_13,k2_xboole_0(k3_xboole_0(A_13,B_14),C_97)) = k4_xboole_0(k4_xboole_0(A_13,B_14),C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3247])).

tff(c_8617,plain,(
    ! [A_173,B_174,C_175] : k4_xboole_0(A_173,k2_xboole_0(k3_xboole_0(A_173,B_174),C_175)) = k4_xboole_0(A_173,k2_xboole_0(B_174,C_175)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3307])).

tff(c_8781,plain,(
    ! [C_175] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),C_175)) = k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,C_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3195,c_8617])).

tff(c_9899,plain,(
    ! [C_186] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),C_186)) = k4_xboole_0('#skF_1',C_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3328,c_8781])).

tff(c_9984,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4191,c_9899])).

tff(c_10029,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3217,c_9984])).

tff(c_10064,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10029,c_18])).

tff(c_10076,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10064])).

tff(c_10078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3206,c_10076])).

tff(c_10079,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3201])).

tff(c_10084,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_10079])).

tff(c_10080,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_3201])).

tff(c_10088,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10080,c_2])).

tff(c_10095,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10088,c_16])).

tff(c_10099,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10095])).

tff(c_11839,plain,(
    ! [C_224] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_224)) = k4_xboole_0('#skF_1',C_224) ),
    inference(superposition,[status(thm),theory(equality)],[c_10099,c_12])).

tff(c_10368,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3195,c_16])).

tff(c_10372,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10368])).

tff(c_11848,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11839,c_10372])).

tff(c_11914,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11848,c_18])).

tff(c_11922,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11914])).

tff(c_11924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10084,c_11922])).

tff(c_11926,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_11967,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_11926,c_22])).

tff(c_11968,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_11967])).

tff(c_11972,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_11968])).

tff(c_11925,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_11942,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11925,c_2])).

tff(c_11947,plain,(
    ! [A_225,B_226] : k4_xboole_0(A_225,k3_xboole_0(A_225,B_226)) = k4_xboole_0(A_225,B_226) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11959,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11942,c_11947])).

tff(c_11965,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11959])).

tff(c_12710,plain,(
    ! [A_11,B_12] : k2_xboole_0(k2_xboole_0(A_11,B_12),A_11) = k2_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_97])).

tff(c_12181,plain,(
    ! [A_237,B_238,C_239] : k4_xboole_0(k4_xboole_0(A_237,B_238),C_239) = k4_xboole_0(A_237,k2_xboole_0(B_238,C_239)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12862,plain,(
    ! [C_253] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),C_253)) = k4_xboole_0('#skF_1',C_253) ),
    inference(superposition,[status(thm),theory(equality)],[c_11965,c_12181])).

tff(c_12892,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12710,c_12862])).

tff(c_12916,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11965,c_12892])).

tff(c_12930,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12916,c_18])).

tff(c_12937,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12930])).

tff(c_12939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11972,c_12937])).

tff(c_12940,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_11967])).

tff(c_12945,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_12940])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13137,plain,(
    ! [A_262,B_263,C_264] : k4_xboole_0(k4_xboole_0(A_262,B_263),C_264) = k4_xboole_0(A_262,k2_xboole_0(B_263,C_264)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13164,plain,(
    ! [A_262,B_263] : k4_xboole_0(A_262,k2_xboole_0(B_263,k4_xboole_0(A_262,B_263))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13137,c_56])).

tff(c_13357,plain,(
    ! [A_267,B_268] : k4_xboole_0(A_267,k2_xboole_0(B_268,A_267)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_13164])).

tff(c_13378,plain,(
    ! [B_268,A_267] : k2_xboole_0(k2_xboole_0(B_268,A_267),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_268,A_267),A_267) ),
    inference(superposition,[status(thm),theory(equality)],[c_13357,c_8])).

tff(c_13408,plain,(
    ! [B_268,A_267] : k2_xboole_0(k2_xboole_0(B_268,A_267),A_267) = k2_xboole_0(B_268,A_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_13378])).

tff(c_14208,plain,(
    ! [C_288] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),C_288)) = k4_xboole_0('#skF_1',C_288) ),
    inference(superposition,[status(thm),theory(equality)],[c_11965,c_13137])).

tff(c_14234,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13408,c_14208])).

tff(c_14265,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11965,c_14234])).

tff(c_14281,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14265,c_18])).

tff(c_14288,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14281])).

tff(c_14290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12945,c_14288])).

tff(c_14292,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_14370,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_14374,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_14370])).

tff(c_14291,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_14300,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14291,c_2])).

tff(c_14305,plain,(
    ! [A_289,B_290] : k4_xboole_0(A_289,k3_xboole_0(A_289,B_290)) = k4_xboole_0(A_289,B_290) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14317,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14300,c_14305])).

tff(c_14320,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14317])).

tff(c_17173,plain,(
    ! [A_351,B_352] : k2_xboole_0(k2_xboole_0(A_351,B_352),A_351) = k2_xboole_0(A_351,B_352) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_97])).

tff(c_14516,plain,(
    ! [A_301,B_302,C_303] : k4_xboole_0(k4_xboole_0(A_301,B_302),C_303) = k4_xboole_0(A_301,k2_xboole_0(B_302,C_303)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14567,plain,(
    ! [C_303] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_2','#skF_3'),C_303)) = k4_xboole_0('#skF_1',C_303) ),
    inference(superposition,[status(thm),theory(equality)],[c_14320,c_14516])).

tff(c_17240,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17173,c_14567])).

tff(c_17308,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14320,c_17240])).

tff(c_17345,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17308,c_18])).

tff(c_17355,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_17345])).

tff(c_17357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14374,c_17355])).

tff(c_17359,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_17376,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17359,c_26])).

tff(c_17377,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_14292,c_17376])).

tff(c_17381,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_17377])).

tff(c_17363,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17359,c_2])).

tff(c_17385,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17363,c_16])).

tff(c_17388,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_17385])).

tff(c_17425,plain,(
    ! [A_355,B_356,C_357] : k4_xboole_0(k4_xboole_0(A_355,B_356),C_357) = k4_xboole_0(A_355,k2_xboole_0(B_356,C_357)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_17877,plain,(
    ! [C_370] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_370)) = k4_xboole_0('#skF_1',C_370) ),
    inference(superposition,[status(thm),theory(equality)],[c_17388,c_17425])).

tff(c_17896,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_17877,c_14320])).

tff(c_17941,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17896,c_18])).

tff(c_17948,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_17941])).

tff(c_17950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17381,c_17948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.57  
% 7.11/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.57  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.11/2.57  
% 7.11/2.57  %Foreground sorts:
% 7.11/2.57  
% 7.11/2.57  
% 7.11/2.57  %Background operators:
% 7.11/2.57  
% 7.11/2.57  
% 7.11/2.57  %Foreground operators:
% 7.11/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.11/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.57  tff('#skF_5', type, '#skF_5': $i).
% 7.11/2.57  tff('#skF_6', type, '#skF_6': $i).
% 7.11/2.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.11/2.57  tff('#skF_2', type, '#skF_2': $i).
% 7.11/2.57  tff('#skF_3', type, '#skF_3': $i).
% 7.11/2.57  tff('#skF_1', type, '#skF_1': $i).
% 7.11/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.57  tff('#skF_4', type, '#skF_4': $i).
% 7.11/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.11/2.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.11/2.57  
% 7.11/2.59  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.11/2.59  tff(f_60, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.11/2.59  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.11/2.59  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.11/2.59  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.11/2.59  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.11/2.59  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.11/2.59  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.11/2.59  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.11/2.59  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.11/2.59  tff(c_20, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.11/2.59  tff(c_130, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_20])).
% 7.11/2.59  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.11/2.59  tff(c_138, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_2])).
% 7.11/2.59  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.11/2.59  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.11/2.59  tff(c_24, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.11/2.59  tff(c_129, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_24])).
% 7.11/2.59  tff(c_134, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_2])).
% 7.11/2.59  tff(c_147, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.11/2.59  tff(c_162, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_134, c_147])).
% 7.11/2.59  tff(c_166, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_162])).
% 7.11/2.59  tff(c_381, plain, (![A_41, B_42, C_43]: (k4_xboole_0(k4_xboole_0(A_41, B_42), C_43)=k4_xboole_0(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.59  tff(c_1223, plain, (![C_60]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_60))=k4_xboole_0('#skF_4', C_60))), inference(superposition, [status(thm), theory('equality')], [c_166, c_381])).
% 7.11/2.59  tff(c_1239, plain, (![C_60]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_60))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_60)))), inference(superposition, [status(thm), theory('equality')], [c_1223, c_18])).
% 7.11/2.59  tff(c_1270, plain, (![C_60]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', C_60))=k3_xboole_0('#skF_4', C_60))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1239])).
% 7.11/2.59  tff(c_28, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.11/2.59  tff(c_376, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_28])).
% 7.11/2.59  tff(c_380, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_376])).
% 7.11/2.59  tff(c_3186, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_380])).
% 7.11/2.59  tff(c_3189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_3186])).
% 7.11/2.59  tff(c_3191, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_28])).
% 7.11/2.59  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.11/2.59  tff(c_3201, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3191, c_30])).
% 7.11/2.59  tff(c_3202, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_3201])).
% 7.11/2.59  tff(c_3206, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_3202])).
% 7.11/2.59  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.11/2.59  tff(c_49, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.11/2.59  tff(c_56, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_49])).
% 7.11/2.59  tff(c_3190, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 7.11/2.59  tff(c_3195, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3190, c_2])).
% 7.11/2.59  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.11/2.59  tff(c_3213, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3195, c_16])).
% 7.11/2.59  tff(c_3217, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3213])).
% 7.11/2.59  tff(c_82, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.11/2.59  tff(c_94, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_56, c_82])).
% 7.11/2.59  tff(c_104, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_94])).
% 7.11/2.59  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.11/2.59  tff(c_97, plain, (![A_11, B_12]: (k2_xboole_0(k2_xboole_0(A_11, B_12), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_82])).
% 7.11/2.59  tff(c_4191, plain, (![A_11, B_12]: (k2_xboole_0(k2_xboole_0(A_11, B_12), A_11)=k2_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_97])).
% 7.11/2.59  tff(c_3247, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k4_xboole_0(A_95, B_96), C_97)=k4_xboole_0(A_95, k2_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.59  tff(c_3328, plain, (![A_7, C_97]: (k4_xboole_0(A_7, k2_xboole_0(k1_xboole_0, C_97))=k4_xboole_0(A_7, C_97))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3247])).
% 7.11/2.59  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.59  tff(c_3307, plain, (![A_13, B_14, C_97]: (k4_xboole_0(A_13, k2_xboole_0(k3_xboole_0(A_13, B_14), C_97))=k4_xboole_0(k4_xboole_0(A_13, B_14), C_97))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3247])).
% 7.11/2.59  tff(c_8617, plain, (![A_173, B_174, C_175]: (k4_xboole_0(A_173, k2_xboole_0(k3_xboole_0(A_173, B_174), C_175))=k4_xboole_0(A_173, k2_xboole_0(B_174, C_175)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3307])).
% 7.11/2.59  tff(c_8781, plain, (![C_175]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), C_175))=k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, C_175)))), inference(superposition, [status(thm), theory('equality')], [c_3195, c_8617])).
% 7.11/2.59  tff(c_9899, plain, (![C_186]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), C_186))=k4_xboole_0('#skF_1', C_186))), inference(demodulation, [status(thm), theory('equality')], [c_3328, c_8781])).
% 7.11/2.59  tff(c_9984, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4191, c_9899])).
% 7.11/2.59  tff(c_10029, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3217, c_9984])).
% 7.11/2.59  tff(c_10064, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10029, c_18])).
% 7.11/2.59  tff(c_10076, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_10064])).
% 7.11/2.59  tff(c_10078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3206, c_10076])).
% 7.11/2.59  tff(c_10079, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_3201])).
% 7.11/2.59  tff(c_10084, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_10079])).
% 7.11/2.59  tff(c_10080, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_3201])).
% 7.11/2.59  tff(c_10088, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_10080, c_2])).
% 7.11/2.59  tff(c_10095, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10088, c_16])).
% 7.11/2.59  tff(c_10099, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10095])).
% 7.11/2.59  tff(c_11839, plain, (![C_224]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_224))=k4_xboole_0('#skF_1', C_224))), inference(superposition, [status(thm), theory('equality')], [c_10099, c_12])).
% 7.11/2.59  tff(c_10368, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3195, c_16])).
% 7.11/2.59  tff(c_10372, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10368])).
% 7.11/2.59  tff(c_11848, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11839, c_10372])).
% 7.11/2.59  tff(c_11914, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11848, c_18])).
% 7.11/2.59  tff(c_11922, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11914])).
% 7.11/2.59  tff(c_11924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10084, c_11922])).
% 7.11/2.59  tff(c_11926, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_20])).
% 7.11/2.59  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.11/2.59  tff(c_11967, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_11926, c_22])).
% 7.11/2.59  tff(c_11968, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_11967])).
% 7.11/2.59  tff(c_11972, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_11968])).
% 7.11/2.59  tff(c_11925, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_20])).
% 7.11/2.59  tff(c_11942, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_11925, c_2])).
% 7.11/2.59  tff(c_11947, plain, (![A_225, B_226]: (k4_xboole_0(A_225, k3_xboole_0(A_225, B_226))=k4_xboole_0(A_225, B_226))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.11/2.59  tff(c_11959, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11942, c_11947])).
% 7.11/2.59  tff(c_11965, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_11959])).
% 7.11/2.59  tff(c_12710, plain, (![A_11, B_12]: (k2_xboole_0(k2_xboole_0(A_11, B_12), A_11)=k2_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_97])).
% 7.11/2.59  tff(c_12181, plain, (![A_237, B_238, C_239]: (k4_xboole_0(k4_xboole_0(A_237, B_238), C_239)=k4_xboole_0(A_237, k2_xboole_0(B_238, C_239)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.59  tff(c_12862, plain, (![C_253]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), C_253))=k4_xboole_0('#skF_1', C_253))), inference(superposition, [status(thm), theory('equality')], [c_11965, c_12181])).
% 7.11/2.59  tff(c_12892, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12710, c_12862])).
% 7.11/2.59  tff(c_12916, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11965, c_12892])).
% 7.11/2.59  tff(c_12930, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12916, c_18])).
% 7.11/2.59  tff(c_12937, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12930])).
% 7.11/2.59  tff(c_12939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11972, c_12937])).
% 7.11/2.59  tff(c_12940, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_11967])).
% 7.11/2.59  tff(c_12945, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_12940])).
% 7.11/2.59  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.11/2.59  tff(c_13137, plain, (![A_262, B_263, C_264]: (k4_xboole_0(k4_xboole_0(A_262, B_263), C_264)=k4_xboole_0(A_262, k2_xboole_0(B_263, C_264)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.59  tff(c_13164, plain, (![A_262, B_263]: (k4_xboole_0(A_262, k2_xboole_0(B_263, k4_xboole_0(A_262, B_263)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13137, c_56])).
% 7.11/2.59  tff(c_13357, plain, (![A_267, B_268]: (k4_xboole_0(A_267, k2_xboole_0(B_268, A_267))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_13164])).
% 7.11/2.59  tff(c_13378, plain, (![B_268, A_267]: (k2_xboole_0(k2_xboole_0(B_268, A_267), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_268, A_267), A_267))), inference(superposition, [status(thm), theory('equality')], [c_13357, c_8])).
% 7.11/2.59  tff(c_13408, plain, (![B_268, A_267]: (k2_xboole_0(k2_xboole_0(B_268, A_267), A_267)=k2_xboole_0(B_268, A_267))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_13378])).
% 7.11/2.59  tff(c_14208, plain, (![C_288]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), C_288))=k4_xboole_0('#skF_1', C_288))), inference(superposition, [status(thm), theory('equality')], [c_11965, c_13137])).
% 7.11/2.59  tff(c_14234, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13408, c_14208])).
% 7.11/2.59  tff(c_14265, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11965, c_14234])).
% 7.11/2.59  tff(c_14281, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14265, c_18])).
% 7.11/2.59  tff(c_14288, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14281])).
% 7.11/2.59  tff(c_14290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12945, c_14288])).
% 7.11/2.59  tff(c_14292, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 7.11/2.59  tff(c_14370, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 7.11/2.59  tff(c_14374, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_14370])).
% 7.11/2.59  tff(c_14291, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_24])).
% 7.11/2.59  tff(c_14300, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14291, c_2])).
% 7.11/2.59  tff(c_14305, plain, (![A_289, B_290]: (k4_xboole_0(A_289, k3_xboole_0(A_289, B_290))=k4_xboole_0(A_289, B_290))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.11/2.59  tff(c_14317, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14300, c_14305])).
% 7.11/2.59  tff(c_14320, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14317])).
% 7.11/2.59  tff(c_17173, plain, (![A_351, B_352]: (k2_xboole_0(k2_xboole_0(A_351, B_352), A_351)=k2_xboole_0(A_351, B_352))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_97])).
% 7.11/2.59  tff(c_14516, plain, (![A_301, B_302, C_303]: (k4_xboole_0(k4_xboole_0(A_301, B_302), C_303)=k4_xboole_0(A_301, k2_xboole_0(B_302, C_303)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.59  tff(c_14567, plain, (![C_303]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), C_303))=k4_xboole_0('#skF_1', C_303))), inference(superposition, [status(thm), theory('equality')], [c_14320, c_14516])).
% 7.11/2.59  tff(c_17240, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17173, c_14567])).
% 7.11/2.59  tff(c_17308, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14320, c_17240])).
% 7.11/2.59  tff(c_17345, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17308, c_18])).
% 7.11/2.59  tff(c_17355, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_17345])).
% 7.11/2.59  tff(c_17357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14374, c_17355])).
% 7.11/2.59  tff(c_17359, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 7.11/2.59  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.11/2.59  tff(c_17376, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17359, c_26])).
% 7.11/2.59  tff(c_17377, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_14292, c_17376])).
% 7.11/2.59  tff(c_17381, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_17377])).
% 7.11/2.59  tff(c_17363, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_17359, c_2])).
% 7.11/2.59  tff(c_17385, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17363, c_16])).
% 7.11/2.59  tff(c_17388, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_17385])).
% 7.11/2.59  tff(c_17425, plain, (![A_355, B_356, C_357]: (k4_xboole_0(k4_xboole_0(A_355, B_356), C_357)=k4_xboole_0(A_355, k2_xboole_0(B_356, C_357)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.11/2.59  tff(c_17877, plain, (![C_370]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_370))=k4_xboole_0('#skF_1', C_370))), inference(superposition, [status(thm), theory('equality')], [c_17388, c_17425])).
% 7.11/2.59  tff(c_17896, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_17877, c_14320])).
% 7.11/2.59  tff(c_17941, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17896, c_18])).
% 7.11/2.59  tff(c_17948, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_17941])).
% 7.11/2.59  tff(c_17950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17381, c_17948])).
% 7.11/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.59  
% 7.11/2.59  Inference rules
% 7.11/2.59  ----------------------
% 7.11/2.59  #Ref     : 0
% 7.11/2.59  #Sup     : 4271
% 7.11/2.59  #Fact    : 0
% 7.11/2.59  #Define  : 0
% 7.11/2.59  #Split   : 6
% 7.11/2.59  #Chain   : 0
% 7.11/2.59  #Close   : 0
% 7.11/2.59  
% 7.11/2.59  Ordering : KBO
% 7.11/2.59  
% 7.11/2.59  Simplification rules
% 7.11/2.59  ----------------------
% 7.11/2.59  #Subsume      : 9
% 7.11/2.59  #Demod        : 4074
% 7.11/2.59  #Tautology    : 3232
% 7.11/2.59  #SimpNegUnit  : 9
% 7.11/2.59  #BackRed      : 1
% 7.11/2.59  
% 7.11/2.59  #Partial instantiations: 0
% 7.11/2.59  #Strategies tried      : 1
% 7.11/2.59  
% 7.11/2.59  Timing (in seconds)
% 7.11/2.59  ----------------------
% 7.11/2.59  Preprocessing        : 0.27
% 7.11/2.59  Parsing              : 0.16
% 7.11/2.59  CNF conversion       : 0.02
% 7.11/2.59  Main loop            : 1.53
% 7.11/2.59  Inferencing          : 0.49
% 7.11/2.59  Reduction            : 0.70
% 7.11/2.59  Demodulation         : 0.57
% 7.11/2.59  BG Simplification    : 0.05
% 7.11/2.59  Subsumption          : 0.21
% 7.11/2.59  Abstraction          : 0.08
% 7.11/2.59  MUC search           : 0.00
% 7.11/2.59  Cooper               : 0.00
% 7.11/2.59  Total                : 1.85
% 7.11/2.59  Index Insertion      : 0.00
% 7.11/2.59  Index Deletion       : 0.00
% 7.11/2.59  Index Matching       : 0.00
% 7.11/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
