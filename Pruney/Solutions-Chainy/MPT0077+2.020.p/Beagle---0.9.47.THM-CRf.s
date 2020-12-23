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

% Result     : Theorem 8.54s
% Output     : CNFRefutation 8.54s
% Verified   : 
% Statistics : Number of formulae       :  249 (1078 expanded)
%              Number of leaves         :   22 ( 366 expanded)
%              Depth                    :   16
%              Number of atoms          :  259 (1392 expanded)
%              Number of equality atoms :  191 ( 911 expanded)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_116,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_120,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5396,plain,(
    ! [A_130,B_131] : k2_xboole_0(k3_xboole_0(A_130,B_131),k4_xboole_0(A_130,B_131)) = A_130 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5418,plain,(
    ! [A_132] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_132,k1_xboole_0)) = A_132 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5396])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5434,plain,(
    ! [A_133] : k2_xboole_0(k1_xboole_0,A_133) = A_133 ),
    inference(superposition,[status(thm),theory(equality)],[c_5418,c_10])).

tff(c_5414,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5396])).

tff(c_5513,plain,(
    ! [A_135] : k4_xboole_0(A_135,k1_xboole_0) = A_135 ),
    inference(superposition,[status(thm),theory(equality)],[c_5434,c_5414])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5525,plain,(
    ! [A_135] : k4_xboole_0(A_135,A_135) = k3_xboole_0(A_135,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5513,c_14])).

tff(c_5532,plain,(
    ! [A_135] : k4_xboole_0(A_135,A_135) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5525])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_29,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_121,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_121,c_4])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_107,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_111,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_130,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_130])).

tff(c_151,plain,(
    ! [A_28] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_28,k1_xboole_0)) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_130])).

tff(c_157,plain,(
    ! [A_28] : k2_xboole_0(k1_xboole_0,A_28) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_10])).

tff(c_460,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_157])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1207,plain,(
    ! [C_57] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_57)) = k4_xboole_0('#skF_4',C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_12])).

tff(c_1232,plain,(
    ! [C_57] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',C_57)) = k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_14])).

tff(c_1265,plain,(
    ! [C_57] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_57)) = k3_xboole_0('#skF_4',C_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1232])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_26])).

tff(c_327,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_424,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_327])).

tff(c_2564,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_424])).

tff(c_2567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_2564])).

tff(c_2568,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_2666,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2568,c_4])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2674,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2666,c_16])).

tff(c_3728,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2674,c_157])).

tff(c_167,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_10])).

tff(c_193,plain,(
    ! [B_7] : k4_xboole_0(B_7,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_167])).

tff(c_248,plain,(
    ! [B_31] : k4_xboole_0(B_31,k1_xboole_0) = B_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_193])).

tff(c_260,plain,(
    ! [B_31] : k4_xboole_0(B_31,B_31) = k3_xboole_0(B_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_14])).

tff(c_2570,plain,(
    ! [B_80] : k4_xboole_0(B_80,B_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_260])).

tff(c_2598,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(B_9,k4_xboole_0(A_8,B_9))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2570])).

tff(c_2813,plain,(
    ! [A_85,B_86] : k4_xboole_0(A_85,k2_xboole_0(B_86,A_85)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2598])).

tff(c_2855,plain,(
    ! [A_13,B_14] : k4_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2813])).

tff(c_271,plain,(
    ! [A_32,B_33,C_34] : k4_xboole_0(k4_xboole_0(A_32,B_33),C_34) = k4_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4987,plain,(
    ! [A_125,B_126,C_127] : k4_xboole_0(k4_xboole_0(A_125,B_126),k4_xboole_0(A_125,k2_xboole_0(B_126,C_127))) = k3_xboole_0(k4_xboole_0(A_125,B_126),C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_14])).

tff(c_5080,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3728,c_4987])).

tff(c_5202,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2855,c_5080])).

tff(c_5367,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5202,c_16])).

tff(c_5375,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3728,c_157,c_12,c_5367])).

tff(c_5377,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_5202])).

tff(c_5380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_5377])).

tff(c_5381,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_5391,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5381,c_4])).

tff(c_5405,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5391,c_5396])).

tff(c_5424,plain,(
    ! [A_132] : k2_xboole_0(k1_xboole_0,A_132) = A_132 ),
    inference(superposition,[status(thm),theory(equality)],[c_5418,c_10])).

tff(c_5772,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5405,c_5424])).

tff(c_5625,plain,(
    ! [A_139] : k4_xboole_0(A_139,A_139) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5525])).

tff(c_5634,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(B_9,k4_xboole_0(A_8,B_9))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5625,c_12])).

tff(c_5801,plain,(
    ! [A_144,B_145] : k4_xboole_0(A_144,k2_xboole_0(B_145,A_144)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5634])).

tff(c_5816,plain,(
    ! [B_145,A_144] : k2_xboole_0(k2_xboole_0(B_145,A_144),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_145,A_144),A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_5801,c_10])).

tff(c_7848,plain,(
    ! [B_183,A_184] : k2_xboole_0(k2_xboole_0(B_183,A_184),A_184) = k2_xboole_0(B_183,A_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5424,c_2,c_5816])).

tff(c_5784,plain,(
    ! [C_10] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_10)) = k4_xboole_0('#skF_1',C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_5772,c_12])).

tff(c_7871,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7848,c_5784])).

tff(c_7957,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5772,c_7871])).

tff(c_8004,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7957,c_14])).

tff(c_8013,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5532,c_8004])).

tff(c_8015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_8013])).

tff(c_8016,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_8026,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8016])).

tff(c_8030,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_8026])).

tff(c_14320,plain,(
    ! [A_305,B_306] : k2_xboole_0(k3_xboole_0(A_305,B_306),k4_xboole_0(A_305,B_306)) = A_305 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14341,plain,(
    ! [A_307] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_307,k1_xboole_0)) = A_307 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_14320])).

tff(c_14357,plain,(
    ! [A_308] : k2_xboole_0(k1_xboole_0,A_308) = A_308 ),
    inference(superposition,[status(thm),theory(equality)],[c_14341,c_10])).

tff(c_14338,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_14320])).

tff(c_14439,plain,(
    ! [A_310] : k4_xboole_0(A_310,k1_xboole_0) = A_310 ),
    inference(superposition,[status(thm),theory(equality)],[c_14357,c_14338])).

tff(c_14451,plain,(
    ! [A_310] : k4_xboole_0(A_310,A_310) = k3_xboole_0(A_310,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14439,c_14])).

tff(c_14525,plain,(
    ! [A_314] : k4_xboole_0(A_314,A_314) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14451])).

tff(c_14534,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(B_9,k4_xboole_0(A_8,B_9))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14525,c_12])).

tff(c_14735,plain,(
    ! [A_319,B_320] : k4_xboole_0(A_319,k2_xboole_0(B_320,A_319)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14534])).

tff(c_14777,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14735])).

tff(c_8033,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_8037,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8033,c_4])).

tff(c_8042,plain,(
    ! [A_185,B_186] : k2_xboole_0(k3_xboole_0(A_185,B_186),k4_xboole_0(A_185,B_186)) = A_185 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8057,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_8042])).

tff(c_8071,plain,(
    ! [A_187] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_187,k1_xboole_0)) = A_187 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_8042])).

tff(c_8077,plain,(
    ! [A_187] : k2_xboole_0(k1_xboole_0,A_187) = A_187 ),
    inference(superposition,[status(thm),theory(equality)],[c_8071,c_10])).

tff(c_8344,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8057,c_8077])).

tff(c_8191,plain,(
    ! [A_191,B_192,C_193] : k4_xboole_0(k4_xboole_0(A_191,B_192),C_193) = k4_xboole_0(A_191,k2_xboole_0(B_192,C_193)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11047,plain,(
    ! [A_246,B_247,C_248] : k4_xboole_0(k4_xboole_0(A_246,B_247),k4_xboole_0(A_246,k2_xboole_0(B_247,C_248))) = k3_xboole_0(k4_xboole_0(A_246,B_247),C_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_8191,c_14])).

tff(c_11197,plain,(
    ! [C_248] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_248))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_8344,c_11047])).

tff(c_11286,plain,(
    ! [C_248] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_248)) = k3_xboole_0('#skF_4',C_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8344,c_14,c_11197])).

tff(c_8066,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_8070,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_8066])).

tff(c_11432,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11286,c_8070])).

tff(c_11435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8037,c_11432])).

tff(c_11436,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_11441,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11436,c_4])).

tff(c_11626,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11441,c_16])).

tff(c_11446,plain,(
    ! [A_251] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_251,k1_xboole_0)) = A_251 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_8042])).

tff(c_11452,plain,(
    ! [A_251] : k2_xboole_0(k1_xboole_0,A_251) = A_251 ),
    inference(superposition,[status(thm),theory(equality)],[c_11446,c_10])).

tff(c_12049,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11626,c_11452])).

tff(c_11505,plain,(
    ! [A_255] : k2_xboole_0(k1_xboole_0,A_255) = A_255 ),
    inference(superposition,[status(thm),theory(equality)],[c_11446,c_10])).

tff(c_8063,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_8042])).

tff(c_11547,plain,(
    ! [A_256] : k4_xboole_0(A_256,k1_xboole_0) = A_256 ),
    inference(superposition,[status(thm),theory(equality)],[c_11505,c_8063])).

tff(c_11566,plain,(
    ! [A_256] : k4_xboole_0(A_256,A_256) = k3_xboole_0(A_256,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11547,c_14])).

tff(c_11632,plain,(
    ! [A_258] : k4_xboole_0(A_258,A_258) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11566])).

tff(c_11664,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(B_9,k4_xboole_0(A_8,B_9))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_11632])).

tff(c_11892,plain,(
    ! [A_263,B_264] : k4_xboole_0(A_263,k2_xboole_0(B_264,A_263)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11664])).

tff(c_11928,plain,(
    ! [A_13,B_14] : k4_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_11892])).

tff(c_11462,plain,(
    ! [A_252,B_253,C_254] : k4_xboole_0(k4_xboole_0(A_252,B_253),C_254) = k4_xboole_0(A_252,k2_xboole_0(B_253,C_254)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13875,plain,(
    ! [A_300,B_301,C_302] : k4_xboole_0(k4_xboole_0(A_300,B_301),k4_xboole_0(A_300,k2_xboole_0(B_301,C_302))) = k3_xboole_0(k4_xboole_0(A_300,B_301),C_302) ),
    inference(superposition,[status(thm),theory(equality)],[c_11462,c_14])).

tff(c_13994,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12049,c_13875])).

tff(c_14095,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11928,c_13994])).

tff(c_11535,plain,(
    ! [B_2] : k2_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11505])).

tff(c_11672,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(B_9,A_8)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11664])).

tff(c_12547,plain,(
    ! [C_277,A_278,B_279] : k2_xboole_0(C_277,k4_xboole_0(A_278,k2_xboole_0(B_279,C_277))) = k2_xboole_0(C_277,k4_xboole_0(A_278,B_279)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11462,c_10])).

tff(c_12599,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k2_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11672,c_12547])).

tff(c_12643,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11535,c_12599])).

tff(c_94,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_94])).

tff(c_106,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_103])).

tff(c_12928,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12643,c_106])).

tff(c_14240,plain,(
    k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2'),k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14095,c_12928])).

tff(c_14258,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12049,c_11452,c_2,c_12,c_14240])).

tff(c_11578,plain,(
    ! [A_256] : k4_xboole_0(A_256,A_256) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11566])).

tff(c_11651,plain,(
    ! [A_258] : k2_xboole_0(A_258,k1_xboole_0) = k2_xboole_0(A_258,A_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_11632,c_10])).

tff(c_11668,plain,(
    ! [A_258] : k2_xboole_0(A_258,A_258) = A_258 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11535,c_11651])).

tff(c_14022,plain,(
    ! [A_300,A_258] : k4_xboole_0(k4_xboole_0(A_300,A_258),k4_xboole_0(A_300,A_258)) = k3_xboole_0(k4_xboole_0(A_300,A_258),A_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_11668,c_13875])).

tff(c_14104,plain,(
    ! [A_300,A_258] : k3_xboole_0(k4_xboole_0(A_300,A_258),A_258) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11578,c_14022])).

tff(c_14270,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14258,c_14104])).

tff(c_14304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8030,c_14270])).

tff(c_14305,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_14319,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14305,c_4])).

tff(c_14521,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14319,c_16])).

tff(c_14347,plain,(
    ! [A_307] : k2_xboole_0(k1_xboole_0,A_307) = A_307 ),
    inference(superposition,[status(thm),theory(equality)],[c_14341,c_10])).

tff(c_14897,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14521,c_14347])).

tff(c_14462,plain,(
    ! [A_311,B_312,C_313] : k4_xboole_0(k4_xboole_0(A_311,B_312),C_313) = k4_xboole_0(A_311,k2_xboole_0(B_312,C_313)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15463,plain,(
    ! [C_337,A_338,B_339] : k2_xboole_0(C_337,k4_xboole_0(A_338,k2_xboole_0(B_339,C_337))) = k2_xboole_0(C_337,k4_xboole_0(A_338,B_339)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14462,c_10])).

tff(c_15511,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14897,c_15463])).

tff(c_15561,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_15511])).

tff(c_8017,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_8021,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8017,c_4])).

tff(c_14329,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8021,c_14320])).

tff(c_14705,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14329,c_14347])).

tff(c_14717,plain,(
    ! [C_10] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_10)) = k4_xboole_0('#skF_1',C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14705,c_12])).

tff(c_16646,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15561,c_14717])).

tff(c_16664,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14777,c_14,c_16646])).

tff(c_16666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8030,c_16664])).

tff(c_16667,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_8016])).

tff(c_16672,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16667,c_4])).

tff(c_16688,plain,(
    ! [A_357,B_358] : k2_xboole_0(k3_xboole_0(A_357,B_358),k4_xboole_0(A_357,B_358)) = A_357 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16706,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_16688])).

tff(c_16720,plain,(
    ! [A_359] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_359,k1_xboole_0)) = A_359 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_16688])).

tff(c_16726,plain,(
    ! [A_359] : k2_xboole_0(k1_xboole_0,A_359) = A_359 ),
    inference(superposition,[status(thm),theory(equality)],[c_16720,c_10])).

tff(c_16993,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16706,c_16726])).

tff(c_16840,plain,(
    ! [A_363,B_364,C_365] : k4_xboole_0(k4_xboole_0(A_363,B_364),C_365) = k4_xboole_0(A_363,k2_xboole_0(B_364,C_365)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_19088,plain,(
    ! [A_409,B_410,C_411] : k4_xboole_0(k4_xboole_0(A_409,B_410),k4_xboole_0(A_409,k2_xboole_0(B_410,C_411))) = k3_xboole_0(k4_xboole_0(A_409,B_410),C_411) ),
    inference(superposition,[status(thm),theory(equality)],[c_16840,c_14])).

tff(c_19226,plain,(
    ! [C_411] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_411))) = k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),C_411) ),
    inference(superposition,[status(thm),theory(equality)],[c_16993,c_19088])).

tff(c_19313,plain,(
    ! [C_411] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_411)) = k3_xboole_0('#skF_4',C_411) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16993,c_14,c_19226])).

tff(c_16715,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_16719,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_16715])).

tff(c_23088,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19313,c_16719])).

tff(c_23091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16672,c_23088])).

tff(c_23093,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_16668,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_8016])).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_23276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23093,c_8017,c_16668,c_30])).

tff(c_23278,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23366,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_23278,c_20])).

tff(c_23367,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_23366])).

tff(c_23371,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_23367])).

tff(c_23291,plain,(
    ! [A_465,B_466] : k2_xboole_0(k3_xboole_0(A_465,B_466),k4_xboole_0(A_465,B_466)) = A_465 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_23310,plain,(
    ! [A_467] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_467,k1_xboole_0)) = A_467 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_23291])).

tff(c_23316,plain,(
    ! [A_467] : k2_xboole_0(k1_xboole_0,A_467) = A_467 ),
    inference(superposition,[status(thm),theory(equality)],[c_23310,c_10])).

tff(c_23326,plain,(
    ! [A_468] : k2_xboole_0(k1_xboole_0,A_468) = A_468 ),
    inference(superposition,[status(thm),theory(equality)],[c_23310,c_10])).

tff(c_23352,plain,(
    ! [B_7] : k4_xboole_0(B_7,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_23326])).

tff(c_23374,plain,(
    ! [B_469] : k4_xboole_0(B_469,k1_xboole_0) = B_469 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23316,c_23352])).

tff(c_23386,plain,(
    ! [B_469] : k4_xboole_0(B_469,B_469) = k3_xboole_0(B_469,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_23374,c_14])).

tff(c_23393,plain,(
    ! [B_469] : k4_xboole_0(B_469,B_469) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_23386])).

tff(c_23277,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_23286,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23277,c_4])).

tff(c_23300,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_23286,c_23291])).

tff(c_24018,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_23300,c_23316])).

tff(c_23519,plain,(
    ! [A_474,B_475,C_476] : k4_xboole_0(k4_xboole_0(A_474,B_475),C_476) = k4_xboole_0(A_474,k2_xboole_0(B_475,C_476)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_23529,plain,(
    ! [A_474,B_475] : k4_xboole_0(A_474,k2_xboole_0(B_475,k4_xboole_0(A_474,B_475))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_23519,c_23393])).

tff(c_23586,plain,(
    ! [A_477,B_478] : k4_xboole_0(A_477,k2_xboole_0(B_478,A_477)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_23529])).

tff(c_23601,plain,(
    ! [B_478,A_477] : k2_xboole_0(k2_xboole_0(B_478,A_477),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_478,A_477),A_477) ),
    inference(superposition,[status(thm),theory(equality)],[c_23586,c_10])).

tff(c_23633,plain,(
    ! [B_478,A_477] : k2_xboole_0(k2_xboole_0(B_478,A_477),A_477) = k2_xboole_0(B_478,A_477) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23316,c_2,c_23601])).

tff(c_25463,plain,(
    ! [C_518] : k4_xboole_0('#skF_1',k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),C_518)) = k4_xboole_0('#skF_1',C_518) ),
    inference(superposition,[status(thm),theory(equality)],[c_24018,c_12])).

tff(c_25514,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23633,c_25463])).

tff(c_25558,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24018,c_25514])).

tff(c_25598,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25558,c_14])).

tff(c_25610,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23393,c_25598])).

tff(c_25612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23371,c_25610])).

tff(c_25613,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_23366])).

tff(c_25618,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_25613])).

tff(c_23306,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_23291])).

tff(c_25672,plain,(
    ! [A_520] : k4_xboole_0(A_520,k1_xboole_0) = A_520 ),
    inference(superposition,[status(thm),theory(equality)],[c_23306,c_23326])).

tff(c_25684,plain,(
    ! [A_520] : k4_xboole_0(A_520,A_520) = k3_xboole_0(A_520,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_25672,c_14])).

tff(c_25752,plain,(
    ! [A_524] : k4_xboole_0(A_524,A_524) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_25684])).

tff(c_25761,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(B_9,k4_xboole_0(A_8,B_9))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_25752,c_12])).

tff(c_25879,plain,(
    ! [A_527,B_528] : k4_xboole_0(A_527,k2_xboole_0(B_528,A_527)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_25761])).

tff(c_25924,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_25879])).

tff(c_26086,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_23300,c_23316])).

tff(c_25699,plain,(
    ! [A_521,B_522,C_523] : k4_xboole_0(k4_xboole_0(A_521,B_522),C_523) = k4_xboole_0(A_521,k2_xboole_0(B_522,C_523)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26807,plain,(
    ! [C_550,A_551,B_552] : k2_xboole_0(C_550,k4_xboole_0(A_551,k2_xboole_0(B_552,C_550))) = k2_xboole_0(C_550,k4_xboole_0(A_551,B_552)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25699,c_10])).

tff(c_26873,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26086,c_26807])).

tff(c_26928,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26873])).

tff(c_25614,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_23366])).

tff(c_25622,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25614,c_4])).

tff(c_25626,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_25622,c_16])).

tff(c_25850,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_25626,c_23316])).

tff(c_25862,plain,(
    ! [C_10] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_10)) = k4_xboole_0('#skF_1',C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_25850,c_12])).

tff(c_27242,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26928,c_25862])).

tff(c_27257,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25924,c_14,c_27242])).

tff(c_27259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25618,c_27257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.54/3.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/3.36  
% 8.54/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/3.37  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.54/3.37  
% 8.54/3.37  %Foreground sorts:
% 8.54/3.37  
% 8.54/3.37  
% 8.54/3.37  %Background operators:
% 8.54/3.37  
% 8.54/3.37  
% 8.54/3.37  %Foreground operators:
% 8.54/3.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.54/3.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.54/3.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.54/3.37  tff('#skF_5', type, '#skF_5': $i).
% 8.54/3.37  tff('#skF_6', type, '#skF_6': $i).
% 8.54/3.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.54/3.37  tff('#skF_2', type, '#skF_2': $i).
% 8.54/3.37  tff('#skF_3', type, '#skF_3': $i).
% 8.54/3.37  tff('#skF_1', type, '#skF_1': $i).
% 8.54/3.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.54/3.37  tff('#skF_4', type, '#skF_4': $i).
% 8.54/3.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.54/3.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.54/3.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.54/3.37  
% 8.54/3.40  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.54/3.40  tff(f_58, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.54/3.40  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.54/3.40  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.54/3.40  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.54/3.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.54/3.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.54/3.40  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.54/3.40  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.54/3.40  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.54/3.40  tff(c_116, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 8.54/3.40  tff(c_120, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_116])).
% 8.54/3.40  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.54/3.40  tff(c_5396, plain, (![A_130, B_131]: (k2_xboole_0(k3_xboole_0(A_130, B_131), k4_xboole_0(A_130, B_131))=A_130)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.54/3.40  tff(c_5418, plain, (![A_132]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_132, k1_xboole_0))=A_132)), inference(superposition, [status(thm), theory('equality')], [c_8, c_5396])).
% 8.54/3.40  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.54/3.40  tff(c_5434, plain, (![A_133]: (k2_xboole_0(k1_xboole_0, A_133)=A_133)), inference(superposition, [status(thm), theory('equality')], [c_5418, c_10])).
% 8.54/3.40  tff(c_5414, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_5396])).
% 8.54/3.40  tff(c_5513, plain, (![A_135]: (k4_xboole_0(A_135, k1_xboole_0)=A_135)), inference(superposition, [status(thm), theory('equality')], [c_5434, c_5414])).
% 8.54/3.40  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.54/3.40  tff(c_5525, plain, (![A_135]: (k4_xboole_0(A_135, A_135)=k3_xboole_0(A_135, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5513, c_14])).
% 8.54/3.40  tff(c_5532, plain, (![A_135]: (k4_xboole_0(A_135, A_135)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5525])).
% 8.54/3.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.54/3.40  tff(c_22, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.54/3.40  tff(c_29, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 8.54/3.40  tff(c_121, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_29])).
% 8.54/3.40  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.54/3.40  tff(c_125, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_121, c_4])).
% 8.54/3.40  tff(c_18, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.54/3.40  tff(c_32, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 8.54/3.40  tff(c_107, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 8.54/3.40  tff(c_111, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_107, c_4])).
% 8.54/3.40  tff(c_130, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.54/3.40  tff(c_142, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_111, c_130])).
% 8.54/3.40  tff(c_151, plain, (![A_28]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_28, k1_xboole_0))=A_28)), inference(superposition, [status(thm), theory('equality')], [c_8, c_130])).
% 8.54/3.40  tff(c_157, plain, (![A_28]: (k2_xboole_0(k1_xboole_0, A_28)=A_28)), inference(superposition, [status(thm), theory('equality')], [c_151, c_10])).
% 8.54/3.40  tff(c_460, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_142, c_157])).
% 8.54/3.40  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.54/3.40  tff(c_1207, plain, (![C_57]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_57))=k4_xboole_0('#skF_4', C_57))), inference(superposition, [status(thm), theory('equality')], [c_460, c_12])).
% 8.54/3.40  tff(c_1232, plain, (![C_57]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', C_57))=k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_57)))), inference(superposition, [status(thm), theory('equality')], [c_1207, c_14])).
% 8.54/3.40  tff(c_1265, plain, (![C_57]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_57))=k3_xboole_0('#skF_4', C_57))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1232])).
% 8.54/3.40  tff(c_26, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.54/3.40  tff(c_31, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_26])).
% 8.54/3.40  tff(c_327, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_31])).
% 8.54/3.40  tff(c_424, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_327])).
% 8.54/3.40  tff(c_2564, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_424])).
% 8.54/3.40  tff(c_2567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_2564])).
% 8.54/3.40  tff(c_2568, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 8.54/3.40  tff(c_2666, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2568, c_4])).
% 8.54/3.40  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.54/3.40  tff(c_2674, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2666, c_16])).
% 8.54/3.40  tff(c_3728, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2674, c_157])).
% 8.54/3.40  tff(c_167, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_151, c_10])).
% 8.54/3.40  tff(c_193, plain, (![B_7]: (k4_xboole_0(B_7, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_167])).
% 8.54/3.40  tff(c_248, plain, (![B_31]: (k4_xboole_0(B_31, k1_xboole_0)=B_31)), inference(demodulation, [status(thm), theory('equality')], [c_157, c_193])).
% 8.54/3.40  tff(c_260, plain, (![B_31]: (k4_xboole_0(B_31, B_31)=k3_xboole_0(B_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_248, c_14])).
% 8.54/3.40  tff(c_2570, plain, (![B_80]: (k4_xboole_0(B_80, B_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_260])).
% 8.54/3.40  tff(c_2598, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(B_9, k4_xboole_0(A_8, B_9)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2570])).
% 8.54/3.40  tff(c_2813, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k2_xboole_0(B_86, A_85))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2598])).
% 8.54/3.40  tff(c_2855, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_2813])).
% 8.54/3.40  tff(c_271, plain, (![A_32, B_33, C_34]: (k4_xboole_0(k4_xboole_0(A_32, B_33), C_34)=k4_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.54/3.40  tff(c_4987, plain, (![A_125, B_126, C_127]: (k4_xboole_0(k4_xboole_0(A_125, B_126), k4_xboole_0(A_125, k2_xboole_0(B_126, C_127)))=k3_xboole_0(k4_xboole_0(A_125, B_126), C_127))), inference(superposition, [status(thm), theory('equality')], [c_271, c_14])).
% 8.54/3.40  tff(c_5080, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3728, c_4987])).
% 8.54/3.40  tff(c_5202, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2855, c_5080])).
% 8.54/3.40  tff(c_5367, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5202, c_16])).
% 8.54/3.40  tff(c_5375, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3728, c_157, c_12, c_5367])).
% 8.54/3.40  tff(c_5377, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_5202])).
% 8.54/3.40  tff(c_5380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_5377])).
% 8.54/3.40  tff(c_5381, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_29])).
% 8.54/3.40  tff(c_5391, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_5381, c_4])).
% 8.54/3.40  tff(c_5405, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5391, c_5396])).
% 8.54/3.40  tff(c_5424, plain, (![A_132]: (k2_xboole_0(k1_xboole_0, A_132)=A_132)), inference(superposition, [status(thm), theory('equality')], [c_5418, c_10])).
% 8.54/3.40  tff(c_5772, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5405, c_5424])).
% 8.54/3.40  tff(c_5625, plain, (![A_139]: (k4_xboole_0(A_139, A_139)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5525])).
% 8.54/3.40  tff(c_5634, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(B_9, k4_xboole_0(A_8, B_9)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5625, c_12])).
% 8.54/3.40  tff(c_5801, plain, (![A_144, B_145]: (k4_xboole_0(A_144, k2_xboole_0(B_145, A_144))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_5634])).
% 8.54/3.40  tff(c_5816, plain, (![B_145, A_144]: (k2_xboole_0(k2_xboole_0(B_145, A_144), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_145, A_144), A_144))), inference(superposition, [status(thm), theory('equality')], [c_5801, c_10])).
% 8.54/3.40  tff(c_7848, plain, (![B_183, A_184]: (k2_xboole_0(k2_xboole_0(B_183, A_184), A_184)=k2_xboole_0(B_183, A_184))), inference(demodulation, [status(thm), theory('equality')], [c_5424, c_2, c_5816])).
% 8.54/3.40  tff(c_5784, plain, (![C_10]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_10))=k4_xboole_0('#skF_1', C_10))), inference(superposition, [status(thm), theory('equality')], [c_5772, c_12])).
% 8.54/3.40  tff(c_7871, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7848, c_5784])).
% 8.54/3.40  tff(c_7957, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5772, c_7871])).
% 8.54/3.40  tff(c_8004, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7957, c_14])).
% 8.54/3.40  tff(c_8013, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5532, c_8004])).
% 8.54/3.40  tff(c_8015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_8013])).
% 8.54/3.40  tff(c_8016, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 8.54/3.40  tff(c_8026, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_8016])).
% 8.54/3.40  tff(c_8030, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_8026])).
% 8.54/3.40  tff(c_14320, plain, (![A_305, B_306]: (k2_xboole_0(k3_xboole_0(A_305, B_306), k4_xboole_0(A_305, B_306))=A_305)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.54/3.40  tff(c_14341, plain, (![A_307]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_307, k1_xboole_0))=A_307)), inference(superposition, [status(thm), theory('equality')], [c_8, c_14320])).
% 8.54/3.40  tff(c_14357, plain, (![A_308]: (k2_xboole_0(k1_xboole_0, A_308)=A_308)), inference(superposition, [status(thm), theory('equality')], [c_14341, c_10])).
% 8.54/3.40  tff(c_14338, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_14320])).
% 8.54/3.40  tff(c_14439, plain, (![A_310]: (k4_xboole_0(A_310, k1_xboole_0)=A_310)), inference(superposition, [status(thm), theory('equality')], [c_14357, c_14338])).
% 8.54/3.40  tff(c_14451, plain, (![A_310]: (k4_xboole_0(A_310, A_310)=k3_xboole_0(A_310, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14439, c_14])).
% 8.54/3.40  tff(c_14525, plain, (![A_314]: (k4_xboole_0(A_314, A_314)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14451])).
% 8.54/3.40  tff(c_14534, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(B_9, k4_xboole_0(A_8, B_9)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14525, c_12])).
% 8.54/3.40  tff(c_14735, plain, (![A_319, B_320]: (k4_xboole_0(A_319, k2_xboole_0(B_320, A_319))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14534])).
% 8.54/3.40  tff(c_14777, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_14735])).
% 8.54/3.40  tff(c_8033, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_29])).
% 8.54/3.40  tff(c_8037, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8033, c_4])).
% 8.54/3.40  tff(c_8042, plain, (![A_185, B_186]: (k2_xboole_0(k3_xboole_0(A_185, B_186), k4_xboole_0(A_185, B_186))=A_185)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.54/3.40  tff(c_8057, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_111, c_8042])).
% 8.54/3.40  tff(c_8071, plain, (![A_187]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_187, k1_xboole_0))=A_187)), inference(superposition, [status(thm), theory('equality')], [c_8, c_8042])).
% 8.54/3.40  tff(c_8077, plain, (![A_187]: (k2_xboole_0(k1_xboole_0, A_187)=A_187)), inference(superposition, [status(thm), theory('equality')], [c_8071, c_10])).
% 8.54/3.40  tff(c_8344, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8057, c_8077])).
% 8.54/3.40  tff(c_8191, plain, (![A_191, B_192, C_193]: (k4_xboole_0(k4_xboole_0(A_191, B_192), C_193)=k4_xboole_0(A_191, k2_xboole_0(B_192, C_193)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.54/3.40  tff(c_11047, plain, (![A_246, B_247, C_248]: (k4_xboole_0(k4_xboole_0(A_246, B_247), k4_xboole_0(A_246, k2_xboole_0(B_247, C_248)))=k3_xboole_0(k4_xboole_0(A_246, B_247), C_248))), inference(superposition, [status(thm), theory('equality')], [c_8191, c_14])).
% 8.54/3.40  tff(c_11197, plain, (![C_248]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_248)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_248))), inference(superposition, [status(thm), theory('equality')], [c_8344, c_11047])).
% 8.54/3.40  tff(c_11286, plain, (![C_248]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_248))=k3_xboole_0('#skF_4', C_248))), inference(demodulation, [status(thm), theory('equality')], [c_8344, c_14, c_11197])).
% 8.54/3.40  tff(c_8066, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_31])).
% 8.54/3.40  tff(c_8070, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_8066])).
% 8.54/3.40  tff(c_11432, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11286, c_8070])).
% 8.54/3.40  tff(c_11435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8037, c_11432])).
% 8.54/3.40  tff(c_11436, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_31])).
% 8.54/3.40  tff(c_11441, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_11436, c_4])).
% 8.54/3.40  tff(c_11626, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11441, c_16])).
% 8.54/3.40  tff(c_11446, plain, (![A_251]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_251, k1_xboole_0))=A_251)), inference(superposition, [status(thm), theory('equality')], [c_8, c_8042])).
% 8.54/3.40  tff(c_11452, plain, (![A_251]: (k2_xboole_0(k1_xboole_0, A_251)=A_251)), inference(superposition, [status(thm), theory('equality')], [c_11446, c_10])).
% 8.54/3.40  tff(c_12049, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11626, c_11452])).
% 8.54/3.40  tff(c_11505, plain, (![A_255]: (k2_xboole_0(k1_xboole_0, A_255)=A_255)), inference(superposition, [status(thm), theory('equality')], [c_11446, c_10])).
% 8.54/3.40  tff(c_8063, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_8042])).
% 8.54/3.40  tff(c_11547, plain, (![A_256]: (k4_xboole_0(A_256, k1_xboole_0)=A_256)), inference(superposition, [status(thm), theory('equality')], [c_11505, c_8063])).
% 8.54/3.40  tff(c_11566, plain, (![A_256]: (k4_xboole_0(A_256, A_256)=k3_xboole_0(A_256, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11547, c_14])).
% 8.54/3.40  tff(c_11632, plain, (![A_258]: (k4_xboole_0(A_258, A_258)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11566])).
% 8.54/3.40  tff(c_11664, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(B_9, k4_xboole_0(A_8, B_9)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_11632])).
% 8.54/3.40  tff(c_11892, plain, (![A_263, B_264]: (k4_xboole_0(A_263, k2_xboole_0(B_264, A_263))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_11664])).
% 8.54/3.40  tff(c_11928, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_11892])).
% 8.54/3.40  tff(c_11462, plain, (![A_252, B_253, C_254]: (k4_xboole_0(k4_xboole_0(A_252, B_253), C_254)=k4_xboole_0(A_252, k2_xboole_0(B_253, C_254)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.54/3.40  tff(c_13875, plain, (![A_300, B_301, C_302]: (k4_xboole_0(k4_xboole_0(A_300, B_301), k4_xboole_0(A_300, k2_xboole_0(B_301, C_302)))=k3_xboole_0(k4_xboole_0(A_300, B_301), C_302))), inference(superposition, [status(thm), theory('equality')], [c_11462, c_14])).
% 8.54/3.40  tff(c_13994, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12049, c_13875])).
% 8.54/3.40  tff(c_14095, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11928, c_13994])).
% 8.54/3.40  tff(c_11535, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_11505])).
% 8.54/3.40  tff(c_11672, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(B_9, A_8))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_11664])).
% 8.54/3.40  tff(c_12547, plain, (![C_277, A_278, B_279]: (k2_xboole_0(C_277, k4_xboole_0(A_278, k2_xboole_0(B_279, C_277)))=k2_xboole_0(C_277, k4_xboole_0(A_278, B_279)))), inference(superposition, [status(thm), theory('equality')], [c_11462, c_10])).
% 8.54/3.40  tff(c_12599, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k2_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11672, c_12547])).
% 8.54/3.40  tff(c_12643, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(A_8, B_9))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_11535, c_12599])).
% 8.54/3.40  tff(c_94, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.54/3.40  tff(c_103, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k2_xboole_0(k4_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_94])).
% 8.54/3.40  tff(c_106, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k2_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_103])).
% 8.54/3.40  tff(c_12928, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_12643, c_106])).
% 8.54/3.40  tff(c_14240, plain, (k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'), k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14095, c_12928])).
% 8.54/3.40  tff(c_14258, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12049, c_11452, c_2, c_12, c_14240])).
% 8.54/3.40  tff(c_11578, plain, (![A_256]: (k4_xboole_0(A_256, A_256)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11566])).
% 8.54/3.40  tff(c_11651, plain, (![A_258]: (k2_xboole_0(A_258, k1_xboole_0)=k2_xboole_0(A_258, A_258))), inference(superposition, [status(thm), theory('equality')], [c_11632, c_10])).
% 8.54/3.40  tff(c_11668, plain, (![A_258]: (k2_xboole_0(A_258, A_258)=A_258)), inference(demodulation, [status(thm), theory('equality')], [c_11535, c_11651])).
% 8.54/3.40  tff(c_14022, plain, (![A_300, A_258]: (k4_xboole_0(k4_xboole_0(A_300, A_258), k4_xboole_0(A_300, A_258))=k3_xboole_0(k4_xboole_0(A_300, A_258), A_258))), inference(superposition, [status(thm), theory('equality')], [c_11668, c_13875])).
% 8.54/3.40  tff(c_14104, plain, (![A_300, A_258]: (k3_xboole_0(k4_xboole_0(A_300, A_258), A_258)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11578, c_14022])).
% 8.54/3.40  tff(c_14270, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14258, c_14104])).
% 8.54/3.40  tff(c_14304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8030, c_14270])).
% 8.54/3.40  tff(c_14305, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_29])).
% 8.54/3.40  tff(c_14319, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14305, c_4])).
% 8.54/3.40  tff(c_14521, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14319, c_16])).
% 8.54/3.40  tff(c_14347, plain, (![A_307]: (k2_xboole_0(k1_xboole_0, A_307)=A_307)), inference(superposition, [status(thm), theory('equality')], [c_14341, c_10])).
% 8.54/3.40  tff(c_14897, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14521, c_14347])).
% 8.54/3.40  tff(c_14462, plain, (![A_311, B_312, C_313]: (k4_xboole_0(k4_xboole_0(A_311, B_312), C_313)=k4_xboole_0(A_311, k2_xboole_0(B_312, C_313)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.54/3.40  tff(c_15463, plain, (![C_337, A_338, B_339]: (k2_xboole_0(C_337, k4_xboole_0(A_338, k2_xboole_0(B_339, C_337)))=k2_xboole_0(C_337, k4_xboole_0(A_338, B_339)))), inference(superposition, [status(thm), theory('equality')], [c_14462, c_10])).
% 8.54/3.40  tff(c_15511, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14897, c_15463])).
% 8.54/3.40  tff(c_15561, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_15511])).
% 8.54/3.40  tff(c_8017, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 8.54/3.40  tff(c_8021, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_8017, c_4])).
% 8.54/3.40  tff(c_14329, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8021, c_14320])).
% 8.54/3.40  tff(c_14705, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14329, c_14347])).
% 8.54/3.40  tff(c_14717, plain, (![C_10]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_10))=k4_xboole_0('#skF_1', C_10))), inference(superposition, [status(thm), theory('equality')], [c_14705, c_12])).
% 8.54/3.40  tff(c_16646, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15561, c_14717])).
% 8.54/3.40  tff(c_16664, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14777, c_14, c_16646])).
% 8.54/3.40  tff(c_16666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8030, c_16664])).
% 8.54/3.40  tff(c_16667, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_8016])).
% 8.54/3.40  tff(c_16672, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_16667, c_4])).
% 8.54/3.40  tff(c_16688, plain, (![A_357, B_358]: (k2_xboole_0(k3_xboole_0(A_357, B_358), k4_xboole_0(A_357, B_358))=A_357)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.54/3.40  tff(c_16706, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_111, c_16688])).
% 8.54/3.40  tff(c_16720, plain, (![A_359]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_359, k1_xboole_0))=A_359)), inference(superposition, [status(thm), theory('equality')], [c_8, c_16688])).
% 8.54/3.40  tff(c_16726, plain, (![A_359]: (k2_xboole_0(k1_xboole_0, A_359)=A_359)), inference(superposition, [status(thm), theory('equality')], [c_16720, c_10])).
% 8.54/3.40  tff(c_16993, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16706, c_16726])).
% 8.54/3.40  tff(c_16840, plain, (![A_363, B_364, C_365]: (k4_xboole_0(k4_xboole_0(A_363, B_364), C_365)=k4_xboole_0(A_363, k2_xboole_0(B_364, C_365)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.54/3.40  tff(c_19088, plain, (![A_409, B_410, C_411]: (k4_xboole_0(k4_xboole_0(A_409, B_410), k4_xboole_0(A_409, k2_xboole_0(B_410, C_411)))=k3_xboole_0(k4_xboole_0(A_409, B_410), C_411))), inference(superposition, [status(thm), theory('equality')], [c_16840, c_14])).
% 8.54/3.40  tff(c_19226, plain, (![C_411]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_411)))=k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), C_411))), inference(superposition, [status(thm), theory('equality')], [c_16993, c_19088])).
% 8.54/3.40  tff(c_19313, plain, (![C_411]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_411))=k3_xboole_0('#skF_4', C_411))), inference(demodulation, [status(thm), theory('equality')], [c_16993, c_14, c_19226])).
% 8.54/3.40  tff(c_16715, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_31])).
% 8.54/3.40  tff(c_16719, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_16715])).
% 8.54/3.40  tff(c_23088, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_19313, c_16719])).
% 8.54/3.40  tff(c_23091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16672, c_23088])).
% 8.54/3.40  tff(c_23093, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_31])).
% 8.54/3.40  tff(c_16668, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_8016])).
% 8.54/3.40  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.54/3.40  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 8.54/3.40  tff(c_23276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23093, c_8017, c_16668, c_30])).
% 8.54/3.40  tff(c_23278, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 8.54/3.40  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.54/3.40  tff(c_23366, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_23278, c_20])).
% 8.54/3.40  tff(c_23367, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_23366])).
% 8.54/3.40  tff(c_23371, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_23367])).
% 8.54/3.40  tff(c_23291, plain, (![A_465, B_466]: (k2_xboole_0(k3_xboole_0(A_465, B_466), k4_xboole_0(A_465, B_466))=A_465)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.54/3.40  tff(c_23310, plain, (![A_467]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_467, k1_xboole_0))=A_467)), inference(superposition, [status(thm), theory('equality')], [c_8, c_23291])).
% 8.54/3.40  tff(c_23316, plain, (![A_467]: (k2_xboole_0(k1_xboole_0, A_467)=A_467)), inference(superposition, [status(thm), theory('equality')], [c_23310, c_10])).
% 8.54/3.40  tff(c_23326, plain, (![A_468]: (k2_xboole_0(k1_xboole_0, A_468)=A_468)), inference(superposition, [status(thm), theory('equality')], [c_23310, c_10])).
% 8.54/3.40  tff(c_23352, plain, (![B_7]: (k4_xboole_0(B_7, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_23326])).
% 8.54/3.40  tff(c_23374, plain, (![B_469]: (k4_xboole_0(B_469, k1_xboole_0)=B_469)), inference(demodulation, [status(thm), theory('equality')], [c_23316, c_23352])).
% 8.54/3.40  tff(c_23386, plain, (![B_469]: (k4_xboole_0(B_469, B_469)=k3_xboole_0(B_469, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_23374, c_14])).
% 8.54/3.40  tff(c_23393, plain, (![B_469]: (k4_xboole_0(B_469, B_469)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_23386])).
% 8.54/3.40  tff(c_23277, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 8.54/3.40  tff(c_23286, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_23277, c_4])).
% 8.54/3.40  tff(c_23300, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_23286, c_23291])).
% 8.54/3.40  tff(c_24018, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_23300, c_23316])).
% 8.54/3.40  tff(c_23519, plain, (![A_474, B_475, C_476]: (k4_xboole_0(k4_xboole_0(A_474, B_475), C_476)=k4_xboole_0(A_474, k2_xboole_0(B_475, C_476)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.54/3.40  tff(c_23529, plain, (![A_474, B_475]: (k4_xboole_0(A_474, k2_xboole_0(B_475, k4_xboole_0(A_474, B_475)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23519, c_23393])).
% 8.54/3.40  tff(c_23586, plain, (![A_477, B_478]: (k4_xboole_0(A_477, k2_xboole_0(B_478, A_477))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_23529])).
% 8.54/3.40  tff(c_23601, plain, (![B_478, A_477]: (k2_xboole_0(k2_xboole_0(B_478, A_477), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_478, A_477), A_477))), inference(superposition, [status(thm), theory('equality')], [c_23586, c_10])).
% 8.54/3.40  tff(c_23633, plain, (![B_478, A_477]: (k2_xboole_0(k2_xboole_0(B_478, A_477), A_477)=k2_xboole_0(B_478, A_477))), inference(demodulation, [status(thm), theory('equality')], [c_23316, c_2, c_23601])).
% 8.54/3.40  tff(c_25463, plain, (![C_518]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), C_518))=k4_xboole_0('#skF_1', C_518))), inference(superposition, [status(thm), theory('equality')], [c_24018, c_12])).
% 8.54/3.40  tff(c_25514, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_23633, c_25463])).
% 8.54/3.40  tff(c_25558, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24018, c_25514])).
% 8.54/3.40  tff(c_25598, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25558, c_14])).
% 8.54/3.40  tff(c_25610, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_23393, c_25598])).
% 8.54/3.40  tff(c_25612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23371, c_25610])).
% 8.54/3.40  tff(c_25613, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_23366])).
% 8.54/3.40  tff(c_25618, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_25613])).
% 8.54/3.40  tff(c_23306, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_23291])).
% 8.54/3.40  tff(c_25672, plain, (![A_520]: (k4_xboole_0(A_520, k1_xboole_0)=A_520)), inference(superposition, [status(thm), theory('equality')], [c_23306, c_23326])).
% 8.54/3.40  tff(c_25684, plain, (![A_520]: (k4_xboole_0(A_520, A_520)=k3_xboole_0(A_520, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_25672, c_14])).
% 8.54/3.40  tff(c_25752, plain, (![A_524]: (k4_xboole_0(A_524, A_524)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_25684])).
% 8.54/3.40  tff(c_25761, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(B_9, k4_xboole_0(A_8, B_9)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_25752, c_12])).
% 8.54/3.40  tff(c_25879, plain, (![A_527, B_528]: (k4_xboole_0(A_527, k2_xboole_0(B_528, A_527))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_25761])).
% 8.54/3.40  tff(c_25924, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_25879])).
% 8.54/3.40  tff(c_26086, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_23300, c_23316])).
% 8.54/3.40  tff(c_25699, plain, (![A_521, B_522, C_523]: (k4_xboole_0(k4_xboole_0(A_521, B_522), C_523)=k4_xboole_0(A_521, k2_xboole_0(B_522, C_523)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.54/3.40  tff(c_26807, plain, (![C_550, A_551, B_552]: (k2_xboole_0(C_550, k4_xboole_0(A_551, k2_xboole_0(B_552, C_550)))=k2_xboole_0(C_550, k4_xboole_0(A_551, B_552)))), inference(superposition, [status(thm), theory('equality')], [c_25699, c_10])).
% 8.54/3.40  tff(c_26873, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26086, c_26807])).
% 8.54/3.40  tff(c_26928, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26873])).
% 8.54/3.40  tff(c_25614, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_23366])).
% 8.54/3.40  tff(c_25622, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_25614, c_4])).
% 8.54/3.40  tff(c_25626, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_25622, c_16])).
% 8.54/3.40  tff(c_25850, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_25626, c_23316])).
% 8.54/3.40  tff(c_25862, plain, (![C_10]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_10))=k4_xboole_0('#skF_1', C_10))), inference(superposition, [status(thm), theory('equality')], [c_25850, c_12])).
% 8.54/3.40  tff(c_27242, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26928, c_25862])).
% 8.54/3.40  tff(c_27257, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_25924, c_14, c_27242])).
% 8.54/3.40  tff(c_27259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25618, c_27257])).
% 8.54/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/3.40  
% 8.54/3.40  Inference rules
% 8.54/3.40  ----------------------
% 8.54/3.40  #Ref     : 0
% 8.54/3.40  #Sup     : 6771
% 8.54/3.40  #Fact    : 0
% 8.54/3.40  #Define  : 0
% 8.54/3.40  #Split   : 10
% 8.54/3.40  #Chain   : 0
% 8.54/3.40  #Close   : 0
% 8.54/3.40  
% 8.54/3.40  Ordering : KBO
% 8.54/3.40  
% 8.54/3.40  Simplification rules
% 8.54/3.40  ----------------------
% 8.54/3.40  #Subsume      : 14
% 8.54/3.40  #Demod        : 6934
% 8.54/3.40  #Tautology    : 4591
% 8.54/3.40  #SimpNegUnit  : 7
% 8.54/3.40  #BackRed      : 43
% 8.54/3.40  
% 8.54/3.40  #Partial instantiations: 0
% 8.54/3.40  #Strategies tried      : 1
% 8.54/3.40  
% 8.54/3.40  Timing (in seconds)
% 8.54/3.40  ----------------------
% 8.90/3.40  Preprocessing        : 0.27
% 8.90/3.40  Parsing              : 0.15
% 8.90/3.40  CNF conversion       : 0.02
% 8.90/3.40  Main loop            : 2.30
% 8.90/3.40  Inferencing          : 0.63
% 8.90/3.40  Reduction            : 1.17
% 8.90/3.40  Demodulation         : 1.00
% 8.90/3.40  BG Simplification    : 0.08
% 8.90/3.40  Subsumption          : 0.29
% 8.90/3.40  Abstraction          : 0.11
% 8.90/3.40  MUC search           : 0.00
% 8.90/3.40  Cooper               : 0.00
% 8.90/3.40  Total                : 2.65
% 8.90/3.40  Index Insertion      : 0.00
% 8.90/3.40  Index Deletion       : 0.00
% 8.90/3.40  Index Matching       : 0.00
% 8.90/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
