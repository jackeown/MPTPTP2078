%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:36 EST 2020

% Result     : Theorem 8.88s
% Output     : CNFRefutation 8.88s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 823 expanded)
%              Number of leaves         :   28 ( 278 expanded)
%              Depth                    :   14
%              Number of atoms          :  255 (1118 expanded)
%              Number of equality atoms :  162 ( 651 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_185,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(A_31,B_32)
      | k3_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_183,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_189,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_185,c_183])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10778,plain,(
    ! [A_270,B_271] : k4_xboole_0(A_270,k4_xboole_0(A_270,B_271)) = k3_xboole_0(A_270,B_271) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10796,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_10778])).

tff(c_10799,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10796])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_394,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_41,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_353,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_357,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_353,c_4])).

tff(c_24,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_364,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_24])).

tff(c_87,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_14])).

tff(c_373,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_103])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_39,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_200,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_204,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_200,c_4])).

tff(c_209,plain,(
    ! [A_35,B_36] : k2_xboole_0(k3_xboole_0(A_35,B_36),k4_xboole_0(A_35,B_36)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_218,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_7')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_209])).

tff(c_233,plain,(
    k4_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_103])).

tff(c_400,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k4_xboole_0(A_49,B_50),C_51) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_450,plain,(
    ! [C_51] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_7',C_51)) = k4_xboole_0('#skF_5',C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_400])).

tff(c_26,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_301,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_307,plain,(
    ! [A_13,C_42] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_42,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_301])).

tff(c_311,plain,(
    ! [C_42] : ~ r2_hidden(C_42,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_307])).

tff(c_251,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_272,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_251])).

tff(c_276,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_272])).

tff(c_410,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(B_50,k4_xboole_0(A_49,B_50))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_276])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k4_xboole_0(A_15,B_16),C_17) = k4_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_417,plain,(
    ! [A_49,B_50,B_19] : k4_xboole_0(A_49,k2_xboole_0(B_50,k4_xboole_0(k4_xboole_0(A_49,B_50),B_19))) = k3_xboole_0(k4_xboole_0(A_49,B_50),B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_22])).

tff(c_3084,plain,(
    ! [A_111,B_112,B_113] : k4_xboole_0(A_111,k2_xboole_0(B_112,k4_xboole_0(A_111,k2_xboole_0(B_112,B_113)))) = k3_xboole_0(k4_xboole_0(A_111,B_112),B_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_417])).

tff(c_3282,plain,(
    ! [A_111,A_5] : k4_xboole_0(A_111,k2_xboole_0(A_5,k4_xboole_0(A_111,A_5))) = k3_xboole_0(k4_xboole_0(A_111,A_5),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3084])).

tff(c_3327,plain,(
    ! [A_114,A_115] : k3_xboole_0(k4_xboole_0(A_114,A_115),A_115) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_3282])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),k3_xboole_0(A_7,B_8))
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3350,plain,(
    ! [A_114,A_115] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_114,A_115),A_115),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(A_114,A_115),A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3327,c_10])).

tff(c_3460,plain,(
    ! [A_116,A_117] : r1_xboole_0(k4_xboole_0(A_116,A_117),A_117) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_3350])).

tff(c_3666,plain,(
    ! [C_119] : r1_xboole_0(k4_xboole_0('#skF_5',C_119),k2_xboole_0('#skF_7',C_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_3460])).

tff(c_3720,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_7','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_3666])).

tff(c_3759,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3720])).

tff(c_3761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_3759])).

tff(c_3762,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_3772,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3762,c_4])).

tff(c_3791,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3772,c_24])).

tff(c_3862,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3791,c_103])).

tff(c_3910,plain,(
    ! [A_124,B_125,C_126] : k4_xboole_0(k4_xboole_0(A_124,B_125),C_126) = k4_xboole_0(A_124,k2_xboole_0(B_125,C_126)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4248,plain,(
    ! [A_132,C_133] : k4_xboole_0(A_132,k2_xboole_0(A_132,C_133)) = k4_xboole_0(k1_xboole_0,C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_3910])).

tff(c_4306,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4248])).

tff(c_4314,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_4306])).

tff(c_3952,plain,(
    ! [A_14,C_126] : k4_xboole_0(A_14,k2_xboole_0(A_14,C_126)) = k4_xboole_0(k1_xboole_0,C_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_3910])).

tff(c_4489,plain,(
    ! [A_138,C_139] : k4_xboole_0(A_138,k2_xboole_0(A_138,C_139)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_3952])).

tff(c_4741,plain,(
    ! [B_144,A_145] : k4_xboole_0(B_144,k2_xboole_0(A_145,B_144)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4489])).

tff(c_4802,plain,(
    ! [A_20,B_21] : k4_xboole_0(k4_xboole_0(A_20,B_21),A_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4741])).

tff(c_5657,plain,(
    ! [A_162,B_163,C_164] : k4_xboole_0(k4_xboole_0(A_162,B_163),k4_xboole_0(A_162,k2_xboole_0(B_163,C_164))) = k3_xboole_0(k4_xboole_0(A_162,B_163),C_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_3910,c_22])).

tff(c_5794,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_2') = k3_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3862,c_5657])).

tff(c_5874,plain,(
    k3_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4802,c_5794])).

tff(c_6106,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3')) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5874,c_24])).

tff(c_6113,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_103,c_20,c_6106])).

tff(c_6200,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6113,c_5874])).

tff(c_6202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_6200])).

tff(c_6203,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_6212,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6203,c_4])).

tff(c_6219,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6212,c_24])).

tff(c_6585,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6219,c_103])).

tff(c_6225,plain,(
    ! [A_170,B_171,C_172] : k4_xboole_0(k4_xboole_0(A_170,B_171),C_172) = k4_xboole_0(A_170,k2_xboole_0(B_171,C_172)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6378,plain,(
    ! [A_175,C_176] : k4_xboole_0(A_175,k2_xboole_0(A_175,C_176)) = k4_xboole_0(k1_xboole_0,C_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_6225])).

tff(c_6436,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_6378])).

tff(c_6444,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_6436])).

tff(c_6258,plain,(
    ! [A_14,C_172] : k4_xboole_0(A_14,k2_xboole_0(A_14,C_172)) = k4_xboole_0(k1_xboole_0,C_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_6225])).

tff(c_6593,plain,(
    ! [A_182,C_183] : k4_xboole_0(A_182,k2_xboole_0(A_182,C_183)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6444,c_6258])).

tff(c_6888,plain,(
    ! [B_190,A_191] : k4_xboole_0(B_190,k2_xboole_0(A_191,B_190)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6593])).

tff(c_6933,plain,(
    ! [A_20,B_21] : k4_xboole_0(k4_xboole_0(A_20,B_21),A_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6888])).

tff(c_10060,plain,(
    ! [A_256,B_257,C_258] : k4_xboole_0(k4_xboole_0(A_256,B_257),k4_xboole_0(A_256,k2_xboole_0(B_257,C_258))) = k3_xboole_0(k4_xboole_0(A_256,B_257),C_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_6225,c_22])).

tff(c_10212,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_2') = k3_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6585,c_10060])).

tff(c_10319,plain,(
    k3_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6933,c_10212])).

tff(c_10617,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3')) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10319,c_24])).

tff(c_10627,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6585,c_103,c_20,c_10617])).

tff(c_10727,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10627,c_10319])).

tff(c_10729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_10727])).

tff(c_10730,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_10739,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10730,c_4])).

tff(c_10744,plain,(
    ! [A_264,B_265] : k2_xboole_0(k3_xboole_0(A_264,B_265),k4_xboole_0(A_264,B_265)) = A_264 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10753,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_10739,c_10744])).

tff(c_10888,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_10753,c_103])).

tff(c_10937,plain,(
    ! [A_282,B_283,C_284] : k4_xboole_0(k4_xboole_0(A_282,B_283),C_284) = k4_xboole_0(A_282,k2_xboole_0(B_283,C_284)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10940,plain,(
    ! [A_282,B_283,C_284,C_17] : k4_xboole_0(k4_xboole_0(A_282,k2_xboole_0(B_283,C_284)),C_17) = k4_xboole_0(k4_xboole_0(A_282,B_283),k2_xboole_0(C_284,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10937,c_20])).

tff(c_12975,plain,(
    ! [A_333,B_334,C_335,C_336] : k4_xboole_0(A_333,k2_xboole_0(k2_xboole_0(B_334,C_335),C_336)) = k4_xboole_0(A_333,k2_xboole_0(B_334,k2_xboole_0(C_335,C_336))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_10940])).

tff(c_10970,plain,(
    ! [C_284] : k4_xboole_0('#skF_2',k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),C_284)) = k4_xboole_0('#skF_2',C_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_10888,c_10937])).

tff(c_13292,plain,(
    ! [C_340] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_340))) = k4_xboole_0('#skF_2',C_340) ),
    inference(superposition,[status(thm),theory(equality)],[c_12975,c_10970])).

tff(c_13341,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_13292])).

tff(c_13351,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10888,c_13341])).

tff(c_13376,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13351,c_22])).

tff(c_13388,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10799,c_13376])).

tff(c_13390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_13388])).

tff(c_13392,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_13395,plain,(
    ! [A_341,B_342] :
      ( r1_xboole_0(A_341,B_342)
      | k3_xboole_0(A_341,B_342) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13391,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_13394,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_13391])).

tff(c_13399,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13395,c_13394])).

tff(c_22595,plain,(
    ! [A_555,B_556] : k4_xboole_0(A_555,k4_xboole_0(A_555,B_556)) = k3_xboole_0(A_555,B_556) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22616,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_22595])).

tff(c_22620,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22616])).

tff(c_13400,plain,(
    ! [A_343,B_344] :
      ( k3_xboole_0(A_343,B_344) = k1_xboole_0
      | ~ r1_xboole_0(A_343,B_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13411,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13392,c_13400])).

tff(c_22551,plain,(
    ! [A_553,B_554] : k2_xboole_0(k3_xboole_0(A_553,B_554),k4_xboole_0(A_553,B_554)) = A_553 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22563,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13411,c_22551])).

tff(c_22577,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22563,c_103])).

tff(c_22710,plain,(
    ! [A_563,B_564,C_565] : k4_xboole_0(k4_xboole_0(A_563,B_564),C_565) = k4_xboole_0(A_563,k2_xboole_0(B_564,C_565)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22858,plain,(
    ! [C_568] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_568)) = k4_xboole_0('#skF_2',C_568) ),
    inference(superposition,[status(thm),theory(equality)],[c_22577,c_22710])).

tff(c_23625,plain,(
    ! [B_590] : k4_xboole_0('#skF_2',k2_xboole_0(B_590,'#skF_3')) = k4_xboole_0('#skF_2',B_590) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22858])).

tff(c_21371,plain,(
    ! [A_516,B_517] : k4_xboole_0(A_516,k4_xboole_0(A_516,B_517)) = k3_xboole_0(A_516,B_517) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21395,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_21371])).

tff(c_21400,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_21395])).

tff(c_21302,plain,(
    ! [A_514,B_515] : k2_xboole_0(k3_xboole_0(A_514,B_515),k4_xboole_0(A_514,B_515)) = A_514 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_21317,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13411,c_21302])).

tff(c_21331,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_21317,c_103])).

tff(c_21523,plain,(
    ! [A_526,B_527,C_528] : k4_xboole_0(k4_xboole_0(A_526,B_527),C_528) = k4_xboole_0(A_526,k2_xboole_0(B_527,C_528)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_21695,plain,(
    ! [C_531] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_531)) = k4_xboole_0('#skF_2',C_531) ),
    inference(superposition,[status(thm),theory(equality)],[c_21331,c_21523])).

tff(c_22422,plain,(
    ! [A_548] : k4_xboole_0('#skF_2',k2_xboole_0(A_548,'#skF_3')) = k4_xboole_0('#skF_2',A_548) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_21695])).

tff(c_13518,plain,(
    ! [A_347,B_348] : k4_xboole_0(A_347,k4_xboole_0(A_347,B_348)) = k3_xboole_0(A_347,B_348) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13542,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_13518])).

tff(c_13547,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_13542])).

tff(c_13434,plain,(
    ! [A_345,B_346] : k2_xboole_0(k3_xboole_0(A_345,B_346),k4_xboole_0(A_345,B_346)) = A_345 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13446,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13411,c_13434])).

tff(c_13467,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13446,c_103])).

tff(c_19225,plain,(
    ! [A_468,B_469,C_470] : k4_xboole_0(k4_xboole_0(A_468,B_469),C_470) = k4_xboole_0(A_468,k2_xboole_0(B_469,C_470)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20891,plain,(
    ! [C_506] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_506)) = k4_xboole_0('#skF_2',C_506) ),
    inference(superposition,[status(thm),theory(equality)],[c_13467,c_19225])).

tff(c_21126,plain,(
    ! [B_509] : k4_xboole_0('#skF_2',k2_xboole_0(B_509,'#skF_3')) = k4_xboole_0('#skF_2',B_509) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20891])).

tff(c_13609,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_13420,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_13424,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13420,c_4])).

tff(c_13443,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_7')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_13424,c_13434])).

tff(c_13511,plain,(
    k4_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_13443,c_103])).

tff(c_13429,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_13433,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13429,c_4])).

tff(c_13460,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_13433,c_24])).

tff(c_13490,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_13460,c_103])).

tff(c_13703,plain,(
    ! [A_362,B_363,C_364] : k4_xboole_0(k4_xboole_0(A_362,B_363),C_364) = k4_xboole_0(A_362,k2_xboole_0(B_363,C_364)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13753,plain,(
    ! [C_364] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_364)) = k4_xboole_0('#skF_5',C_364) ),
    inference(superposition,[status(thm),theory(equality)],[c_13490,c_13703])).

tff(c_13617,plain,(
    ! [A_351,B_352,C_353] :
      ( ~ r1_xboole_0(A_351,B_352)
      | ~ r2_hidden(C_353,k3_xboole_0(A_351,B_352)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13632,plain,(
    ! [A_13,C_353] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_353,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_13617])).

tff(c_13640,plain,(
    ! [C_353] : ~ r2_hidden(C_353,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_13632])).

tff(c_15663,plain,(
    ! [A_404,B_405,C_406] : k4_xboole_0(k4_xboole_0(A_404,B_405),k4_xboole_0(A_404,k2_xboole_0(B_405,C_406))) = k3_xboole_0(k4_xboole_0(A_404,B_405),C_406) ),
    inference(superposition,[status(thm),theory(equality)],[c_13703,c_22])).

tff(c_15837,plain,(
    ! [A_404,A_5] : k4_xboole_0(k4_xboole_0(A_404,A_5),k4_xboole_0(A_404,A_5)) = k3_xboole_0(k4_xboole_0(A_404,A_5),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15663])).

tff(c_15888,plain,(
    ! [A_407,A_408] : k3_xboole_0(k4_xboole_0(A_407,A_408),A_408) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13547,c_15837])).

tff(c_15902,plain,(
    ! [A_407,A_408] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_407,A_408),A_408),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(A_407,A_408),A_408) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15888,c_10])).

tff(c_16005,plain,(
    ! [A_409,A_410] : r1_xboole_0(k4_xboole_0(A_409,A_410),A_410) ),
    inference(negUnitSimplification,[status(thm)],[c_13640,c_15902])).

tff(c_19062,plain,(
    ! [C_459] : r1_xboole_0(k4_xboole_0('#skF_5',C_459),k2_xboole_0('#skF_6',C_459)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13753,c_16005])).

tff(c_19110,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13511,c_19062])).

tff(c_19149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13609,c_19110])).

tff(c_19150,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_19155,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19150,c_4])).

tff(c_19166,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_19155,c_24])).

tff(c_19608,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_19166])).

tff(c_21153,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_21126,c_19608])).

tff(c_21250,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21153,c_22])).

tff(c_21261,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13547,c_21250])).

tff(c_21263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13399,c_21261])).

tff(c_21264,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_21273,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21264,c_4])).

tff(c_21311,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_21273,c_21302])).

tff(c_21484,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_21311,c_103])).

tff(c_22445,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22422,c_21484])).

tff(c_22506,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22445,c_22])).

tff(c_22514,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21400,c_22506])).

tff(c_22516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13399,c_22514])).

tff(c_22517,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_22526,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22517,c_4])).

tff(c_22560,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22526,c_22551])).

tff(c_22689,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22560,c_103])).

tff(c_23648,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_23625,c_22689])).

tff(c_23710,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_23648,c_22])).

tff(c_23718,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22620,c_23710])).

tff(c_23720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13399,c_23718])).

tff(c_23722,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_13391])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_23760,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13392,c_23722,c_30])).

tff(c_23764,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23760,c_4])).

tff(c_23721,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_13391])).

tff(c_23723,plain,(
    ! [A_591,B_592] :
      ( k3_xboole_0(A_591,B_592) = k1_xboole_0
      | ~ r1_xboole_0(A_591,B_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23737,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23721,c_23723])).

tff(c_23770,plain,(
    ! [A_595,B_596] : k2_xboole_0(k3_xboole_0(A_595,B_596),k4_xboole_0(A_595,B_596)) = A_595 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_23785,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_23737,c_23770])).

tff(c_23903,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_23785,c_103])).

tff(c_24082,plain,(
    ! [A_613,B_614,C_615] : k4_xboole_0(k4_xboole_0(A_613,B_614),C_615) = k4_xboole_0(A_613,k2_xboole_0(B_614,C_615)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_25313,plain,(
    ! [C_640] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_640)) = k4_xboole_0('#skF_5',C_640) ),
    inference(superposition,[status(thm),theory(equality)],[c_23903,c_24082])).

tff(c_25336,plain,(
    ! [C_640] : k4_xboole_0('#skF_5',k4_xboole_0('#skF_5',C_640)) = k3_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_640)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25313,c_22])).

tff(c_25371,plain,(
    ! [C_640] : k3_xboole_0('#skF_5',k2_xboole_0('#skF_6',C_640)) = k3_xboole_0('#skF_5',C_640) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_25336])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_23894,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13392,c_23722,c_38])).

tff(c_23898,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_23894])).

tff(c_27208,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25371,c_23898])).

tff(c_27211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23764,c_27208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:55:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.88/3.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.61  
% 8.88/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.61  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.88/3.61  
% 8.88/3.61  %Foreground sorts:
% 8.88/3.61  
% 8.88/3.61  
% 8.88/3.61  %Background operators:
% 8.88/3.61  
% 8.88/3.61  
% 8.88/3.61  %Foreground operators:
% 8.88/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.88/3.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.88/3.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.88/3.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.88/3.61  tff('#skF_7', type, '#skF_7': $i).
% 8.88/3.61  tff('#skF_5', type, '#skF_5': $i).
% 8.88/3.61  tff('#skF_6', type, '#skF_6': $i).
% 8.88/3.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.88/3.61  tff('#skF_2', type, '#skF_2': $i).
% 8.88/3.61  tff('#skF_3', type, '#skF_3': $i).
% 8.88/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.88/3.61  tff('#skF_4', type, '#skF_4': $i).
% 8.88/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.88/3.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.88/3.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.88/3.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.88/3.61  
% 8.88/3.65  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.88/3.65  tff(f_78, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.88/3.65  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.88/3.65  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.88/3.65  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.88/3.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.88/3.65  tff(f_59, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 8.88/3.65  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.88/3.65  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.88/3.65  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.88/3.65  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.88/3.65  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.88/3.65  tff(c_185, plain, (![A_31, B_32]: (r1_xboole_0(A_31, B_32) | k3_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.88/3.65  tff(c_34, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.88/3.65  tff(c_183, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 8.88/3.65  tff(c_189, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_185, c_183])).
% 8.88/3.65  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.88/3.65  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.88/3.65  tff(c_10778, plain, (![A_270, B_271]: (k4_xboole_0(A_270, k4_xboole_0(A_270, B_271))=k3_xboole_0(A_270, B_271))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.88/3.65  tff(c_10796, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_10778])).
% 8.88/3.65  tff(c_10799, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10796])).
% 8.88/3.65  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.88/3.65  tff(c_36, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.88/3.65  tff(c_40, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 8.88/3.65  tff(c_394, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_40])).
% 8.88/3.65  tff(c_32, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.88/3.65  tff(c_41, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | r1_xboole_0('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 8.88/3.65  tff(c_353, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_41])).
% 8.88/3.65  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.88/3.65  tff(c_357, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_353, c_4])).
% 8.88/3.65  tff(c_24, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.88/3.65  tff(c_364, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_357, c_24])).
% 8.88/3.65  tff(c_87, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.88/3.65  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.88/3.65  tff(c_103, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_87, c_14])).
% 8.88/3.65  tff(c_373, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_364, c_103])).
% 8.88/3.65  tff(c_28, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.88/3.65  tff(c_39, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | r1_xboole_0('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 8.88/3.65  tff(c_200, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_39])).
% 8.88/3.65  tff(c_204, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_200, c_4])).
% 8.88/3.65  tff(c_209, plain, (![A_35, B_36]: (k2_xboole_0(k3_xboole_0(A_35, B_36), k4_xboole_0(A_35, B_36))=A_35)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.88/3.65  tff(c_218, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_7'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_204, c_209])).
% 8.88/3.65  tff(c_233, plain, (k4_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_218, c_103])).
% 8.88/3.65  tff(c_400, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k4_xboole_0(A_49, B_50), C_51)=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_450, plain, (![C_51]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_7', C_51))=k4_xboole_0('#skF_5', C_51))), inference(superposition, [status(thm), theory('equality')], [c_233, c_400])).
% 8.88/3.65  tff(c_26, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.88/3.65  tff(c_301, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.88/3.65  tff(c_307, plain, (![A_13, C_42]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_301])).
% 8.88/3.65  tff(c_311, plain, (![C_42]: (~r2_hidden(C_42, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_307])).
% 8.88/3.65  tff(c_251, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.88/3.65  tff(c_272, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_251])).
% 8.88/3.65  tff(c_276, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_272])).
% 8.88/3.65  tff(c_410, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(B_50, k4_xboole_0(A_49, B_50)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_400, c_276])).
% 8.88/3.65  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.88/3.65  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k4_xboole_0(A_15, B_16), C_17)=k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.88/3.65  tff(c_417, plain, (![A_49, B_50, B_19]: (k4_xboole_0(A_49, k2_xboole_0(B_50, k4_xboole_0(k4_xboole_0(A_49, B_50), B_19)))=k3_xboole_0(k4_xboole_0(A_49, B_50), B_19))), inference(superposition, [status(thm), theory('equality')], [c_400, c_22])).
% 8.88/3.65  tff(c_3084, plain, (![A_111, B_112, B_113]: (k4_xboole_0(A_111, k2_xboole_0(B_112, k4_xboole_0(A_111, k2_xboole_0(B_112, B_113))))=k3_xboole_0(k4_xboole_0(A_111, B_112), B_113))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_417])).
% 8.88/3.65  tff(c_3282, plain, (![A_111, A_5]: (k4_xboole_0(A_111, k2_xboole_0(A_5, k4_xboole_0(A_111, A_5)))=k3_xboole_0(k4_xboole_0(A_111, A_5), A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3084])).
% 8.88/3.65  tff(c_3327, plain, (![A_114, A_115]: (k3_xboole_0(k4_xboole_0(A_114, A_115), A_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_410, c_3282])).
% 8.88/3.65  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), k3_xboole_0(A_7, B_8)) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.88/3.65  tff(c_3350, plain, (![A_114, A_115]: (r2_hidden('#skF_1'(k4_xboole_0(A_114, A_115), A_115), k1_xboole_0) | r1_xboole_0(k4_xboole_0(A_114, A_115), A_115))), inference(superposition, [status(thm), theory('equality')], [c_3327, c_10])).
% 8.88/3.65  tff(c_3460, plain, (![A_116, A_117]: (r1_xboole_0(k4_xboole_0(A_116, A_117), A_117))), inference(negUnitSimplification, [status(thm)], [c_311, c_3350])).
% 8.88/3.65  tff(c_3666, plain, (![C_119]: (r1_xboole_0(k4_xboole_0('#skF_5', C_119), k2_xboole_0('#skF_7', C_119)))), inference(superposition, [status(thm), theory('equality')], [c_450, c_3460])).
% 8.88/3.65  tff(c_3720, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_7', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_3666])).
% 8.88/3.65  tff(c_3759, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3720])).
% 8.88/3.65  tff(c_3761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_394, c_3759])).
% 8.88/3.65  tff(c_3762, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_40])).
% 8.88/3.65  tff(c_3772, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3762, c_4])).
% 8.88/3.65  tff(c_3791, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3772, c_24])).
% 8.88/3.65  tff(c_3862, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3791, c_103])).
% 8.88/3.65  tff(c_3910, plain, (![A_124, B_125, C_126]: (k4_xboole_0(k4_xboole_0(A_124, B_125), C_126)=k4_xboole_0(A_124, k2_xboole_0(B_125, C_126)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_4248, plain, (![A_132, C_133]: (k4_xboole_0(A_132, k2_xboole_0(A_132, C_133))=k4_xboole_0(k1_xboole_0, C_133))), inference(superposition, [status(thm), theory('equality')], [c_276, c_3910])).
% 8.88/3.65  tff(c_4306, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4248])).
% 8.88/3.65  tff(c_4314, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_276, c_4306])).
% 8.88/3.65  tff(c_3952, plain, (![A_14, C_126]: (k4_xboole_0(A_14, k2_xboole_0(A_14, C_126))=k4_xboole_0(k1_xboole_0, C_126))), inference(superposition, [status(thm), theory('equality')], [c_276, c_3910])).
% 8.88/3.65  tff(c_4489, plain, (![A_138, C_139]: (k4_xboole_0(A_138, k2_xboole_0(A_138, C_139))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_3952])).
% 8.88/3.65  tff(c_4741, plain, (![B_144, A_145]: (k4_xboole_0(B_144, k2_xboole_0(A_145, B_144))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4489])).
% 8.88/3.65  tff(c_4802, plain, (![A_20, B_21]: (k4_xboole_0(k4_xboole_0(A_20, B_21), A_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_4741])).
% 8.88/3.65  tff(c_5657, plain, (![A_162, B_163, C_164]: (k4_xboole_0(k4_xboole_0(A_162, B_163), k4_xboole_0(A_162, k2_xboole_0(B_163, C_164)))=k3_xboole_0(k4_xboole_0(A_162, B_163), C_164))), inference(superposition, [status(thm), theory('equality')], [c_3910, c_22])).
% 8.88/3.65  tff(c_5794, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_2')=k3_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3862, c_5657])).
% 8.88/3.65  tff(c_5874, plain, (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4802, c_5794])).
% 8.88/3.65  tff(c_6106, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3'))=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5874, c_24])).
% 8.88/3.65  tff(c_6113, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_103, c_20, c_6106])).
% 8.88/3.65  tff(c_6200, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6113, c_5874])).
% 8.88/3.65  tff(c_6202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_6200])).
% 8.88/3.65  tff(c_6203, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_41])).
% 8.88/3.65  tff(c_6212, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_6203, c_4])).
% 8.88/3.65  tff(c_6219, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_6212, c_24])).
% 8.88/3.65  tff(c_6585, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_6219, c_103])).
% 8.88/3.65  tff(c_6225, plain, (![A_170, B_171, C_172]: (k4_xboole_0(k4_xboole_0(A_170, B_171), C_172)=k4_xboole_0(A_170, k2_xboole_0(B_171, C_172)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_6378, plain, (![A_175, C_176]: (k4_xboole_0(A_175, k2_xboole_0(A_175, C_176))=k4_xboole_0(k1_xboole_0, C_176))), inference(superposition, [status(thm), theory('equality')], [c_276, c_6225])).
% 8.88/3.65  tff(c_6436, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_6378])).
% 8.88/3.65  tff(c_6444, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_276, c_6436])).
% 8.88/3.65  tff(c_6258, plain, (![A_14, C_172]: (k4_xboole_0(A_14, k2_xboole_0(A_14, C_172))=k4_xboole_0(k1_xboole_0, C_172))), inference(superposition, [status(thm), theory('equality')], [c_276, c_6225])).
% 8.88/3.65  tff(c_6593, plain, (![A_182, C_183]: (k4_xboole_0(A_182, k2_xboole_0(A_182, C_183))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6444, c_6258])).
% 8.88/3.65  tff(c_6888, plain, (![B_190, A_191]: (k4_xboole_0(B_190, k2_xboole_0(A_191, B_190))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6593])).
% 8.88/3.65  tff(c_6933, plain, (![A_20, B_21]: (k4_xboole_0(k4_xboole_0(A_20, B_21), A_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_6888])).
% 8.88/3.65  tff(c_10060, plain, (![A_256, B_257, C_258]: (k4_xboole_0(k4_xboole_0(A_256, B_257), k4_xboole_0(A_256, k2_xboole_0(B_257, C_258)))=k3_xboole_0(k4_xboole_0(A_256, B_257), C_258))), inference(superposition, [status(thm), theory('equality')], [c_6225, c_22])).
% 8.88/3.65  tff(c_10212, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_2')=k3_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6585, c_10060])).
% 8.88/3.65  tff(c_10319, plain, (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6933, c_10212])).
% 8.88/3.65  tff(c_10617, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3'))=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10319, c_24])).
% 8.88/3.65  tff(c_10627, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6585, c_103, c_20, c_10617])).
% 8.88/3.65  tff(c_10727, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10627, c_10319])).
% 8.88/3.65  tff(c_10729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_10727])).
% 8.88/3.65  tff(c_10730, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_39])).
% 8.88/3.65  tff(c_10739, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10730, c_4])).
% 8.88/3.65  tff(c_10744, plain, (![A_264, B_265]: (k2_xboole_0(k3_xboole_0(A_264, B_265), k4_xboole_0(A_264, B_265))=A_264)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.88/3.65  tff(c_10753, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_10739, c_10744])).
% 8.88/3.65  tff(c_10888, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_10753, c_103])).
% 8.88/3.65  tff(c_10937, plain, (![A_282, B_283, C_284]: (k4_xboole_0(k4_xboole_0(A_282, B_283), C_284)=k4_xboole_0(A_282, k2_xboole_0(B_283, C_284)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_10940, plain, (![A_282, B_283, C_284, C_17]: (k4_xboole_0(k4_xboole_0(A_282, k2_xboole_0(B_283, C_284)), C_17)=k4_xboole_0(k4_xboole_0(A_282, B_283), k2_xboole_0(C_284, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_10937, c_20])).
% 8.88/3.65  tff(c_12975, plain, (![A_333, B_334, C_335, C_336]: (k4_xboole_0(A_333, k2_xboole_0(k2_xboole_0(B_334, C_335), C_336))=k4_xboole_0(A_333, k2_xboole_0(B_334, k2_xboole_0(C_335, C_336))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_10940])).
% 8.88/3.65  tff(c_10970, plain, (![C_284]: (k4_xboole_0('#skF_2', k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), C_284))=k4_xboole_0('#skF_2', C_284))), inference(superposition, [status(thm), theory('equality')], [c_10888, c_10937])).
% 8.88/3.65  tff(c_13292, plain, (![C_340]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_340)))=k4_xboole_0('#skF_2', C_340))), inference(superposition, [status(thm), theory('equality')], [c_12975, c_10970])).
% 8.88/3.65  tff(c_13341, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_13292])).
% 8.88/3.65  tff(c_13351, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10888, c_13341])).
% 8.88/3.65  tff(c_13376, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13351, c_22])).
% 8.88/3.65  tff(c_13388, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10799, c_13376])).
% 8.88/3.65  tff(c_13390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_13388])).
% 8.88/3.65  tff(c_13392, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 8.88/3.65  tff(c_13395, plain, (![A_341, B_342]: (r1_xboole_0(A_341, B_342) | k3_xboole_0(A_341, B_342)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.88/3.65  tff(c_13391, plain, (~r1_xboole_0('#skF_2', '#skF_4') | r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 8.88/3.65  tff(c_13394, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_13391])).
% 8.88/3.65  tff(c_13399, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_13395, c_13394])).
% 8.88/3.65  tff(c_22595, plain, (![A_555, B_556]: (k4_xboole_0(A_555, k4_xboole_0(A_555, B_556))=k3_xboole_0(A_555, B_556))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.88/3.65  tff(c_22616, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_22595])).
% 8.88/3.65  tff(c_22620, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22616])).
% 8.88/3.65  tff(c_13400, plain, (![A_343, B_344]: (k3_xboole_0(A_343, B_344)=k1_xboole_0 | ~r1_xboole_0(A_343, B_344))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.88/3.65  tff(c_13411, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_13392, c_13400])).
% 8.88/3.65  tff(c_22551, plain, (![A_553, B_554]: (k2_xboole_0(k3_xboole_0(A_553, B_554), k4_xboole_0(A_553, B_554))=A_553)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.88/3.65  tff(c_22563, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13411, c_22551])).
% 8.88/3.65  tff(c_22577, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_22563, c_103])).
% 8.88/3.65  tff(c_22710, plain, (![A_563, B_564, C_565]: (k4_xboole_0(k4_xboole_0(A_563, B_564), C_565)=k4_xboole_0(A_563, k2_xboole_0(B_564, C_565)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_22858, plain, (![C_568]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_568))=k4_xboole_0('#skF_2', C_568))), inference(superposition, [status(thm), theory('equality')], [c_22577, c_22710])).
% 8.88/3.65  tff(c_23625, plain, (![B_590]: (k4_xboole_0('#skF_2', k2_xboole_0(B_590, '#skF_3'))=k4_xboole_0('#skF_2', B_590))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22858])).
% 8.88/3.65  tff(c_21371, plain, (![A_516, B_517]: (k4_xboole_0(A_516, k4_xboole_0(A_516, B_517))=k3_xboole_0(A_516, B_517))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.88/3.65  tff(c_21395, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_21371])).
% 8.88/3.65  tff(c_21400, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_21395])).
% 8.88/3.65  tff(c_21302, plain, (![A_514, B_515]: (k2_xboole_0(k3_xboole_0(A_514, B_515), k4_xboole_0(A_514, B_515))=A_514)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.88/3.65  tff(c_21317, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13411, c_21302])).
% 8.88/3.65  tff(c_21331, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_21317, c_103])).
% 8.88/3.65  tff(c_21523, plain, (![A_526, B_527, C_528]: (k4_xboole_0(k4_xboole_0(A_526, B_527), C_528)=k4_xboole_0(A_526, k2_xboole_0(B_527, C_528)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_21695, plain, (![C_531]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_531))=k4_xboole_0('#skF_2', C_531))), inference(superposition, [status(thm), theory('equality')], [c_21331, c_21523])).
% 8.88/3.65  tff(c_22422, plain, (![A_548]: (k4_xboole_0('#skF_2', k2_xboole_0(A_548, '#skF_3'))=k4_xboole_0('#skF_2', A_548))), inference(superposition, [status(thm), theory('equality')], [c_2, c_21695])).
% 8.88/3.65  tff(c_13518, plain, (![A_347, B_348]: (k4_xboole_0(A_347, k4_xboole_0(A_347, B_348))=k3_xboole_0(A_347, B_348))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.88/3.65  tff(c_13542, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_13518])).
% 8.88/3.65  tff(c_13547, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_13542])).
% 8.88/3.65  tff(c_13434, plain, (![A_345, B_346]: (k2_xboole_0(k3_xboole_0(A_345, B_346), k4_xboole_0(A_345, B_346))=A_345)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.88/3.65  tff(c_13446, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13411, c_13434])).
% 8.88/3.65  tff(c_13467, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13446, c_103])).
% 8.88/3.65  tff(c_19225, plain, (![A_468, B_469, C_470]: (k4_xboole_0(k4_xboole_0(A_468, B_469), C_470)=k4_xboole_0(A_468, k2_xboole_0(B_469, C_470)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_20891, plain, (![C_506]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_506))=k4_xboole_0('#skF_2', C_506))), inference(superposition, [status(thm), theory('equality')], [c_13467, c_19225])).
% 8.88/3.65  tff(c_21126, plain, (![B_509]: (k4_xboole_0('#skF_2', k2_xboole_0(B_509, '#skF_3'))=k4_xboole_0('#skF_2', B_509))), inference(superposition, [status(thm), theory('equality')], [c_2, c_20891])).
% 8.88/3.65  tff(c_13609, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_40])).
% 8.88/3.65  tff(c_13420, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_39])).
% 8.88/3.65  tff(c_13424, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_13420, c_4])).
% 8.88/3.65  tff(c_13443, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_7'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_13424, c_13434])).
% 8.88/3.65  tff(c_13511, plain, (k4_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_13443, c_103])).
% 8.88/3.65  tff(c_13429, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_41])).
% 8.88/3.65  tff(c_13433, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_13429, c_4])).
% 8.88/3.65  tff(c_13460, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_13433, c_24])).
% 8.88/3.65  tff(c_13490, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_13460, c_103])).
% 8.88/3.65  tff(c_13703, plain, (![A_362, B_363, C_364]: (k4_xboole_0(k4_xboole_0(A_362, B_363), C_364)=k4_xboole_0(A_362, k2_xboole_0(B_363, C_364)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_13753, plain, (![C_364]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_364))=k4_xboole_0('#skF_5', C_364))), inference(superposition, [status(thm), theory('equality')], [c_13490, c_13703])).
% 8.88/3.65  tff(c_13617, plain, (![A_351, B_352, C_353]: (~r1_xboole_0(A_351, B_352) | ~r2_hidden(C_353, k3_xboole_0(A_351, B_352)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.88/3.65  tff(c_13632, plain, (![A_13, C_353]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_353, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_13617])).
% 8.88/3.65  tff(c_13640, plain, (![C_353]: (~r2_hidden(C_353, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_13632])).
% 8.88/3.65  tff(c_15663, plain, (![A_404, B_405, C_406]: (k4_xboole_0(k4_xboole_0(A_404, B_405), k4_xboole_0(A_404, k2_xboole_0(B_405, C_406)))=k3_xboole_0(k4_xboole_0(A_404, B_405), C_406))), inference(superposition, [status(thm), theory('equality')], [c_13703, c_22])).
% 8.88/3.65  tff(c_15837, plain, (![A_404, A_5]: (k4_xboole_0(k4_xboole_0(A_404, A_5), k4_xboole_0(A_404, A_5))=k3_xboole_0(k4_xboole_0(A_404, A_5), A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_15663])).
% 8.88/3.65  tff(c_15888, plain, (![A_407, A_408]: (k3_xboole_0(k4_xboole_0(A_407, A_408), A_408)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13547, c_15837])).
% 8.88/3.65  tff(c_15902, plain, (![A_407, A_408]: (r2_hidden('#skF_1'(k4_xboole_0(A_407, A_408), A_408), k1_xboole_0) | r1_xboole_0(k4_xboole_0(A_407, A_408), A_408))), inference(superposition, [status(thm), theory('equality')], [c_15888, c_10])).
% 8.88/3.65  tff(c_16005, plain, (![A_409, A_410]: (r1_xboole_0(k4_xboole_0(A_409, A_410), A_410))), inference(negUnitSimplification, [status(thm)], [c_13640, c_15902])).
% 8.88/3.65  tff(c_19062, plain, (![C_459]: (r1_xboole_0(k4_xboole_0('#skF_5', C_459), k2_xboole_0('#skF_6', C_459)))), inference(superposition, [status(thm), theory('equality')], [c_13753, c_16005])).
% 8.88/3.65  tff(c_19110, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_13511, c_19062])).
% 8.88/3.65  tff(c_19149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13609, c_19110])).
% 8.88/3.65  tff(c_19150, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_40])).
% 8.88/3.65  tff(c_19155, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_19150, c_4])).
% 8.88/3.65  tff(c_19166, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_19155, c_24])).
% 8.88/3.65  tff(c_19608, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_103, c_19166])).
% 8.88/3.65  tff(c_21153, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_21126, c_19608])).
% 8.88/3.65  tff(c_21250, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21153, c_22])).
% 8.88/3.65  tff(c_21261, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13547, c_21250])).
% 8.88/3.65  tff(c_21263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13399, c_21261])).
% 8.88/3.65  tff(c_21264, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_41])).
% 8.88/3.65  tff(c_21273, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_21264, c_4])).
% 8.88/3.65  tff(c_21311, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_21273, c_21302])).
% 8.88/3.65  tff(c_21484, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_21311, c_103])).
% 8.88/3.65  tff(c_22445, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_22422, c_21484])).
% 8.88/3.65  tff(c_22506, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22445, c_22])).
% 8.88/3.65  tff(c_22514, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_21400, c_22506])).
% 8.88/3.65  tff(c_22516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13399, c_22514])).
% 8.88/3.65  tff(c_22517, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_39])).
% 8.88/3.65  tff(c_22526, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22517, c_4])).
% 8.88/3.65  tff(c_22560, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_22526, c_22551])).
% 8.88/3.65  tff(c_22689, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_22560, c_103])).
% 8.88/3.65  tff(c_23648, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_23625, c_22689])).
% 8.88/3.65  tff(c_23710, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_23648, c_22])).
% 8.88/3.65  tff(c_23718, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22620, c_23710])).
% 8.88/3.65  tff(c_23720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13399, c_23718])).
% 8.88/3.65  tff(c_23722, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_13391])).
% 8.88/3.65  tff(c_30, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.88/3.65  tff(c_23760, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13392, c_23722, c_30])).
% 8.88/3.65  tff(c_23764, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_23760, c_4])).
% 8.88/3.65  tff(c_23721, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_13391])).
% 8.88/3.65  tff(c_23723, plain, (![A_591, B_592]: (k3_xboole_0(A_591, B_592)=k1_xboole_0 | ~r1_xboole_0(A_591, B_592))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.88/3.65  tff(c_23737, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_23721, c_23723])).
% 8.88/3.65  tff(c_23770, plain, (![A_595, B_596]: (k2_xboole_0(k3_xboole_0(A_595, B_596), k4_xboole_0(A_595, B_596))=A_595)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.88/3.65  tff(c_23785, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_23737, c_23770])).
% 8.88/3.65  tff(c_23903, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_23785, c_103])).
% 8.88/3.65  tff(c_24082, plain, (![A_613, B_614, C_615]: (k4_xboole_0(k4_xboole_0(A_613, B_614), C_615)=k4_xboole_0(A_613, k2_xboole_0(B_614, C_615)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.88/3.65  tff(c_25313, plain, (![C_640]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_640))=k4_xboole_0('#skF_5', C_640))), inference(superposition, [status(thm), theory('equality')], [c_23903, c_24082])).
% 8.88/3.65  tff(c_25336, plain, (![C_640]: (k4_xboole_0('#skF_5', k4_xboole_0('#skF_5', C_640))=k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_640)))), inference(superposition, [status(thm), theory('equality')], [c_25313, c_22])).
% 8.88/3.65  tff(c_25371, plain, (![C_640]: (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', C_640))=k3_xboole_0('#skF_5', C_640))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_25336])).
% 8.88/3.65  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.88/3.65  tff(c_38, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.88/3.65  tff(c_23894, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_13392, c_23722, c_38])).
% 8.88/3.65  tff(c_23898, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_23894])).
% 8.88/3.65  tff(c_27208, plain, (k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_25371, c_23898])).
% 8.88/3.65  tff(c_27211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23764, c_27208])).
% 8.88/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.65  
% 8.88/3.65  Inference rules
% 8.88/3.65  ----------------------
% 8.88/3.65  #Ref     : 0
% 8.88/3.65  #Sup     : 6811
% 8.88/3.65  #Fact    : 0
% 8.88/3.65  #Define  : 0
% 8.88/3.65  #Split   : 9
% 8.88/3.65  #Chain   : 0
% 8.88/3.65  #Close   : 0
% 8.88/3.65  
% 8.88/3.65  Ordering : KBO
% 8.88/3.65  
% 8.88/3.65  Simplification rules
% 8.88/3.65  ----------------------
% 8.88/3.65  #Subsume      : 121
% 8.88/3.65  #Demod        : 6242
% 8.88/3.65  #Tautology    : 4339
% 8.88/3.65  #SimpNegUnit  : 73
% 8.88/3.65  #BackRed      : 33
% 8.88/3.65  
% 8.88/3.65  #Partial instantiations: 0
% 8.88/3.65  #Strategies tried      : 1
% 8.88/3.65  
% 8.88/3.65  Timing (in seconds)
% 8.88/3.65  ----------------------
% 8.88/3.65  Preprocessing        : 0.31
% 8.88/3.65  Parsing              : 0.18
% 8.88/3.65  CNF conversion       : 0.02
% 8.88/3.65  Main loop            : 2.51
% 8.88/3.65  Inferencing          : 0.68
% 8.88/3.65  Reduction            : 1.24
% 8.88/3.65  Demodulation         : 1.04
% 8.88/3.65  BG Simplification    : 0.09
% 8.88/3.65  Subsumption          : 0.34
% 8.88/3.65  Abstraction          : 0.12
% 8.88/3.65  MUC search           : 0.00
% 8.88/3.65  Cooper               : 0.00
% 8.88/3.65  Total                : 2.90
% 8.88/3.65  Index Insertion      : 0.00
% 8.88/3.65  Index Deletion       : 0.00
% 8.88/3.65  Index Matching       : 0.00
% 8.88/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
