%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:06 EST 2020

% Result     : Theorem 26.15s
% Output     : CNFRefutation 26.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 588 expanded)
%              Number of leaves         :   23 ( 210 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 606 expanded)
%              Number of equality atoms :  117 ( 605 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_35,B_36] : k3_xboole_0(A_35,k2_xboole_0(A_35,B_36)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_1447,plain,(
    ! [A_85,B_86,C_87] : k4_xboole_0(k3_xboole_0(A_85,B_86),C_87) = k3_xboole_0(A_85,k4_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1515,plain,(
    ! [A_3,C_87] : k3_xboole_0(A_3,k4_xboole_0(A_3,C_87)) = k4_xboole_0(A_3,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1447])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k3_xboole_0(A_20,B_21),C_22) = k3_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1340,plain,(
    ! [A_82,B_83,C_84] : k4_xboole_0(k4_xboole_0(A_82,B_83),C_84) = k4_xboole_0(A_82,k2_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1400,plain,(
    ! [A_18,B_19,C_84] : k4_xboole_0(A_18,k2_xboole_0(k4_xboole_0(A_18,B_19),C_84)) = k4_xboole_0(k3_xboole_0(A_18,B_19),C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1340])).

tff(c_11692,plain,(
    ! [A_212,B_213,C_214] : k4_xboole_0(A_212,k2_xboole_0(k4_xboole_0(A_212,B_213),C_214)) = k3_xboole_0(A_212,k4_xboole_0(B_213,C_214)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1400])).

tff(c_11911,plain,(
    ! [A_212,B_2,B_213] : k4_xboole_0(A_212,k2_xboole_0(B_2,k4_xboole_0(A_212,B_213))) = k3_xboole_0(A_212,k4_xboole_0(B_213,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11692])).

tff(c_16,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1361,plain,(
    ! [C_84,A_82,B_83] : k2_xboole_0(C_84,k4_xboole_0(A_82,k2_xboole_0(B_83,C_84))) = k2_xboole_0(C_84,k4_xboole_0(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_16])).

tff(c_1404,plain,(
    ! [A_82,B_83,B_19] : k4_xboole_0(A_82,k2_xboole_0(B_83,k4_xboole_0(k4_xboole_0(A_82,B_83),B_19))) = k3_xboole_0(k4_xboole_0(A_82,B_83),B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1340])).

tff(c_19464,plain,(
    ! [A_282,B_283,B_284] : k4_xboole_0(A_282,k2_xboole_0(B_283,k4_xboole_0(A_282,k2_xboole_0(B_283,B_284)))) = k3_xboole_0(k4_xboole_0(A_282,B_283),B_284) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1404])).

tff(c_19765,plain,(
    ! [A_282,B_2,A_1] : k4_xboole_0(A_282,k2_xboole_0(B_2,k4_xboole_0(A_282,k2_xboole_0(A_1,B_2)))) = k3_xboole_0(k4_xboole_0(A_282,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19464])).

tff(c_19842,plain,(
    ! [A_282,B_2,A_1] : k4_xboole_0(A_282,k2_xboole_0(B_2,k4_xboole_0(A_282,A_1))) = k3_xboole_0(k4_xboole_0(A_282,B_2),A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_19765])).

tff(c_108965,plain,(
    ! [A_282,B_2,A_1] : k3_xboole_0(k4_xboole_0(A_282,B_2),A_1) = k3_xboole_0(A_282,k4_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11911,c_19842])).

tff(c_101,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4,B_5] : k3_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_40,B_39] : k3_xboole_0(A_40,k2_xboole_0(B_39,A_40)) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_6])).

tff(c_53,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_479,plain,(
    ! [A_58,B_59] : k2_xboole_0(A_58,k4_xboole_0(B_59,A_58)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_526,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_479])).

tff(c_541,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_526])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_529,plain,(
    ! [A_16,B_17] : k2_xboole_0(k2_xboole_0(A_16,B_17),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_479])).

tff(c_720,plain,(
    ! [A_67,B_68] : k2_xboole_0(k2_xboole_0(A_67,B_68),A_67) = k2_xboole_0(A_67,B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_529])).

tff(c_542,plain,(
    ! [A_16,B_17] : k2_xboole_0(k2_xboole_0(A_16,B_17),A_16) = k2_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_529])).

tff(c_723,plain,(
    ! [A_67,B_68] : k2_xboole_0(k2_xboole_0(A_67,B_68),k2_xboole_0(A_67,B_68)) = k2_xboole_0(k2_xboole_0(A_67,B_68),A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_542])).

tff(c_797,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k2_xboole_0(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_2,c_723])).

tff(c_122,plain,(
    ! [A_40,B_39] : k4_xboole_0(A_40,k2_xboole_0(B_39,A_40)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_20])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | k4_xboole_0(B_8,A_7) != k4_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_17568,plain,(
    ! [A_263,B_264,C_265] :
      ( k4_xboole_0(A_263,B_264) = C_265
      | k4_xboole_0(C_265,k4_xboole_0(A_263,B_264)) != k4_xboole_0(A_263,k2_xboole_0(B_264,C_265)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_10])).

tff(c_17744,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | k4_xboole_0(A_18,k2_xboole_0(B_19,A_18)) != k3_xboole_0(A_18,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_17568])).

tff(c_22701,plain,(
    ! [A_324,B_325] :
      ( k4_xboole_0(A_324,B_325) = A_324
      | k3_xboole_0(A_324,B_325) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_17744])).

tff(c_403,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_435,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_403])).

tff(c_443,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_435])).

tff(c_11974,plain,(
    ! [C_215,B_216] : k3_xboole_0(C_215,k4_xboole_0(B_216,C_215)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11692,c_122])).

tff(c_406,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,k4_xboole_0(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_22])).

tff(c_8156,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1515,c_406])).

tff(c_11991,plain,(
    ! [C_215,B_216] : k4_xboole_0(C_215,k4_xboole_0(B_216,C_215)) = k4_xboole_0(C_215,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11974,c_8156])).

tff(c_12093,plain,(
    ! [C_215,B_216] : k4_xboole_0(C_215,k4_xboole_0(B_216,C_215)) = C_215 ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_11991])).

tff(c_46750,plain,(
    ! [B_457,A_458] :
      ( k4_xboole_0(B_457,A_458) = B_457
      | k3_xboole_0(A_458,B_457) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22701,c_12093])).

tff(c_135,plain,(
    ! [A_40] : k2_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_4])).

tff(c_13974,plain,(
    ! [C_237,A_238,B_239] : k2_xboole_0(C_237,k4_xboole_0(A_238,k2_xboole_0(B_239,C_237))) = k2_xboole_0(C_237,k4_xboole_0(A_238,B_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_16])).

tff(c_14321,plain,(
    ! [C_237,B_239] : k2_xboole_0(C_237,k4_xboole_0(k2_xboole_0(B_239,C_237),B_239)) = k2_xboole_0(C_237,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_13974])).

tff(c_23857,plain,(
    ! [C_331,B_332] : k2_xboole_0(C_331,k4_xboole_0(k2_xboole_0(B_332,C_331),B_332)) = C_331 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14321])).

tff(c_1022,plain,(
    ! [A_73,B_74,C_75] : k2_xboole_0(k2_xboole_0(A_73,B_74),C_75) = k2_xboole_0(A_73,k2_xboole_0(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3534,plain,(
    ! [A_124,A_122,B_123] : k2_xboole_0(A_124,k2_xboole_0(A_122,B_123)) = k2_xboole_0(A_122,k2_xboole_0(B_123,A_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1022])).

tff(c_4007,plain,(
    ! [A_40,A_124] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_40,A_124)) = k2_xboole_0(A_124,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_3534])).

tff(c_24009,plain,(
    ! [B_332,C_331] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_332,C_331),B_332),C_331) = k2_xboole_0(k1_xboole_0,C_331) ),
    inference(superposition,[status(thm),theory(equality)],[c_23857,c_4007])).

tff(c_27181,plain,(
    ! [B_352,C_353] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_352,C_353),B_352),C_353) = C_353 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_24009])).

tff(c_27647,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(k2_xboole_0(A_1,B_2),B_2),A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_27181])).

tff(c_46771,plain,(
    ! [A_1,A_458] :
      ( k2_xboole_0(k2_xboole_0(A_1,A_458),A_1) = A_1
      | k3_xboole_0(A_458,k2_xboole_0(A_1,A_458)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46750,c_27647])).

tff(c_47437,plain,(
    ! [A_459,A_460] :
      ( k2_xboole_0(A_459,A_460) = A_459
      | k1_xboole_0 != A_460 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_797,c_2,c_46771])).

tff(c_48197,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47437])).

tff(c_14300,plain,(
    ! [A_40,B_39] : k2_xboole_0(A_40,k4_xboole_0(A_40,B_39)) = k2_xboole_0(A_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_13974])).

tff(c_14415,plain,(
    ! [A_240,B_241] : k2_xboole_0(A_240,k4_xboole_0(A_240,B_241)) = A_240 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14300])).

tff(c_14542,plain,(
    ! [A_240,B_241] : k2_xboole_0(k4_xboole_0(A_240,B_241),A_240) = k2_xboole_0(k1_xboole_0,A_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_14415,c_4007])).

tff(c_14758,plain,(
    ! [A_240,B_241] : k2_xboole_0(k4_xboole_0(A_240,B_241),A_240) = A_240 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_14542])).

tff(c_49640,plain,(
    ! [A_467,B_468] :
      ( k4_xboole_0(A_467,B_468) = A_467
      | k1_xboole_0 != A_467 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47437,c_14758])).

tff(c_1487,plain,(
    ! [A_85,B_86] : k3_xboole_0(A_85,k4_xboole_0(B_86,k3_xboole_0(A_85,B_86))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_60])).

tff(c_53336,plain,(
    ! [A_85] : k3_xboole_0(A_85,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_49640,c_1487])).

tff(c_14706,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_14415])).

tff(c_11780,plain,(
    ! [C_214,B_213] : k3_xboole_0(C_214,k4_xboole_0(B_213,C_214)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11692,c_122])).

tff(c_30454,plain,(
    ! [B_374,A_375] :
      ( k3_xboole_0(B_374,A_375) = k1_xboole_0
      | k3_xboole_0(A_375,B_374) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22701,c_11780])).

tff(c_35692,plain,(
    ! [B_403,A_404] : k3_xboole_0(k4_xboole_0(B_403,k3_xboole_0(A_404,B_403)),A_404) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1487,c_30454])).

tff(c_14406,plain,(
    ! [A_40,B_39] : k2_xboole_0(A_40,k4_xboole_0(A_40,B_39)) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14300])).

tff(c_513,plain,(
    ! [A_18,B_19] : k2_xboole_0(k4_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(k4_xboole_0(A_18,B_19),A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_479])).

tff(c_537,plain,(
    ! [A_18,B_19] : k2_xboole_0(k4_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_513])).

tff(c_14413,plain,(
    ! [A_18,B_19] : k2_xboole_0(k4_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14406,c_537])).

tff(c_35751,plain,(
    ! [B_403,A_404] : k2_xboole_0(k4_xboole_0(k4_xboole_0(B_403,k3_xboole_0(A_404,B_403)),A_404),k1_xboole_0) = k4_xboole_0(B_403,k3_xboole_0(A_404,B_403)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35692,c_14413])).

tff(c_66504,plain,(
    ! [B_553,A_554] : k4_xboole_0(B_553,k3_xboole_0(A_554,B_553)) = k4_xboole_0(B_553,A_554) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14706,c_2,c_4,c_18,c_35751])).

tff(c_66717,plain,(
    ! [B_553,A_554] : k4_xboole_0(B_553,k4_xboole_0(B_553,A_554)) = k3_xboole_0(B_553,k3_xboole_0(A_554,B_553)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66504,c_22])).

tff(c_66922,plain,(
    ! [B_553,A_554] : k3_xboole_0(B_553,k3_xboole_0(A_554,B_553)) = k3_xboole_0(B_553,A_554) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_66717])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_15325,plain,(
    ! [C_248,A_249,B_250] : k2_xboole_0(C_248,k3_xboole_0(A_249,k4_xboole_0(B_250,C_248))) = k2_xboole_0(C_248,k3_xboole_0(A_249,B_250)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_16])).

tff(c_15645,plain,(
    ! [A_3,A_249] : k2_xboole_0(A_3,k3_xboole_0(A_249,k1_xboole_0)) = k2_xboole_0(A_3,k3_xboole_0(A_249,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_15325])).

tff(c_15726,plain,(
    ! [A_3,A_249] : k2_xboole_0(A_3,k3_xboole_0(A_249,A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8,c_15645])).

tff(c_4138,plain,(
    ! [A_125,A_126] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_125,A_126)) = k2_xboole_0(A_126,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_3534])).

tff(c_4335,plain,(
    ! [B_12,A_11] : k2_xboole_0(k4_xboole_0(B_12,A_11),A_11) = k2_xboole_0(k1_xboole_0,k2_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4138])).

tff(c_4405,plain,(
    ! [B_12,A_11] : k2_xboole_0(k4_xboole_0(B_12,A_11),A_11) = k2_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_4335])).

tff(c_66693,plain,(
    ! [B_553,A_554] : k2_xboole_0(k4_xboole_0(B_553,A_554),k3_xboole_0(A_554,B_553)) = k2_xboole_0(k3_xboole_0(A_554,B_553),B_553) ),
    inference(superposition,[status(thm),theory(equality)],[c_66504,c_4405])).

tff(c_82676,plain,(
    ! [B_632,A_633] : k2_xboole_0(k4_xboole_0(B_632,A_633),k3_xboole_0(A_633,B_632)) = B_632 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15726,c_2,c_66693])).

tff(c_83097,plain,(
    ! [A_554,B_553] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_554,B_553),B_553),k3_xboole_0(B_553,A_554)) = k3_xboole_0(A_554,B_553) ),
    inference(superposition,[status(thm),theory(equality)],[c_66922,c_82676])).

tff(c_83467,plain,(
    ! [B_553,A_554] : k3_xboole_0(B_553,A_554) = k3_xboole_0(A_554,B_553) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48197,c_53336,c_60,c_24,c_83097])).

tff(c_30,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_83528,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k4_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83467,c_31])).

tff(c_108967,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108965,c_83528])).

tff(c_108980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1515,c_2,c_18,c_108967])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.15/15.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.22/15.77  
% 26.22/15.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.22/15.78  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 26.22/15.78  
% 26.22/15.78  %Foreground sorts:
% 26.22/15.78  
% 26.22/15.78  
% 26.22/15.78  %Background operators:
% 26.22/15.78  
% 26.22/15.78  
% 26.22/15.78  %Foreground operators:
% 26.22/15.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.22/15.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.22/15.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.22/15.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.22/15.78  tff('#skF_2', type, '#skF_2': $i).
% 26.22/15.78  tff('#skF_3', type, '#skF_3': $i).
% 26.22/15.78  tff('#skF_1', type, '#skF_1': $i).
% 26.22/15.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.22/15.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.22/15.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.22/15.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.22/15.78  
% 26.22/15.81  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 26.22/15.81  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 26.22/15.81  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 26.22/15.81  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 26.22/15.81  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 26.22/15.81  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 26.22/15.81  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 26.22/15.81  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 26.22/15.81  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 26.22/15.81  tff(f_53, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 26.22/15.81  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 26.22/15.81  tff(f_58, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 26.22/15.81  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 26.22/15.81  tff(c_63, plain, (![A_35, B_36]: (k3_xboole_0(A_35, k2_xboole_0(A_35, B_36))=A_35)), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.22/15.81  tff(c_72, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_63])).
% 26.22/15.81  tff(c_1447, plain, (![A_85, B_86, C_87]: (k4_xboole_0(k3_xboole_0(A_85, B_86), C_87)=k3_xboole_0(A_85, k4_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 26.22/15.81  tff(c_1515, plain, (![A_3, C_87]: (k3_xboole_0(A_3, k4_xboole_0(A_3, C_87))=k4_xboole_0(A_3, C_87))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1447])).
% 26.22/15.81  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 26.22/15.81  tff(c_18, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 26.22/15.81  tff(c_24, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k3_xboole_0(A_20, B_21), C_22)=k3_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 26.22/15.81  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.22/15.81  tff(c_1340, plain, (![A_82, B_83, C_84]: (k4_xboole_0(k4_xboole_0(A_82, B_83), C_84)=k4_xboole_0(A_82, k2_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 26.22/15.81  tff(c_1400, plain, (![A_18, B_19, C_84]: (k4_xboole_0(A_18, k2_xboole_0(k4_xboole_0(A_18, B_19), C_84))=k4_xboole_0(k3_xboole_0(A_18, B_19), C_84))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1340])).
% 26.22/15.81  tff(c_11692, plain, (![A_212, B_213, C_214]: (k4_xboole_0(A_212, k2_xboole_0(k4_xboole_0(A_212, B_213), C_214))=k3_xboole_0(A_212, k4_xboole_0(B_213, C_214)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1400])).
% 26.22/15.81  tff(c_11911, plain, (![A_212, B_2, B_213]: (k4_xboole_0(A_212, k2_xboole_0(B_2, k4_xboole_0(A_212, B_213)))=k3_xboole_0(A_212, k4_xboole_0(B_213, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11692])).
% 26.22/15.81  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.22/15.81  tff(c_1361, plain, (![C_84, A_82, B_83]: (k2_xboole_0(C_84, k4_xboole_0(A_82, k2_xboole_0(B_83, C_84)))=k2_xboole_0(C_84, k4_xboole_0(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_1340, c_16])).
% 26.22/15.81  tff(c_1404, plain, (![A_82, B_83, B_19]: (k4_xboole_0(A_82, k2_xboole_0(B_83, k4_xboole_0(k4_xboole_0(A_82, B_83), B_19)))=k3_xboole_0(k4_xboole_0(A_82, B_83), B_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1340])).
% 26.22/15.81  tff(c_19464, plain, (![A_282, B_283, B_284]: (k4_xboole_0(A_282, k2_xboole_0(B_283, k4_xboole_0(A_282, k2_xboole_0(B_283, B_284))))=k3_xboole_0(k4_xboole_0(A_282, B_283), B_284))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1404])).
% 26.22/15.81  tff(c_19765, plain, (![A_282, B_2, A_1]: (k4_xboole_0(A_282, k2_xboole_0(B_2, k4_xboole_0(A_282, k2_xboole_0(A_1, B_2))))=k3_xboole_0(k4_xboole_0(A_282, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_19464])).
% 26.22/15.81  tff(c_19842, plain, (![A_282, B_2, A_1]: (k4_xboole_0(A_282, k2_xboole_0(B_2, k4_xboole_0(A_282, A_1)))=k3_xboole_0(k4_xboole_0(A_282, B_2), A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_19765])).
% 26.22/15.81  tff(c_108965, plain, (![A_282, B_2, A_1]: (k3_xboole_0(k4_xboole_0(A_282, B_2), A_1)=k3_xboole_0(A_282, k4_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_11911, c_19842])).
% 26.22/15.81  tff(c_101, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 26.22/15.81  tff(c_6, plain, (![A_4, B_5]: (k3_xboole_0(A_4, k2_xboole_0(A_4, B_5))=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.22/15.81  tff(c_116, plain, (![A_40, B_39]: (k3_xboole_0(A_40, k2_xboole_0(B_39, A_40))=A_40)), inference(superposition, [status(thm), theory('equality')], [c_101, c_6])).
% 26.22/15.81  tff(c_53, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 26.22/15.81  tff(c_60, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 26.22/15.81  tff(c_479, plain, (![A_58, B_59]: (k2_xboole_0(A_58, k4_xboole_0(B_59, A_58))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.22/15.81  tff(c_526, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_60, c_479])).
% 26.22/15.81  tff(c_541, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_526])).
% 26.22/15.81  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 26.22/15.81  tff(c_529, plain, (![A_16, B_17]: (k2_xboole_0(k2_xboole_0(A_16, B_17), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_479])).
% 26.22/15.81  tff(c_720, plain, (![A_67, B_68]: (k2_xboole_0(k2_xboole_0(A_67, B_68), A_67)=k2_xboole_0(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_529])).
% 26.22/15.81  tff(c_542, plain, (![A_16, B_17]: (k2_xboole_0(k2_xboole_0(A_16, B_17), A_16)=k2_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_529])).
% 26.22/15.81  tff(c_723, plain, (![A_67, B_68]: (k2_xboole_0(k2_xboole_0(A_67, B_68), k2_xboole_0(A_67, B_68))=k2_xboole_0(k2_xboole_0(A_67, B_68), A_67))), inference(superposition, [status(thm), theory('equality')], [c_720, c_542])).
% 26.22/15.81  tff(c_797, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k2_xboole_0(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_2, c_723])).
% 26.22/15.81  tff(c_122, plain, (![A_40, B_39]: (k4_xboole_0(A_40, k2_xboole_0(B_39, A_40))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_20])).
% 26.22/15.81  tff(c_10, plain, (![B_8, A_7]: (B_8=A_7 | k4_xboole_0(B_8, A_7)!=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 26.22/15.81  tff(c_17568, plain, (![A_263, B_264, C_265]: (k4_xboole_0(A_263, B_264)=C_265 | k4_xboole_0(C_265, k4_xboole_0(A_263, B_264))!=k4_xboole_0(A_263, k2_xboole_0(B_264, C_265)))), inference(superposition, [status(thm), theory('equality')], [c_1340, c_10])).
% 26.22/15.81  tff(c_17744, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | k4_xboole_0(A_18, k2_xboole_0(B_19, A_18))!=k3_xboole_0(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_17568])).
% 26.22/15.81  tff(c_22701, plain, (![A_324, B_325]: (k4_xboole_0(A_324, B_325)=A_324 | k3_xboole_0(A_324, B_325)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_17744])).
% 26.22/15.81  tff(c_403, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 26.22/15.81  tff(c_435, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k4_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_403])).
% 26.22/15.81  tff(c_443, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_435])).
% 26.22/15.81  tff(c_11974, plain, (![C_215, B_216]: (k3_xboole_0(C_215, k4_xboole_0(B_216, C_215))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11692, c_122])).
% 26.22/15.81  tff(c_406, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k3_xboole_0(A_55, k4_xboole_0(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_403, c_22])).
% 26.22/15.81  tff(c_8156, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(demodulation, [status(thm), theory('equality')], [c_1515, c_406])).
% 26.22/15.81  tff(c_11991, plain, (![C_215, B_216]: (k4_xboole_0(C_215, k4_xboole_0(B_216, C_215))=k4_xboole_0(C_215, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11974, c_8156])).
% 26.22/15.82  tff(c_12093, plain, (![C_215, B_216]: (k4_xboole_0(C_215, k4_xboole_0(B_216, C_215))=C_215)), inference(demodulation, [status(thm), theory('equality')], [c_443, c_11991])).
% 26.22/15.82  tff(c_46750, plain, (![B_457, A_458]: (k4_xboole_0(B_457, A_458)=B_457 | k3_xboole_0(A_458, B_457)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22701, c_12093])).
% 26.22/15.82  tff(c_135, plain, (![A_40]: (k2_xboole_0(k1_xboole_0, A_40)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_101, c_4])).
% 26.22/15.82  tff(c_13974, plain, (![C_237, A_238, B_239]: (k2_xboole_0(C_237, k4_xboole_0(A_238, k2_xboole_0(B_239, C_237)))=k2_xboole_0(C_237, k4_xboole_0(A_238, B_239)))), inference(superposition, [status(thm), theory('equality')], [c_1340, c_16])).
% 26.22/15.82  tff(c_14321, plain, (![C_237, B_239]: (k2_xboole_0(C_237, k4_xboole_0(k2_xboole_0(B_239, C_237), B_239))=k2_xboole_0(C_237, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_13974])).
% 26.22/15.82  tff(c_23857, plain, (![C_331, B_332]: (k2_xboole_0(C_331, k4_xboole_0(k2_xboole_0(B_332, C_331), B_332))=C_331)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14321])).
% 26.22/15.82  tff(c_1022, plain, (![A_73, B_74, C_75]: (k2_xboole_0(k2_xboole_0(A_73, B_74), C_75)=k2_xboole_0(A_73, k2_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 26.22/15.82  tff(c_3534, plain, (![A_124, A_122, B_123]: (k2_xboole_0(A_124, k2_xboole_0(A_122, B_123))=k2_xboole_0(A_122, k2_xboole_0(B_123, A_124)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1022])).
% 26.22/15.82  tff(c_4007, plain, (![A_40, A_124]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_40, A_124))=k2_xboole_0(A_124, A_40))), inference(superposition, [status(thm), theory('equality')], [c_135, c_3534])).
% 26.22/15.82  tff(c_24009, plain, (![B_332, C_331]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_332, C_331), B_332), C_331)=k2_xboole_0(k1_xboole_0, C_331))), inference(superposition, [status(thm), theory('equality')], [c_23857, c_4007])).
% 26.22/15.82  tff(c_27181, plain, (![B_352, C_353]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_352, C_353), B_352), C_353)=C_353)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_24009])).
% 26.22/15.82  tff(c_27647, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(A_1, B_2), B_2), A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_27181])).
% 26.22/15.82  tff(c_46771, plain, (![A_1, A_458]: (k2_xboole_0(k2_xboole_0(A_1, A_458), A_1)=A_1 | k3_xboole_0(A_458, k2_xboole_0(A_1, A_458))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46750, c_27647])).
% 26.22/15.82  tff(c_47437, plain, (![A_459, A_460]: (k2_xboole_0(A_459, A_460)=A_459 | k1_xboole_0!=A_460)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_797, c_2, c_46771])).
% 26.22/15.82  tff(c_48197, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_47437])).
% 26.22/15.82  tff(c_14300, plain, (![A_40, B_39]: (k2_xboole_0(A_40, k4_xboole_0(A_40, B_39))=k2_xboole_0(A_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_122, c_13974])).
% 26.22/15.82  tff(c_14415, plain, (![A_240, B_241]: (k2_xboole_0(A_240, k4_xboole_0(A_240, B_241))=A_240)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14300])).
% 26.22/15.82  tff(c_14542, plain, (![A_240, B_241]: (k2_xboole_0(k4_xboole_0(A_240, B_241), A_240)=k2_xboole_0(k1_xboole_0, A_240))), inference(superposition, [status(thm), theory('equality')], [c_14415, c_4007])).
% 26.22/15.82  tff(c_14758, plain, (![A_240, B_241]: (k2_xboole_0(k4_xboole_0(A_240, B_241), A_240)=A_240)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_14542])).
% 26.22/15.82  tff(c_49640, plain, (![A_467, B_468]: (k4_xboole_0(A_467, B_468)=A_467 | k1_xboole_0!=A_467)), inference(superposition, [status(thm), theory('equality')], [c_47437, c_14758])).
% 26.22/15.82  tff(c_1487, plain, (![A_85, B_86]: (k3_xboole_0(A_85, k4_xboole_0(B_86, k3_xboole_0(A_85, B_86)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1447, c_60])).
% 26.22/15.82  tff(c_53336, plain, (![A_85]: (k3_xboole_0(A_85, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49640, c_1487])).
% 26.22/15.82  tff(c_14706, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k3_xboole_0(A_18, B_19))=A_18)), inference(superposition, [status(thm), theory('equality')], [c_22, c_14415])).
% 26.22/15.82  tff(c_11780, plain, (![C_214, B_213]: (k3_xboole_0(C_214, k4_xboole_0(B_213, C_214))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11692, c_122])).
% 26.22/15.82  tff(c_30454, plain, (![B_374, A_375]: (k3_xboole_0(B_374, A_375)=k1_xboole_0 | k3_xboole_0(A_375, B_374)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22701, c_11780])).
% 26.22/15.82  tff(c_35692, plain, (![B_403, A_404]: (k3_xboole_0(k4_xboole_0(B_403, k3_xboole_0(A_404, B_403)), A_404)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1487, c_30454])).
% 26.22/15.82  tff(c_14406, plain, (![A_40, B_39]: (k2_xboole_0(A_40, k4_xboole_0(A_40, B_39))=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14300])).
% 26.22/15.82  tff(c_513, plain, (![A_18, B_19]: (k2_xboole_0(k4_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(k4_xboole_0(A_18, B_19), A_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_479])).
% 26.22/15.82  tff(c_537, plain, (![A_18, B_19]: (k2_xboole_0(k4_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, k4_xboole_0(A_18, B_19)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_513])).
% 26.22/15.82  tff(c_14413, plain, (![A_18, B_19]: (k2_xboole_0(k4_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_14406, c_537])).
% 26.22/15.82  tff(c_35751, plain, (![B_403, A_404]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(B_403, k3_xboole_0(A_404, B_403)), A_404), k1_xboole_0)=k4_xboole_0(B_403, k3_xboole_0(A_404, B_403)))), inference(superposition, [status(thm), theory('equality')], [c_35692, c_14413])).
% 26.22/15.82  tff(c_66504, plain, (![B_553, A_554]: (k4_xboole_0(B_553, k3_xboole_0(A_554, B_553))=k4_xboole_0(B_553, A_554))), inference(demodulation, [status(thm), theory('equality')], [c_14706, c_2, c_4, c_18, c_35751])).
% 26.22/15.82  tff(c_66717, plain, (![B_553, A_554]: (k4_xboole_0(B_553, k4_xboole_0(B_553, A_554))=k3_xboole_0(B_553, k3_xboole_0(A_554, B_553)))), inference(superposition, [status(thm), theory('equality')], [c_66504, c_22])).
% 26.22/15.82  tff(c_66922, plain, (![B_553, A_554]: (k3_xboole_0(B_553, k3_xboole_0(A_554, B_553))=k3_xboole_0(B_553, A_554))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_66717])).
% 26.22/15.82  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 26.22/15.82  tff(c_15325, plain, (![C_248, A_249, B_250]: (k2_xboole_0(C_248, k3_xboole_0(A_249, k4_xboole_0(B_250, C_248)))=k2_xboole_0(C_248, k3_xboole_0(A_249, B_250)))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_16])).
% 26.22/15.82  tff(c_15645, plain, (![A_3, A_249]: (k2_xboole_0(A_3, k3_xboole_0(A_249, k1_xboole_0))=k2_xboole_0(A_3, k3_xboole_0(A_249, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_15325])).
% 26.22/15.82  tff(c_15726, plain, (![A_3, A_249]: (k2_xboole_0(A_3, k3_xboole_0(A_249, A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8, c_15645])).
% 26.22/15.82  tff(c_4138, plain, (![A_125, A_126]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_125, A_126))=k2_xboole_0(A_126, A_125))), inference(superposition, [status(thm), theory('equality')], [c_135, c_3534])).
% 26.22/15.82  tff(c_4335, plain, (![B_12, A_11]: (k2_xboole_0(k4_xboole_0(B_12, A_11), A_11)=k2_xboole_0(k1_xboole_0, k2_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4138])).
% 26.22/15.82  tff(c_4405, plain, (![B_12, A_11]: (k2_xboole_0(k4_xboole_0(B_12, A_11), A_11)=k2_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_4335])).
% 26.22/15.82  tff(c_66693, plain, (![B_553, A_554]: (k2_xboole_0(k4_xboole_0(B_553, A_554), k3_xboole_0(A_554, B_553))=k2_xboole_0(k3_xboole_0(A_554, B_553), B_553))), inference(superposition, [status(thm), theory('equality')], [c_66504, c_4405])).
% 26.22/15.82  tff(c_82676, plain, (![B_632, A_633]: (k2_xboole_0(k4_xboole_0(B_632, A_633), k3_xboole_0(A_633, B_632))=B_632)), inference(demodulation, [status(thm), theory('equality')], [c_15726, c_2, c_66693])).
% 26.22/15.82  tff(c_83097, plain, (![A_554, B_553]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_554, B_553), B_553), k3_xboole_0(B_553, A_554))=k3_xboole_0(A_554, B_553))), inference(superposition, [status(thm), theory('equality')], [c_66922, c_82676])).
% 26.22/15.82  tff(c_83467, plain, (![B_553, A_554]: (k3_xboole_0(B_553, A_554)=k3_xboole_0(A_554, B_553))), inference(demodulation, [status(thm), theory('equality')], [c_48197, c_53336, c_60, c_24, c_83097])).
% 26.22/15.82  tff(c_30, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 26.22/15.82  tff(c_31, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 26.22/15.82  tff(c_83528, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83467, c_31])).
% 26.22/15.82  tff(c_108967, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108965, c_83528])).
% 26.22/15.82  tff(c_108980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1515, c_2, c_18, c_108967])).
% 26.22/15.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.22/15.82  
% 26.22/15.82  Inference rules
% 26.22/15.82  ----------------------
% 26.22/15.82  #Ref     : 4
% 26.22/15.82  #Sup     : 28236
% 26.22/15.82  #Fact    : 0
% 26.22/15.82  #Define  : 0
% 26.22/15.82  #Split   : 9
% 26.22/15.82  #Chain   : 0
% 26.22/15.82  #Close   : 0
% 26.22/15.82  
% 26.22/15.82  Ordering : KBO
% 26.22/15.82  
% 26.22/15.82  Simplification rules
% 26.22/15.82  ----------------------
% 26.22/15.82  #Subsume      : 2996
% 26.22/15.82  #Demod        : 27429
% 26.22/15.82  #Tautology    : 16023
% 26.22/15.82  #SimpNegUnit  : 0
% 26.22/15.82  #BackRed      : 42
% 26.22/15.82  
% 26.22/15.82  #Partial instantiations: 0
% 26.22/15.82  #Strategies tried      : 1
% 26.22/15.82  
% 26.22/15.82  Timing (in seconds)
% 26.22/15.82  ----------------------
% 26.22/15.82  Preprocessing        : 0.29
% 26.22/15.82  Parsing              : 0.16
% 26.22/15.82  CNF conversion       : 0.02
% 26.22/15.82  Main loop            : 14.71
% 26.22/15.82  Inferencing          : 1.62
% 26.22/15.82  Reduction            : 9.88
% 26.22/15.82  Demodulation         : 9.16
% 26.22/15.82  BG Simplification    : 0.23
% 26.22/15.82  Subsumption          : 2.37
% 26.22/15.82  Abstraction          : 0.41
% 26.22/15.82  MUC search           : 0.00
% 26.22/15.82  Cooper               : 0.00
% 26.22/15.83  Total                : 15.07
% 26.22/15.83  Index Insertion      : 0.00
% 26.22/15.83  Index Deletion       : 0.00
% 26.22/15.83  Index Matching       : 0.00
% 26.22/15.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
