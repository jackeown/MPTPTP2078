%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:49 EST 2020

% Result     : Theorem 18.60s
% Output     : CNFRefutation 18.64s
% Verified   : 
% Statistics : Number of formulae       :  107 (1366 expanded)
%              Number of leaves         :   27 ( 485 expanded)
%              Depth                    :   26
%              Number of atoms          :  101 (1532 expanded)
%              Number of equality atoms :   83 (1160 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [C_23,A_21,B_22] :
      ( k4_xboole_0(C_23,k2_tarski(A_21,B_22)) = C_23
      | r2_hidden(B_22,C_23)
      | r2_hidden(A_21,C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    ! [B_33,A_34] : k2_xboole_0(B_33,A_34) = k2_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [A_34] : k2_xboole_0(k1_xboole_0,A_34) = A_34 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_27,B_28] : r1_tarski(k4_xboole_0(A_27,B_28),A_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [B_28] : k4_xboole_0(k1_xboole_0,B_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_12])).

tff(c_236,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k4_xboole_0(B_41,A_40)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_252,plain,(
    ! [B_28] : k5_xboole_0(B_28,k1_xboole_0) = k2_xboole_0(B_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_236])).

tff(c_256,plain,(
    ! [B_28] : k5_xboole_0(B_28,k1_xboole_0) = B_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_252])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_334,plain,(
    ! [A_48,B_49] : k5_xboole_0(k5_xboole_0(A_48,B_49),k2_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_367,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,k1_xboole_0),A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_334])).

tff(c_374,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8,c_367])).

tff(c_375,plain,(
    ! [A_50] : k5_xboole_0(A_50,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8,c_367])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),k5_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_400,plain,(
    ! [A_51] : r1_tarski(k4_xboole_0(A_51,A_51),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_16])).

tff(c_446,plain,(
    ! [A_55] : k4_xboole_0(A_55,A_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_400,c_12])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_455,plain,(
    ! [A_55] : k5_xboole_0(A_55,k1_xboole_0) = k2_xboole_0(A_55,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_18])).

tff(c_475,plain,(
    ! [A_55] : k2_xboole_0(A_55,A_55) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_455])).

tff(c_616,plain,(
    ! [A_60,B_61,C_62] : k2_xboole_0(k4_xboole_0(A_60,k2_xboole_0(B_61,C_62)),k4_xboole_0(B_61,k2_xboole_0(A_60,C_62))) = k4_xboole_0(k5_xboole_0(A_60,B_61),C_62) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_663,plain,(
    ! [A_60,C_62] : k4_xboole_0(k5_xboole_0(A_60,A_60),C_62) = k4_xboole_0(A_60,k2_xboole_0(A_60,C_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_616])).

tff(c_727,plain,(
    ! [A_63,C_64] : k4_xboole_0(A_63,k2_xboole_0(A_63,C_64)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_374,c_663])).

tff(c_761,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_727])).

tff(c_69,plain,(
    ! [A_30,B_31] : k3_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_69])).

tff(c_481,plain,(
    ! [A_56] : k2_xboole_0(A_56,A_56) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_455])).

tff(c_14,plain,(
    ! [A_10,B_11] : k5_xboole_0(k5_xboole_0(A_10,B_11),k2_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_487,plain,(
    ! [A_56] : k5_xboole_0(k5_xboole_0(A_56,A_56),A_56) = k3_xboole_0(A_56,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_14])).

tff(c_522,plain,(
    ! [A_57] : k5_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_78,c_487])).

tff(c_540,plain,(
    ! [B_15] : k4_xboole_0(B_15,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_18])).

tff(c_563,plain,(
    ! [B_15] : k4_xboole_0(B_15,k1_xboole_0) = B_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_540])).

tff(c_5081,plain,(
    ! [B_140,A_141,C_142] : k2_xboole_0(k4_xboole_0(B_140,k2_xboole_0(A_141,C_142)),k4_xboole_0(A_141,k2_xboole_0(B_140,C_142))) = k4_xboole_0(k5_xboole_0(A_141,B_140),C_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_2])).

tff(c_5467,plain,(
    ! [A_3,A_141] : k2_xboole_0(k4_xboole_0(A_3,k2_xboole_0(A_141,k1_xboole_0)),k4_xboole_0(A_141,A_3)) = k4_xboole_0(k5_xboole_0(A_141,A_3),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5081])).

tff(c_28031,plain,(
    ! [A_307,A_308] : k2_xboole_0(k4_xboole_0(A_307,A_308),k4_xboole_0(A_308,A_307)) = k5_xboole_0(A_308,A_307) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_4,c_5467])).

tff(c_28361,plain,(
    ! [B_2,A_1] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_2,A_1),A_1),k1_xboole_0) = k5_xboole_0(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_28031])).

tff(c_28475,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k4_xboole_0(k2_xboole_0(B_2,A_1),A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28361])).

tff(c_738,plain,(
    ! [A_63,C_64] : k5_xboole_0(k2_xboole_0(A_63,C_64),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_63,C_64),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_18])).

tff(c_852,plain,(
    ! [A_67,C_68] : k2_xboole_0(k2_xboole_0(A_67,C_68),A_67) = k2_xboole_0(A_67,C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_738])).

tff(c_879,plain,(
    ! [A_67,C_68] : k2_xboole_0(A_67,k2_xboole_0(A_67,C_68)) = k2_xboole_0(A_67,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_2])).

tff(c_1090,plain,(
    ! [A_73,B_74] : k2_xboole_0(k2_xboole_0(A_73,B_74),B_74) = k2_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_852])).

tff(c_713,plain,(
    ! [A_60,C_62] : k4_xboole_0(A_60,k2_xboole_0(A_60,C_62)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_374,c_663])).

tff(c_2393,plain,(
    ! [A_97,B_98] : k4_xboole_0(k2_xboole_0(A_97,B_98),k2_xboole_0(B_98,A_97)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_713])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k4_xboole_0(A_16,k2_xboole_0(B_17,C_18)),k4_xboole_0(B_17,k2_xboole_0(A_16,C_18))) = k4_xboole_0(k5_xboole_0(A_16,B_17),C_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2407,plain,(
    ! [B_98,A_97] : k2_xboole_0(k4_xboole_0(B_98,k2_xboole_0(k2_xboole_0(A_97,B_98),A_97)),k1_xboole_0) = k4_xboole_0(k5_xboole_0(B_98,k2_xboole_0(A_97,B_98)),A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_2393,c_20])).

tff(c_2519,plain,(
    ! [B_98,A_97] : k4_xboole_0(k5_xboole_0(B_98,k2_xboole_0(A_97,B_98)),A_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_879,c_2,c_4,c_2407])).

tff(c_34408,plain,(
    ! [A_340,B_341] : k4_xboole_0(k4_xboole_0(k2_xboole_0(A_340,B_341),B_341),A_340) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28475,c_2519])).

tff(c_35289,plain,(
    ! [B_344,A_345] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_344,A_345),B_344),A_345) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_34408])).

tff(c_784,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k2_xboole_0(B_66,A_65)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_727])).

tff(c_792,plain,(
    ! [B_66,A_65] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_66,k2_xboole_0(A_65,A_65))) = k4_xboole_0(k5_xboole_0(A_65,B_66),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_20])).

tff(c_1612,plain,(
    ! [A_83,B_84] : k4_xboole_0(k5_xboole_0(A_83,B_84),A_83) = k4_xboole_0(B_84,A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_122,c_792])).

tff(c_1641,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k4_xboole_0(B_84,A_83)) = k2_xboole_0(A_83,k5_xboole_0(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1612,c_18])).

tff(c_2012,plain,(
    ! [A_91,B_92] : k2_xboole_0(A_91,k5_xboole_0(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1641])).

tff(c_2091,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2012])).

tff(c_3956,plain,(
    ! [A_124,B_125] : k2_xboole_0(A_124,k4_xboole_0(B_125,A_124)) = k2_xboole_0(A_124,B_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_2091])).

tff(c_798,plain,(
    ! [B_66,A_65] : k5_xboole_0(k2_xboole_0(B_66,A_65),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_66,A_65),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_18])).

tff(c_1464,plain,(
    ! [B_81,A_82] : k2_xboole_0(k2_xboole_0(B_81,A_82),A_82) = k2_xboole_0(B_81,A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_798])).

tff(c_1842,plain,(
    ! [A_89,B_90] : k2_xboole_0(k2_xboole_0(A_89,B_90),A_89) = k2_xboole_0(B_90,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1464])).

tff(c_1972,plain,(
    ! [A_1,B_90] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_90)) = k2_xboole_0(B_90,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1842])).

tff(c_3971,plain,(
    ! [B_125,A_124] : k2_xboole_0(k4_xboole_0(B_125,A_124),A_124) = k2_xboole_0(A_124,k2_xboole_0(A_124,B_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3956,c_1972])).

tff(c_4087,plain,(
    ! [B_125,A_124] : k2_xboole_0(k4_xboole_0(B_125,A_124),A_124) = k2_xboole_0(A_124,B_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_3971])).

tff(c_35430,plain,(
    ! [A_345,B_344] : k2_xboole_0(A_345,k4_xboole_0(k2_xboole_0(B_344,A_345),B_344)) = k2_xboole_0(k1_xboole_0,A_345) ),
    inference(superposition,[status(thm),theory(equality)],[c_35289,c_4087])).

tff(c_35696,plain,(
    ! [A_345,B_344] : k2_xboole_0(A_345,k4_xboole_0(k2_xboole_0(B_344,A_345),B_344)) = A_345 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_35430])).

tff(c_28367,plain,(
    ! [A_60,C_62] : k2_xboole_0(k4_xboole_0(k2_xboole_0(A_60,C_62),A_60),k1_xboole_0) = k5_xboole_0(A_60,k2_xboole_0(A_60,C_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_28031])).

tff(c_39668,plain,(
    ! [A_362,C_363] : k5_xboole_0(A_362,k2_xboole_0(A_362,C_363)) = k4_xboole_0(k2_xboole_0(A_362,C_363),A_362) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28367])).

tff(c_795,plain,(
    ! [B_66,A_65] : k2_xboole_0(k4_xboole_0(B_66,k2_xboole_0(A_65,A_65)),k1_xboole_0) = k4_xboole_0(k5_xboole_0(B_66,A_65),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_20])).

tff(c_837,plain,(
    ! [B_66,A_65] : k4_xboole_0(k5_xboole_0(B_66,A_65),A_65) = k4_xboole_0(B_66,A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_4,c_795])).

tff(c_39829,plain,(
    ! [A_362,C_363] : k4_xboole_0(k4_xboole_0(k2_xboole_0(A_362,C_363),A_362),k2_xboole_0(A_362,C_363)) = k4_xboole_0(A_362,k2_xboole_0(A_362,C_363)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39668,c_837])).

tff(c_54139,plain,(
    ! [A_416,C_417] : k4_xboole_0(k4_xboole_0(k2_xboole_0(A_416,C_417),A_416),k2_xboole_0(A_416,C_417)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_39829])).

tff(c_5450,plain,(
    ! [B_2,A_141,A_1] : k2_xboole_0(k4_xboole_0(B_2,k2_xboole_0(A_141,A_1)),k4_xboole_0(A_141,k2_xboole_0(A_1,B_2))) = k4_xboole_0(k5_xboole_0(A_141,B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5081])).

tff(c_54189,plain,(
    ! [A_416,C_417] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_416,k2_xboole_0(C_417,k4_xboole_0(k2_xboole_0(A_416,C_417),A_416)))) = k4_xboole_0(k5_xboole_0(A_416,k4_xboole_0(k2_xboole_0(A_416,C_417),A_416)),C_417) ),
    inference(superposition,[status(thm),theory(equality)],[c_54139,c_5450])).

tff(c_54732,plain,(
    ! [A_416,C_417] : k4_xboole_0(k2_xboole_0(A_416,C_417),C_417) = k4_xboole_0(A_416,C_417) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35696,c_879,c_18,c_122,c_54189])).

tff(c_26,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54906,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54732,c_26])).

tff(c_55975,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_54906])).

tff(c_55979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_55975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.60/10.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.64/10.98  
% 18.64/10.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.64/10.98  %$ r2_hidden > r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 18.64/10.98  
% 18.64/10.98  %Foreground sorts:
% 18.64/10.98  
% 18.64/10.98  
% 18.64/10.98  %Background operators:
% 18.64/10.98  
% 18.64/10.98  
% 18.64/10.98  %Foreground operators:
% 18.64/10.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.64/10.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.64/10.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.64/10.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.64/10.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.64/10.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.64/10.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.64/10.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.64/10.98  tff('#skF_2', type, '#skF_2': $i).
% 18.64/10.98  tff('#skF_3', type, '#skF_3': $i).
% 18.64/10.98  tff('#skF_1', type, '#skF_1': $i).
% 18.64/10.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.64/10.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.64/10.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.64/10.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.64/10.98  
% 18.64/11.00  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 18.64/11.00  tff(f_59, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 18.64/11.00  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 18.64/11.00  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 18.64/11.00  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 18.64/11.00  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 18.64/11.00  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 18.64/11.00  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 18.64/11.00  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 18.64/11.00  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 18.64/11.00  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_xboole_1)).
% 18.64/11.00  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 18.64/11.00  tff(c_30, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.64/11.00  tff(c_28, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.64/11.00  tff(c_24, plain, (![C_23, A_21, B_22]: (k4_xboole_0(C_23, k2_tarski(A_21, B_22))=C_23 | r2_hidden(B_22, C_23) | r2_hidden(A_21, C_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.64/11.00  tff(c_100, plain, (![B_33, A_34]: (k2_xboole_0(B_33, A_34)=k2_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.64/11.00  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.64/11.00  tff(c_122, plain, (![A_34]: (k2_xboole_0(k1_xboole_0, A_34)=A_34)), inference(superposition, [status(thm), theory('equality')], [c_100, c_4])).
% 18.64/11.00  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.64/11.00  tff(c_48, plain, (![A_27, B_28]: (r1_tarski(k4_xboole_0(A_27, B_28), A_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.64/11.00  tff(c_12, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.64/11.00  tff(c_53, plain, (![B_28]: (k4_xboole_0(k1_xboole_0, B_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_12])).
% 18.64/11.00  tff(c_236, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k4_xboole_0(B_41, A_40))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.64/11.00  tff(c_252, plain, (![B_28]: (k5_xboole_0(B_28, k1_xboole_0)=k2_xboole_0(B_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_53, c_236])).
% 18.64/11.00  tff(c_256, plain, (![B_28]: (k5_xboole_0(B_28, k1_xboole_0)=B_28)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_252])).
% 18.64/11.00  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.64/11.00  tff(c_334, plain, (![A_48, B_49]: (k5_xboole_0(k5_xboole_0(A_48, B_49), k2_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.64/11.00  tff(c_367, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, k1_xboole_0), A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_334])).
% 18.64/11.00  tff(c_374, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_8, c_367])).
% 18.64/11.00  tff(c_375, plain, (![A_50]: (k5_xboole_0(A_50, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_8, c_367])).
% 18.64/11.00  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), k5_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.64/11.00  tff(c_400, plain, (![A_51]: (r1_tarski(k4_xboole_0(A_51, A_51), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_375, c_16])).
% 18.64/11.00  tff(c_446, plain, (![A_55]: (k4_xboole_0(A_55, A_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_400, c_12])).
% 18.64/11.00  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.64/11.00  tff(c_455, plain, (![A_55]: (k5_xboole_0(A_55, k1_xboole_0)=k2_xboole_0(A_55, A_55))), inference(superposition, [status(thm), theory('equality')], [c_446, c_18])).
% 18.64/11.00  tff(c_475, plain, (![A_55]: (k2_xboole_0(A_55, A_55)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_455])).
% 18.64/11.00  tff(c_616, plain, (![A_60, B_61, C_62]: (k2_xboole_0(k4_xboole_0(A_60, k2_xboole_0(B_61, C_62)), k4_xboole_0(B_61, k2_xboole_0(A_60, C_62)))=k4_xboole_0(k5_xboole_0(A_60, B_61), C_62))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.64/11.00  tff(c_663, plain, (![A_60, C_62]: (k4_xboole_0(k5_xboole_0(A_60, A_60), C_62)=k4_xboole_0(A_60, k2_xboole_0(A_60, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_475, c_616])).
% 18.64/11.00  tff(c_727, plain, (![A_63, C_64]: (k4_xboole_0(A_63, k2_xboole_0(A_63, C_64))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_374, c_663])).
% 18.64/11.00  tff(c_761, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_727])).
% 18.64/11.00  tff(c_69, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k2_xboole_0(A_30, B_31))=A_30)), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.64/11.00  tff(c_78, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_69])).
% 18.64/11.00  tff(c_481, plain, (![A_56]: (k2_xboole_0(A_56, A_56)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_455])).
% 18.64/11.00  tff(c_14, plain, (![A_10, B_11]: (k5_xboole_0(k5_xboole_0(A_10, B_11), k2_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.64/11.00  tff(c_487, plain, (![A_56]: (k5_xboole_0(k5_xboole_0(A_56, A_56), A_56)=k3_xboole_0(A_56, A_56))), inference(superposition, [status(thm), theory('equality')], [c_481, c_14])).
% 18.64/11.00  tff(c_522, plain, (![A_57]: (k5_xboole_0(k1_xboole_0, A_57)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_374, c_78, c_487])).
% 18.64/11.00  tff(c_540, plain, (![B_15]: (k4_xboole_0(B_15, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_15))), inference(superposition, [status(thm), theory('equality')], [c_522, c_18])).
% 18.64/11.00  tff(c_563, plain, (![B_15]: (k4_xboole_0(B_15, k1_xboole_0)=B_15)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_540])).
% 18.64/11.00  tff(c_5081, plain, (![B_140, A_141, C_142]: (k2_xboole_0(k4_xboole_0(B_140, k2_xboole_0(A_141, C_142)), k4_xboole_0(A_141, k2_xboole_0(B_140, C_142)))=k4_xboole_0(k5_xboole_0(A_141, B_140), C_142))), inference(superposition, [status(thm), theory('equality')], [c_616, c_2])).
% 18.64/11.00  tff(c_5467, plain, (![A_3, A_141]: (k2_xboole_0(k4_xboole_0(A_3, k2_xboole_0(A_141, k1_xboole_0)), k4_xboole_0(A_141, A_3))=k4_xboole_0(k5_xboole_0(A_141, A_3), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5081])).
% 18.64/11.00  tff(c_28031, plain, (![A_307, A_308]: (k2_xboole_0(k4_xboole_0(A_307, A_308), k4_xboole_0(A_308, A_307))=k5_xboole_0(A_308, A_307))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_4, c_5467])).
% 18.64/11.00  tff(c_28361, plain, (![B_2, A_1]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_2, A_1), A_1), k1_xboole_0)=k5_xboole_0(A_1, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_761, c_28031])).
% 18.64/11.00  tff(c_28475, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k4_xboole_0(k2_xboole_0(B_2, A_1), A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28361])).
% 18.64/11.00  tff(c_738, plain, (![A_63, C_64]: (k5_xboole_0(k2_xboole_0(A_63, C_64), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_63, C_64), A_63))), inference(superposition, [status(thm), theory('equality')], [c_727, c_18])).
% 18.64/11.00  tff(c_852, plain, (![A_67, C_68]: (k2_xboole_0(k2_xboole_0(A_67, C_68), A_67)=k2_xboole_0(A_67, C_68))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_738])).
% 18.64/11.00  tff(c_879, plain, (![A_67, C_68]: (k2_xboole_0(A_67, k2_xboole_0(A_67, C_68))=k2_xboole_0(A_67, C_68))), inference(superposition, [status(thm), theory('equality')], [c_852, c_2])).
% 18.64/11.00  tff(c_1090, plain, (![A_73, B_74]: (k2_xboole_0(k2_xboole_0(A_73, B_74), B_74)=k2_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_2, c_852])).
% 18.64/11.00  tff(c_713, plain, (![A_60, C_62]: (k4_xboole_0(A_60, k2_xboole_0(A_60, C_62))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_374, c_663])).
% 18.64/11.00  tff(c_2393, plain, (![A_97, B_98]: (k4_xboole_0(k2_xboole_0(A_97, B_98), k2_xboole_0(B_98, A_97))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1090, c_713])).
% 18.64/11.00  tff(c_20, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k4_xboole_0(A_16, k2_xboole_0(B_17, C_18)), k4_xboole_0(B_17, k2_xboole_0(A_16, C_18)))=k4_xboole_0(k5_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.64/11.00  tff(c_2407, plain, (![B_98, A_97]: (k2_xboole_0(k4_xboole_0(B_98, k2_xboole_0(k2_xboole_0(A_97, B_98), A_97)), k1_xboole_0)=k4_xboole_0(k5_xboole_0(B_98, k2_xboole_0(A_97, B_98)), A_97))), inference(superposition, [status(thm), theory('equality')], [c_2393, c_20])).
% 18.64/11.00  tff(c_2519, plain, (![B_98, A_97]: (k4_xboole_0(k5_xboole_0(B_98, k2_xboole_0(A_97, B_98)), A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_761, c_879, c_2, c_4, c_2407])).
% 18.64/11.00  tff(c_34408, plain, (![A_340, B_341]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(A_340, B_341), B_341), A_340)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28475, c_2519])).
% 18.64/11.00  tff(c_35289, plain, (![B_344, A_345]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_344, A_345), B_344), A_345)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_34408])).
% 18.64/11.00  tff(c_784, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k2_xboole_0(B_66, A_65))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_727])).
% 18.64/11.00  tff(c_792, plain, (![B_66, A_65]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_66, k2_xboole_0(A_65, A_65)))=k4_xboole_0(k5_xboole_0(A_65, B_66), A_65))), inference(superposition, [status(thm), theory('equality')], [c_784, c_20])).
% 18.64/11.00  tff(c_1612, plain, (![A_83, B_84]: (k4_xboole_0(k5_xboole_0(A_83, B_84), A_83)=k4_xboole_0(B_84, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_122, c_792])).
% 18.64/11.00  tff(c_1641, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k4_xboole_0(B_84, A_83))=k2_xboole_0(A_83, k5_xboole_0(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_1612, c_18])).
% 18.64/11.00  tff(c_2012, plain, (![A_91, B_92]: (k2_xboole_0(A_91, k5_xboole_0(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1641])).
% 18.64/11.00  tff(c_2091, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, k2_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2012])).
% 18.64/11.00  tff(c_3956, plain, (![A_124, B_125]: (k2_xboole_0(A_124, k4_xboole_0(B_125, A_124))=k2_xboole_0(A_124, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_879, c_2091])).
% 18.64/11.00  tff(c_798, plain, (![B_66, A_65]: (k5_xboole_0(k2_xboole_0(B_66, A_65), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_66, A_65), A_65))), inference(superposition, [status(thm), theory('equality')], [c_784, c_18])).
% 18.64/11.00  tff(c_1464, plain, (![B_81, A_82]: (k2_xboole_0(k2_xboole_0(B_81, A_82), A_82)=k2_xboole_0(B_81, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_798])).
% 18.64/11.00  tff(c_1842, plain, (![A_89, B_90]: (k2_xboole_0(k2_xboole_0(A_89, B_90), A_89)=k2_xboole_0(B_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1464])).
% 18.64/11.00  tff(c_1972, plain, (![A_1, B_90]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_90))=k2_xboole_0(B_90, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1842])).
% 18.64/11.00  tff(c_3971, plain, (![B_125, A_124]: (k2_xboole_0(k4_xboole_0(B_125, A_124), A_124)=k2_xboole_0(A_124, k2_xboole_0(A_124, B_125)))), inference(superposition, [status(thm), theory('equality')], [c_3956, c_1972])).
% 18.64/11.00  tff(c_4087, plain, (![B_125, A_124]: (k2_xboole_0(k4_xboole_0(B_125, A_124), A_124)=k2_xboole_0(A_124, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_879, c_3971])).
% 18.64/11.00  tff(c_35430, plain, (![A_345, B_344]: (k2_xboole_0(A_345, k4_xboole_0(k2_xboole_0(B_344, A_345), B_344))=k2_xboole_0(k1_xboole_0, A_345))), inference(superposition, [status(thm), theory('equality')], [c_35289, c_4087])).
% 18.64/11.00  tff(c_35696, plain, (![A_345, B_344]: (k2_xboole_0(A_345, k4_xboole_0(k2_xboole_0(B_344, A_345), B_344))=A_345)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_35430])).
% 18.64/11.00  tff(c_28367, plain, (![A_60, C_62]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(A_60, C_62), A_60), k1_xboole_0)=k5_xboole_0(A_60, k2_xboole_0(A_60, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_713, c_28031])).
% 18.64/11.00  tff(c_39668, plain, (![A_362, C_363]: (k5_xboole_0(A_362, k2_xboole_0(A_362, C_363))=k4_xboole_0(k2_xboole_0(A_362, C_363), A_362))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28367])).
% 18.64/11.00  tff(c_795, plain, (![B_66, A_65]: (k2_xboole_0(k4_xboole_0(B_66, k2_xboole_0(A_65, A_65)), k1_xboole_0)=k4_xboole_0(k5_xboole_0(B_66, A_65), A_65))), inference(superposition, [status(thm), theory('equality')], [c_784, c_20])).
% 18.64/11.00  tff(c_837, plain, (![B_66, A_65]: (k4_xboole_0(k5_xboole_0(B_66, A_65), A_65)=k4_xboole_0(B_66, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_4, c_795])).
% 18.64/11.00  tff(c_39829, plain, (![A_362, C_363]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(A_362, C_363), A_362), k2_xboole_0(A_362, C_363))=k4_xboole_0(A_362, k2_xboole_0(A_362, C_363)))), inference(superposition, [status(thm), theory('equality')], [c_39668, c_837])).
% 18.64/11.00  tff(c_54139, plain, (![A_416, C_417]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(A_416, C_417), A_416), k2_xboole_0(A_416, C_417))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_713, c_39829])).
% 18.64/11.00  tff(c_5450, plain, (![B_2, A_141, A_1]: (k2_xboole_0(k4_xboole_0(B_2, k2_xboole_0(A_141, A_1)), k4_xboole_0(A_141, k2_xboole_0(A_1, B_2)))=k4_xboole_0(k5_xboole_0(A_141, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5081])).
% 18.64/11.00  tff(c_54189, plain, (![A_416, C_417]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_416, k2_xboole_0(C_417, k4_xboole_0(k2_xboole_0(A_416, C_417), A_416))))=k4_xboole_0(k5_xboole_0(A_416, k4_xboole_0(k2_xboole_0(A_416, C_417), A_416)), C_417))), inference(superposition, [status(thm), theory('equality')], [c_54139, c_5450])).
% 18.64/11.00  tff(c_54732, plain, (![A_416, C_417]: (k4_xboole_0(k2_xboole_0(A_416, C_417), C_417)=k4_xboole_0(A_416, C_417))), inference(demodulation, [status(thm), theory('equality')], [c_35696, c_879, c_18, c_122, c_54189])).
% 18.64/11.00  tff(c_26, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.64/11.00  tff(c_54906, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54732, c_26])).
% 18.64/11.00  tff(c_55975, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_54906])).
% 18.64/11.00  tff(c_55979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_55975])).
% 18.64/11.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.64/11.00  
% 18.64/11.00  Inference rules
% 18.64/11.00  ----------------------
% 18.64/11.00  #Ref     : 0
% 18.64/11.00  #Sup     : 14358
% 18.64/11.00  #Fact    : 0
% 18.64/11.00  #Define  : 0
% 18.64/11.00  #Split   : 1
% 18.64/11.00  #Chain   : 0
% 18.64/11.00  #Close   : 0
% 18.64/11.00  
% 18.64/11.00  Ordering : KBO
% 18.64/11.00  
% 18.64/11.00  Simplification rules
% 18.64/11.00  ----------------------
% 18.64/11.00  #Subsume      : 141
% 18.64/11.00  #Demod        : 21162
% 18.64/11.00  #Tautology    : 7241
% 18.64/11.00  #SimpNegUnit  : 1
% 18.64/11.00  #BackRed      : 41
% 18.64/11.00  
% 18.64/11.00  #Partial instantiations: 0
% 18.64/11.00  #Strategies tried      : 1
% 18.64/11.00  
% 18.64/11.00  Timing (in seconds)
% 18.64/11.00  ----------------------
% 18.64/11.00  Preprocessing        : 0.31
% 18.64/11.00  Parsing              : 0.16
% 18.64/11.00  CNF conversion       : 0.02
% 18.64/11.00  Main loop            : 9.93
% 18.64/11.00  Inferencing          : 1.36
% 18.64/11.00  Reduction            : 6.81
% 18.64/11.00  Demodulation         : 6.37
% 18.64/11.00  BG Simplification    : 0.23
% 18.64/11.00  Subsumption          : 1.21
% 18.64/11.00  Abstraction          : 0.47
% 18.64/11.00  MUC search           : 0.00
% 18.64/11.00  Cooper               : 0.00
% 18.64/11.00  Total                : 10.28
% 18.64/11.00  Index Insertion      : 0.00
% 18.64/11.00  Index Deletion       : 0.00
% 18.64/11.00  Index Matching       : 0.00
% 18.64/11.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
