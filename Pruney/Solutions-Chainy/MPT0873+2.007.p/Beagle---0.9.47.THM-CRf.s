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
% DateTime   : Thu Dec  3 10:09:27 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 348 expanded)
%              Number of leaves         :   20 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :   92 ( 515 expanded)
%              Number of equality atoms :   88 ( 511 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
       => ( A = E
          & B = F
          & C = G
          & D = H ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(c_10,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_6,plain,(
    ! [A_9,B_10] : k1_mcart_1(k4_tarski(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [A_15,B_16,C_17,D_18] : k4_tarski(k3_mcart_1(A_15,B_16,C_17),D_18) = k4_mcart_1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_15,B_16,C_17,D_18] : k1_mcart_1(k4_mcart_1(A_15,B_16,C_17,D_18)) = k3_mcart_1(A_15,B_16,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_116,plain,(
    ! [A_28,B_29,C_30,D_31] : k4_tarski(k4_tarski(k4_tarski(A_28,B_29),C_30),D_31) = k4_mcart_1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [A_28,B_29,C_30,D_31] : k4_tarski(k4_tarski(A_28,B_29),C_30) = k1_mcart_1(k4_mcart_1(A_28,B_29,C_30,D_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6])).

tff(c_150,plain,(
    ! [A_32,B_33,C_34] : k4_tarski(k4_tarski(A_32,B_33),C_34) = k3_mcart_1(A_32,B_33,C_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128])).

tff(c_159,plain,(
    ! [A_32,B_33,C_34] : k1_mcart_1(k3_mcart_1(A_32,B_33,C_34)) = k4_tarski(A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_6])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_mcart_1(k4_tarski(A_9,B_10)) = B_10 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_162,plain,(
    ! [A_32,B_33,C_34] : k2_mcart_1(k3_mcart_1(A_32,B_33,C_34)) = C_34 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_8])).

tff(c_45,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_mcart_1(k4_mcart_1(A_15,B_16,C_17,D_18)) = D_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_12,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_51,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_mcart_1(k4_mcart_1(A_19,B_20,C_21,D_22)) = D_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_60,plain,(
    k2_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_63,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_60])).

tff(c_64,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_81,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_5','#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_87,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_81])).

tff(c_176,plain,(
    ! [A_35,B_36,C_37] : k2_mcart_1(k3_mcart_1(A_35,B_36,C_37)) = C_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_8])).

tff(c_185,plain,(
    k2_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_176])).

tff(c_188,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_185])).

tff(c_214,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_3') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_87])).

tff(c_231,plain,(
    k1_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = k4_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_159])).

tff(c_240,plain,(
    k4_tarski('#skF_5','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_231])).

tff(c_253,plain,(
    k1_mcart_1(k4_tarski('#skF_1','#skF_2')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_6])).

tff(c_261,plain,(
    '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_253])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_261])).

tff(c_264,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_270,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_276,plain,(
    ! [A_46,B_47,C_48,D_49] : k4_tarski(k3_mcart_1(A_46,B_47,C_48),D_49) = k4_mcart_1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_285,plain,(
    ! [A_46,B_47,C_48,D_49] : k2_mcart_1(k4_mcart_1(A_46,B_47,C_48,D_49)) = D_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_8])).

tff(c_265,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_271,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_12])).

tff(c_321,plain,(
    ! [A_54,B_55,C_56,D_57] : k2_mcart_1(k4_mcart_1(A_54,B_55,C_56,D_57)) = D_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_8])).

tff(c_330,plain,(
    k2_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_321])).

tff(c_333,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_330])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_333])).

tff(c_336,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_342,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_348,plain,(
    ! [A_58,B_59,C_60,D_61] : k4_tarski(k3_mcart_1(A_58,B_59,C_60),D_61) = k4_mcart_1(A_58,B_59,C_60,D_61) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_354,plain,(
    ! [A_58,B_59,C_60,D_61] : k1_mcart_1(k4_mcart_1(A_58,B_59,C_60,D_61)) = k3_mcart_1(A_58,B_59,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_6])).

tff(c_397,plain,(
    ! [A_70,B_71,C_72,D_73] : k4_tarski(k4_tarski(k4_tarski(A_70,B_71),C_72),D_73) = k4_mcart_1(A_70,B_71,C_72,D_73) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_409,plain,(
    ! [A_70,B_71,C_72,D_73] : k4_tarski(k4_tarski(A_70,B_71),C_72) = k1_mcart_1(k4_mcart_1(A_70,B_71,C_72,D_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_6])).

tff(c_431,plain,(
    ! [A_74,B_75,C_76] : k4_tarski(k4_tarski(A_74,B_75),C_76) = k3_mcart_1(A_74,B_75,C_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_409])).

tff(c_440,plain,(
    ! [A_74,B_75,C_76] : k1_mcart_1(k3_mcart_1(A_74,B_75,C_76)) = k4_tarski(A_74,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_6])).

tff(c_443,plain,(
    ! [A_74,B_75,C_76] : k2_mcart_1(k3_mcart_1(A_74,B_75,C_76)) = C_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_8])).

tff(c_337,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_343,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_265,c_12])).

tff(c_376,plain,(
    ! [A_66,B_67,C_68,D_69] : k1_mcart_1(k4_mcart_1(A_66,B_67,C_68,D_69)) = k3_mcart_1(A_66,B_67,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_6])).

tff(c_385,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_1','#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_376])).

tff(c_388,plain,(
    k3_mcart_1('#skF_1','#skF_6','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_385])).

tff(c_457,plain,(
    ! [A_77,B_78,C_79] : k2_mcart_1(k3_mcart_1(A_77,B_78,C_79)) = C_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_8])).

tff(c_466,plain,(
    k2_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_457])).

tff(c_469,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_466])).

tff(c_470,plain,(
    k3_mcart_1('#skF_1','#skF_6','#skF_3') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_388])).

tff(c_500,plain,(
    k1_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = k4_tarski('#skF_1','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_440])).

tff(c_509,plain,(
    k4_tarski('#skF_1','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_500])).

tff(c_522,plain,(
    k2_mcart_1(k4_tarski('#skF_1','#skF_2')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_8])).

tff(c_527,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_522])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_527])).

tff(c_530,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_541,plain,(
    ! [A_83,B_84,C_85,D_86] : k4_tarski(k3_mcart_1(A_83,B_84,C_85),D_86) = k4_mcart_1(A_83,B_84,C_85,D_86) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_547,plain,(
    ! [A_83,B_84,C_85,D_86] : k1_mcart_1(k4_mcart_1(A_83,B_84,C_85,D_86)) = k3_mcart_1(A_83,B_84,C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_6])).

tff(c_608,plain,(
    ! [A_96,B_97,C_98,D_99] : k4_tarski(k4_tarski(k4_tarski(A_96,B_97),C_98),D_99) = k4_mcart_1(A_96,B_97,C_98,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_620,plain,(
    ! [A_96,B_97,C_98,D_99] : k4_tarski(k4_tarski(A_96,B_97),C_98) = k1_mcart_1(k4_mcart_1(A_96,B_97,C_98,D_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_6])).

tff(c_642,plain,(
    ! [A_100,B_101,C_102] : k4_tarski(k4_tarski(A_100,B_101),C_102) = k3_mcart_1(A_100,B_101,C_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_620])).

tff(c_654,plain,(
    ! [A_100,B_101,C_102] : k2_mcart_1(k3_mcart_1(A_100,B_101,C_102)) = C_102 ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_8])).

tff(c_531,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_536,plain,(
    k4_mcart_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_265,c_337,c_12])).

tff(c_569,plain,(
    ! [A_91,B_92,C_93,D_94] : k1_mcart_1(k4_mcart_1(A_91,B_92,C_93,D_94)) = k3_mcart_1(A_91,B_92,C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_6])).

tff(c_578,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_1','#skF_2','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_569])).

tff(c_581,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_578])).

tff(c_668,plain,(
    ! [A_103,B_104,C_105] : k2_mcart_1(k3_mcart_1(A_103,B_104,C_105)) = C_105 ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_8])).

tff(c_677,plain,(
    k2_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_668])).

tff(c_680,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_677])).

tff(c_682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.32  
% 2.08/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.33  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.08/1.33  
% 2.08/1.33  %Foreground sorts:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Background operators:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Foreground operators:
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.08/1.33  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.08/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.08/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.08/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.08/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.08/1.33  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.08/1.33  
% 2.41/1.34  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 2.41/1.34  tff(f_33, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.41/1.34  tff(f_27, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.41/1.34  tff(f_29, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 2.41/1.34  tff(c_10, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.41/1.34  tff(c_31, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_10])).
% 2.41/1.34  tff(c_6, plain, (![A_9, B_10]: (k1_mcart_1(k4_tarski(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.34  tff(c_36, plain, (![A_15, B_16, C_17, D_18]: (k4_tarski(k3_mcart_1(A_15, B_16, C_17), D_18)=k4_mcart_1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.34  tff(c_42, plain, (![A_15, B_16, C_17, D_18]: (k1_mcart_1(k4_mcart_1(A_15, B_16, C_17, D_18))=k3_mcart_1(A_15, B_16, C_17))), inference(superposition, [status(thm), theory('equality')], [c_36, c_6])).
% 2.41/1.34  tff(c_116, plain, (![A_28, B_29, C_30, D_31]: (k4_tarski(k4_tarski(k4_tarski(A_28, B_29), C_30), D_31)=k4_mcart_1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.34  tff(c_128, plain, (![A_28, B_29, C_30, D_31]: (k4_tarski(k4_tarski(A_28, B_29), C_30)=k1_mcart_1(k4_mcart_1(A_28, B_29, C_30, D_31)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_6])).
% 2.41/1.34  tff(c_150, plain, (![A_32, B_33, C_34]: (k4_tarski(k4_tarski(A_32, B_33), C_34)=k3_mcart_1(A_32, B_33, C_34))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_128])).
% 2.41/1.34  tff(c_159, plain, (![A_32, B_33, C_34]: (k1_mcart_1(k3_mcart_1(A_32, B_33, C_34))=k4_tarski(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_150, c_6])).
% 2.41/1.34  tff(c_8, plain, (![A_9, B_10]: (k2_mcart_1(k4_tarski(A_9, B_10))=B_10)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.34  tff(c_162, plain, (![A_32, B_33, C_34]: (k2_mcart_1(k3_mcart_1(A_32, B_33, C_34))=C_34)), inference(superposition, [status(thm), theory('equality')], [c_150, c_8])).
% 2.41/1.34  tff(c_45, plain, (![A_15, B_16, C_17, D_18]: (k2_mcart_1(k4_mcart_1(A_15, B_16, C_17, D_18))=D_18)), inference(superposition, [status(thm), theory('equality')], [c_36, c_8])).
% 2.41/1.34  tff(c_12, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.41/1.34  tff(c_51, plain, (![A_19, B_20, C_21, D_22]: (k2_mcart_1(k4_mcart_1(A_19, B_20, C_21, D_22))=D_22)), inference(superposition, [status(thm), theory('equality')], [c_36, c_8])).
% 2.41/1.34  tff(c_60, plain, (k2_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 2.41/1.34  tff(c_63, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_60])).
% 2.41/1.34  tff(c_64, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_12])).
% 2.41/1.34  tff(c_81, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_5', '#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_64, c_42])).
% 2.41/1.34  tff(c_87, plain, (k3_mcart_1('#skF_5', '#skF_6', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_81])).
% 2.41/1.34  tff(c_176, plain, (![A_35, B_36, C_37]: (k2_mcart_1(k3_mcart_1(A_35, B_36, C_37))=C_37)), inference(superposition, [status(thm), theory('equality')], [c_150, c_8])).
% 2.41/1.34  tff(c_185, plain, (k2_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_87, c_176])).
% 2.41/1.34  tff(c_188, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_185])).
% 2.41/1.34  tff(c_214, plain, (k3_mcart_1('#skF_5', '#skF_6', '#skF_3')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_87])).
% 2.41/1.34  tff(c_231, plain, (k1_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))=k4_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_214, c_159])).
% 2.41/1.34  tff(c_240, plain, (k4_tarski('#skF_5', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_231])).
% 2.41/1.34  tff(c_253, plain, (k1_mcart_1(k4_tarski('#skF_1', '#skF_2'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_240, c_6])).
% 2.41/1.34  tff(c_261, plain, ('#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_253])).
% 2.41/1.34  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_261])).
% 2.41/1.34  tff(c_264, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_10])).
% 2.41/1.34  tff(c_270, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_264])).
% 2.41/1.34  tff(c_276, plain, (![A_46, B_47, C_48, D_49]: (k4_tarski(k3_mcart_1(A_46, B_47, C_48), D_49)=k4_mcart_1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.34  tff(c_285, plain, (![A_46, B_47, C_48, D_49]: (k2_mcart_1(k4_mcart_1(A_46, B_47, C_48, D_49))=D_49)), inference(superposition, [status(thm), theory('equality')], [c_276, c_8])).
% 2.41/1.34  tff(c_265, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_10])).
% 2.41/1.34  tff(c_271, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_12])).
% 2.41/1.34  tff(c_321, plain, (![A_54, B_55, C_56, D_57]: (k2_mcart_1(k4_mcart_1(A_54, B_55, C_56, D_57))=D_57)), inference(superposition, [status(thm), theory('equality')], [c_276, c_8])).
% 2.41/1.34  tff(c_330, plain, (k2_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_271, c_321])).
% 2.41/1.34  tff(c_333, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_285, c_330])).
% 2.41/1.34  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_270, c_333])).
% 2.41/1.34  tff(c_336, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_264])).
% 2.41/1.34  tff(c_342, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_336])).
% 2.41/1.34  tff(c_348, plain, (![A_58, B_59, C_60, D_61]: (k4_tarski(k3_mcart_1(A_58, B_59, C_60), D_61)=k4_mcart_1(A_58, B_59, C_60, D_61))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.34  tff(c_354, plain, (![A_58, B_59, C_60, D_61]: (k1_mcart_1(k4_mcart_1(A_58, B_59, C_60, D_61))=k3_mcart_1(A_58, B_59, C_60))), inference(superposition, [status(thm), theory('equality')], [c_348, c_6])).
% 2.41/1.34  tff(c_397, plain, (![A_70, B_71, C_72, D_73]: (k4_tarski(k4_tarski(k4_tarski(A_70, B_71), C_72), D_73)=k4_mcart_1(A_70, B_71, C_72, D_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.34  tff(c_409, plain, (![A_70, B_71, C_72, D_73]: (k4_tarski(k4_tarski(A_70, B_71), C_72)=k1_mcart_1(k4_mcart_1(A_70, B_71, C_72, D_73)))), inference(superposition, [status(thm), theory('equality')], [c_397, c_6])).
% 2.41/1.34  tff(c_431, plain, (![A_74, B_75, C_76]: (k4_tarski(k4_tarski(A_74, B_75), C_76)=k3_mcart_1(A_74, B_75, C_76))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_409])).
% 2.41/1.34  tff(c_440, plain, (![A_74, B_75, C_76]: (k1_mcart_1(k3_mcart_1(A_74, B_75, C_76))=k4_tarski(A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_431, c_6])).
% 2.41/1.34  tff(c_443, plain, (![A_74, B_75, C_76]: (k2_mcart_1(k3_mcart_1(A_74, B_75, C_76))=C_76)), inference(superposition, [status(thm), theory('equality')], [c_431, c_8])).
% 2.41/1.34  tff(c_337, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_264])).
% 2.41/1.34  tff(c_343, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_265, c_12])).
% 2.41/1.34  tff(c_376, plain, (![A_66, B_67, C_68, D_69]: (k1_mcart_1(k4_mcart_1(A_66, B_67, C_68, D_69))=k3_mcart_1(A_66, B_67, C_68))), inference(superposition, [status(thm), theory('equality')], [c_348, c_6])).
% 2.41/1.34  tff(c_385, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_1', '#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_343, c_376])).
% 2.41/1.34  tff(c_388, plain, (k3_mcart_1('#skF_1', '#skF_6', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_385])).
% 2.41/1.34  tff(c_457, plain, (![A_77, B_78, C_79]: (k2_mcart_1(k3_mcart_1(A_77, B_78, C_79))=C_79)), inference(superposition, [status(thm), theory('equality')], [c_431, c_8])).
% 2.41/1.34  tff(c_466, plain, (k2_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_388, c_457])).
% 2.41/1.34  tff(c_469, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_466])).
% 2.41/1.34  tff(c_470, plain, (k3_mcart_1('#skF_1', '#skF_6', '#skF_3')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_388])).
% 2.41/1.34  tff(c_500, plain, (k1_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))=k4_tarski('#skF_1', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_470, c_440])).
% 2.41/1.34  tff(c_509, plain, (k4_tarski('#skF_1', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_500])).
% 2.41/1.34  tff(c_522, plain, (k2_mcart_1(k4_tarski('#skF_1', '#skF_2'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_509, c_8])).
% 2.41/1.34  tff(c_527, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_522])).
% 2.41/1.34  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_527])).
% 2.41/1.34  tff(c_530, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_336])).
% 2.41/1.34  tff(c_541, plain, (![A_83, B_84, C_85, D_86]: (k4_tarski(k3_mcart_1(A_83, B_84, C_85), D_86)=k4_mcart_1(A_83, B_84, C_85, D_86))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.34  tff(c_547, plain, (![A_83, B_84, C_85, D_86]: (k1_mcart_1(k4_mcart_1(A_83, B_84, C_85, D_86))=k3_mcart_1(A_83, B_84, C_85))), inference(superposition, [status(thm), theory('equality')], [c_541, c_6])).
% 2.41/1.34  tff(c_608, plain, (![A_96, B_97, C_98, D_99]: (k4_tarski(k4_tarski(k4_tarski(A_96, B_97), C_98), D_99)=k4_mcart_1(A_96, B_97, C_98, D_99))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.34  tff(c_620, plain, (![A_96, B_97, C_98, D_99]: (k4_tarski(k4_tarski(A_96, B_97), C_98)=k1_mcart_1(k4_mcart_1(A_96, B_97, C_98, D_99)))), inference(superposition, [status(thm), theory('equality')], [c_608, c_6])).
% 2.41/1.34  tff(c_642, plain, (![A_100, B_101, C_102]: (k4_tarski(k4_tarski(A_100, B_101), C_102)=k3_mcart_1(A_100, B_101, C_102))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_620])).
% 2.41/1.34  tff(c_654, plain, (![A_100, B_101, C_102]: (k2_mcart_1(k3_mcart_1(A_100, B_101, C_102))=C_102)), inference(superposition, [status(thm), theory('equality')], [c_642, c_8])).
% 2.41/1.34  tff(c_531, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_336])).
% 2.41/1.34  tff(c_536, plain, (k4_mcart_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_265, c_337, c_12])).
% 2.41/1.34  tff(c_569, plain, (![A_91, B_92, C_93, D_94]: (k1_mcart_1(k4_mcart_1(A_91, B_92, C_93, D_94))=k3_mcart_1(A_91, B_92, C_93))), inference(superposition, [status(thm), theory('equality')], [c_541, c_6])).
% 2.41/1.34  tff(c_578, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_1', '#skF_2', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_536, c_569])).
% 2.41/1.34  tff(c_581, plain, (k3_mcart_1('#skF_1', '#skF_2', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_578])).
% 2.41/1.34  tff(c_668, plain, (![A_103, B_104, C_105]: (k2_mcart_1(k3_mcart_1(A_103, B_104, C_105))=C_105)), inference(superposition, [status(thm), theory('equality')], [c_642, c_8])).
% 2.41/1.34  tff(c_677, plain, (k2_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_581, c_668])).
% 2.41/1.34  tff(c_680, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_654, c_677])).
% 2.41/1.34  tff(c_682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_530, c_680])).
% 2.41/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  Inference rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Ref     : 0
% 2.41/1.34  #Sup     : 182
% 2.41/1.34  #Fact    : 0
% 2.41/1.34  #Define  : 0
% 2.41/1.34  #Split   : 3
% 2.41/1.34  #Chain   : 0
% 2.41/1.34  #Close   : 0
% 2.41/1.34  
% 2.41/1.34  Ordering : KBO
% 2.41/1.34  
% 2.41/1.34  Simplification rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Subsume      : 0
% 2.41/1.34  #Demod        : 69
% 2.41/1.34  #Tautology    : 112
% 2.41/1.34  #SimpNegUnit  : 4
% 2.41/1.34  #BackRed      : 8
% 2.41/1.34  
% 2.41/1.34  #Partial instantiations: 0
% 2.41/1.35  #Strategies tried      : 1
% 2.41/1.35  
% 2.41/1.35  Timing (in seconds)
% 2.41/1.35  ----------------------
% 2.41/1.35  Preprocessing        : 0.27
% 2.41/1.35  Parsing              : 0.15
% 2.41/1.35  CNF conversion       : 0.01
% 2.41/1.35  Main loop            : 0.29
% 2.41/1.35  Inferencing          : 0.12
% 2.41/1.35  Reduction            : 0.09
% 2.41/1.35  Demodulation         : 0.07
% 2.41/1.35  BG Simplification    : 0.02
% 2.41/1.35  Subsumption          : 0.02
% 2.41/1.35  Abstraction          : 0.02
% 2.41/1.35  MUC search           : 0.00
% 2.41/1.35  Cooper               : 0.00
% 2.41/1.35  Total                : 0.60
% 2.41/1.35  Index Insertion      : 0.00
% 2.41/1.35  Index Deletion       : 0.00
% 2.41/1.35  Index Matching       : 0.00
% 2.41/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
