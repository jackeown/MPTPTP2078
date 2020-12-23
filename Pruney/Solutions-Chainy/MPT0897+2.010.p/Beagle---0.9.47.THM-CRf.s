%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:49 EST 2020

% Result     : Theorem 9.12s
% Output     : CNFRefutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :  238 (8385 expanded)
%              Number of leaves         :   21 (2691 expanded)
%              Depth                    :   25
%              Number of atoms          :  446 (15066 expanded)
%              Number of equality atoms :  430 (15050 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

tff(c_30,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_109,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_zfmisc_1(k3_zfmisc_1(A_4,B_5,C_6),D_7) = k4_zfmisc_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_36,B_37,C_38] : k2_zfmisc_1(k2_zfmisc_1(A_36,B_37),C_38) = k3_zfmisc_1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_36,B_37,C_38,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_36,B_37),C_38,C_3) = k2_zfmisc_1(k3_zfmisc_1(A_36,B_37,C_38),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_2])).

tff(c_141,plain,(
    ! [A_36,B_37,C_38,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_36,B_37),C_38,C_3) = k4_zfmisc_1(A_36,B_37,C_38,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_113])).

tff(c_32,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_387,plain,(
    ! [A_85,E_80,F_81,B_84,C_83,D_82] :
      ( F_81 = C_83
      | k3_zfmisc_1(A_85,B_84,C_83) = k1_xboole_0
      | k3_zfmisc_1(D_82,E_80,F_81) != k3_zfmisc_1(A_85,B_84,C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1068,plain,(
    ! [C_152,C_155,C_156,B_153,A_157,A_151,B_154] :
      ( C_155 = C_152
      | k3_zfmisc_1(A_157,B_154,C_152) = k1_xboole_0
      | k4_zfmisc_1(A_151,B_153,C_156,C_155) != k3_zfmisc_1(A_157,B_154,C_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_387])).

tff(c_1506,plain,(
    ! [C_188,A_189,B_190] :
      ( C_188 = '#skF_8'
      | k3_zfmisc_1(A_189,B_190,C_188) = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_189,B_190,C_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1068])).

tff(c_1533,plain,(
    ! [C_3,A_36,B_37,C_38] :
      ( C_3 = '#skF_8'
      | k3_zfmisc_1(k2_zfmisc_1(A_36,B_37),C_38,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_36,B_37,C_38,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_1506])).

tff(c_1542,plain,(
    ! [C_3,A_36,B_37,C_38] :
      ( C_3 = '#skF_8'
      | k4_zfmisc_1(A_36,B_37,C_38,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_36,B_37,C_38,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_1533])).

tff(c_2212,plain,
    ( '#skF_8' = '#skF_4'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1542])).

tff(c_2213,plain,(
    '#skF_8' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2212])).

tff(c_260,plain,(
    ! [D_63,E_61,A_66,C_64,B_65,F_62] :
      ( E_61 = B_65
      | k3_zfmisc_1(A_66,B_65,C_64) = k1_xboole_0
      | k3_zfmisc_1(D_63,E_61,F_62) != k3_zfmisc_1(A_66,B_65,C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1410,plain,(
    ! [A_181,B_178,C_184,C_183,B_182,A_180,C_179] :
      ( C_184 = B_178
      | k3_zfmisc_1(A_181,B_178,C_179) = k1_xboole_0
      | k4_zfmisc_1(A_180,B_182,C_184,C_183) != k3_zfmisc_1(A_181,B_178,C_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_260])).

tff(c_1469,plain,(
    ! [B_185,A_186,C_187] :
      ( B_185 = '#skF_7'
      | k3_zfmisc_1(A_186,B_185,C_187) = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_186,B_185,C_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1410])).

tff(c_1496,plain,(
    ! [C_38,A_36,B_37,C_3] :
      ( C_38 = '#skF_7'
      | k3_zfmisc_1(k2_zfmisc_1(A_36,B_37),C_38,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_36,B_37,C_38,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_1469])).

tff(c_1505,plain,(
    ! [C_38,A_36,B_37,C_3] :
      ( C_38 = '#skF_7'
      | k4_zfmisc_1(A_36,B_37,C_38,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_36,B_37,C_38,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_1496])).

tff(c_1546,plain,
    ( '#skF_7' = '#skF_3'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1505])).

tff(c_1547,plain,(
    '#skF_7' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1546])).

tff(c_1582,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_32])).

tff(c_2247,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2213,c_1582])).

tff(c_300,plain,(
    ! [D_70,B_72,E_68,C_71,A_73,F_69] :
      ( D_70 = A_73
      | k3_zfmisc_1(A_73,B_72,C_71) = k1_xboole_0
      | k3_zfmisc_1(D_70,E_68,F_69) != k3_zfmisc_1(A_73,B_72,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_312,plain,(
    ! [D_70,A_36,C_3,E_68,C_38,F_69,B_37] :
      ( k2_zfmisc_1(A_36,B_37) = D_70
      | k3_zfmisc_1(k2_zfmisc_1(A_36,B_37),C_38,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_36,B_37,C_38,C_3) != k3_zfmisc_1(D_70,E_68,F_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_300])).

tff(c_3680,plain,(
    ! [D_372,B_368,E_371,A_367,F_373,C_369,C_370] :
      ( k2_zfmisc_1(A_367,B_368) = D_372
      | k4_zfmisc_1(A_367,B_368,C_370,C_369) = k1_xboole_0
      | k4_zfmisc_1(A_367,B_368,C_370,C_369) != k3_zfmisc_1(D_372,E_371,F_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_312])).

tff(c_3683,plain,(
    ! [D_372,E_371,F_373] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_372
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_372,E_371,F_373) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2247,c_3680])).

tff(c_3717,plain,(
    ! [D_372,E_371,F_373] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_372
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_372,E_371,F_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2247,c_3683])).

tff(c_3732,plain,(
    ! [D_375,E_376,F_377] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_375
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_375,E_376,F_377) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3717])).

tff(c_3747,plain,(
    ! [A_36,B_37,C_38,C_3] :
      ( k2_zfmisc_1(A_36,B_37) = k2_zfmisc_1('#skF_5','#skF_6')
      | k4_zfmisc_1(A_36,B_37,C_38,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_3732])).

tff(c_3751,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3747])).

tff(c_3829,plain,(
    ! [C_3] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_3) = k3_zfmisc_1('#skF_5','#skF_6',C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_3751,c_2])).

tff(c_3836,plain,(
    ! [C_387] : k3_zfmisc_1('#skF_5','#skF_6',C_387) = k3_zfmisc_1('#skF_1','#skF_2',C_387) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3829])).

tff(c_16,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] :
      ( D_17 = A_14
      | k3_zfmisc_1(A_14,B_15,C_16) = k1_xboole_0
      | k3_zfmisc_1(D_17,E_18,F_19) != k3_zfmisc_1(A_14,B_15,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3918,plain,(
    ! [A_14,B_15,C_16,C_387] :
      ( A_14 = '#skF_5'
      | k3_zfmisc_1(A_14,B_15,C_16) = k1_xboole_0
      | k3_zfmisc_1(A_14,B_15,C_16) != k3_zfmisc_1('#skF_1','#skF_2',C_387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3836,c_16])).

tff(c_4380,plain,(
    ! [C_387] :
      ( '#skF_5' = '#skF_1'
      | k3_zfmisc_1('#skF_1','#skF_2',C_387) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3918])).

tff(c_4381,plain,(
    ! [C_387] : k3_zfmisc_1('#skF_1','#skF_2',C_387) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_4380])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22] : k4_zfmisc_1(A_20,B_21,C_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_142,plain,(
    ! [A_43,B_44,C_45,C_46] : k3_zfmisc_1(k2_zfmisc_1(A_43,B_44),C_45,C_46) = k4_zfmisc_1(A_43,B_44,C_45,C_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_113])).

tff(c_209,plain,(
    ! [B_59,C_56,A_58,C_57,D_60] : k4_zfmisc_1(k2_zfmisc_1(A_58,B_59),C_56,C_57,D_60) = k2_zfmisc_1(k4_zfmisc_1(A_58,B_59,C_56,C_57),D_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_4])).

tff(c_22,plain,(
    ! [A_20,B_21,D_23] : k4_zfmisc_1(A_20,B_21,k1_xboole_0,D_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,(
    ! [A_58,B_59,C_56,D_60] : k2_zfmisc_1(k4_zfmisc_1(A_58,B_59,C_56,k1_xboole_0),D_60) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_22])).

tff(c_250,plain,(
    ! [D_60] : k2_zfmisc_1(k1_xboole_0,D_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_223])).

tff(c_346,plain,(
    ! [A_76,B_77,B_78,C_79] : k2_zfmisc_1(k4_zfmisc_1(A_76,B_77,B_78,C_79),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_209])).

tff(c_357,plain,(
    ! [B_77,A_76,B_78,C_3,C_79] : k3_zfmisc_1(k4_zfmisc_1(A_76,B_77,B_78,C_79),k1_xboole_0,C_3) = k2_zfmisc_1(k1_xboole_0,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_2])).

tff(c_375,plain,(
    ! [B_77,A_76,B_78,C_3,C_79] : k3_zfmisc_1(k4_zfmisc_1(A_76,B_77,B_78,C_79),k1_xboole_0,C_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_357])).

tff(c_800,plain,(
    ! [C_126,D_127,B_125,A_123,E_124,F_122] :
      ( F_122 = C_126
      | k1_xboole_0 = C_126
      | k1_xboole_0 = B_125
      | k1_xboole_0 = A_123
      | k3_zfmisc_1(D_127,E_124,F_122) != k3_zfmisc_1(A_123,B_125,C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_821,plain,(
    ! [C_3,C_126,B_125,A_123] :
      ( C_3 = C_126
      | k1_xboole_0 = C_126
      | k1_xboole_0 = B_125
      | k1_xboole_0 = A_123
      | k3_zfmisc_1(A_123,B_125,C_126) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_800])).

tff(c_3895,plain,(
    ! [C_387,C_3] :
      ( C_387 = C_3
      | k1_xboole_0 = C_387
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k3_zfmisc_1('#skF_1','#skF_2',C_387) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3836,c_821])).

tff(c_4151,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3895])).

tff(c_275,plain,(
    ! [D_67] : k2_zfmisc_1(k1_xboole_0,D_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_223])).

tff(c_286,plain,(
    ! [D_67,C_3] : k3_zfmisc_1(k1_xboole_0,D_67,C_3) = k2_zfmisc_1(k1_xboole_0,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_2])).

tff(c_292,plain,(
    ! [D_67,C_3] : k3_zfmisc_1(k1_xboole_0,D_67,C_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_286])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k4_zfmisc_1(A_20,B_21,C_22,D_23) != k1_xboole_0
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2650,plain,(
    ! [C_306,A_307,D_309,B_305,C_308] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_307,B_305,C_306,C_308),D_309) != k1_xboole_0
      | k1_xboole_0 = D_309
      | k1_xboole_0 = C_308
      | k1_xboole_0 = C_306
      | k2_zfmisc_1(A_307,B_305) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_18])).

tff(c_2653,plain,(
    ! [D_309] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),D_309) != k1_xboole_0
      | k1_xboole_0 = D_309
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2247,c_2650])).

tff(c_2745,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2653])).

tff(c_2752,plain,(
    ! [C_38,C_3] : k4_zfmisc_1('#skF_5','#skF_6',C_38,C_3) = k3_zfmisc_1(k1_xboole_0,C_38,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_2745,c_141])).

tff(c_2759,plain,(
    ! [C_38,C_3] : k4_zfmisc_1('#skF_5','#skF_6',C_38,C_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_2752])).

tff(c_2878,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2759,c_2247])).

tff(c_2880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2878])).

tff(c_2882,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2653])).

tff(c_3819,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3751,c_2882])).

tff(c_4155,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4151,c_3819])).

tff(c_4186,plain,(
    ! [D_60] : k2_zfmisc_1('#skF_5',D_60) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4151,c_4151,c_250])).

tff(c_4199,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4186,c_3751])).

tff(c_4217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4155,c_4199])).

tff(c_4219,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3895])).

tff(c_4218,plain,(
    ! [C_387,C_3] :
      ( k1_xboole_0 = '#skF_6'
      | C_387 = C_3
      | k1_xboole_0 = C_387
      | k3_zfmisc_1('#skF_1','#skF_2',C_387) != k1_xboole_0 ) ),
    inference(splitRight,[status(thm)],[c_3895])).

tff(c_4253,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4218])).

tff(c_4258,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_3819])).

tff(c_24,plain,(
    ! [A_20,C_22,D_23] : k4_zfmisc_1(A_20,k1_xboole_0,C_22,D_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_574,plain,(
    ! [B_104,A_102,C_105,F_101,E_103,D_106] :
      ( E_103 = B_104
      | k1_xboole_0 = C_105
      | k1_xboole_0 = B_104
      | k1_xboole_0 = A_102
      | k3_zfmisc_1(D_106,E_103,F_101) != k3_zfmisc_1(A_102,B_104,C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_764,plain,(
    ! [B_119,C_120,A_121] :
      ( k1_xboole_0 = B_119
      | k1_xboole_0 = C_120
      | k1_xboole_0 = B_119
      | k1_xboole_0 = A_121
      | k3_zfmisc_1(A_121,B_119,C_120) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_574])).

tff(c_1627,plain,(
    ! [C_195,C_196,A_197,B_198] :
      ( k1_xboole_0 = C_195
      | k1_xboole_0 = C_196
      | k1_xboole_0 = C_195
      | k2_zfmisc_1(A_197,B_198) = k1_xboole_0
      | k4_zfmisc_1(A_197,B_198,C_195,C_196) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_764])).

tff(c_1655,plain,(
    ! [D_23,C_22,A_20] :
      ( k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1627])).

tff(c_1658,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1655])).

tff(c_4278,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4253,c_4253,c_1658])).

tff(c_4319,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4278,c_3751])).

tff(c_4321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4258,c_4319])).

tff(c_4323,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4218])).

tff(c_589,plain,(
    ! [D_67,B_104,C_105,A_102] :
      ( D_67 = B_104
      | k1_xboole_0 = C_105
      | k1_xboole_0 = B_104
      | k1_xboole_0 = A_102
      | k3_zfmisc_1(A_102,B_104,C_105) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_574])).

tff(c_3897,plain,(
    ! [D_67,C_387] :
      ( D_67 = '#skF_6'
      | k1_xboole_0 = C_387
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k3_zfmisc_1('#skF_1','#skF_2',C_387) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3836,c_589])).

tff(c_4330,plain,(
    ! [D_67,C_387] :
      ( D_67 = '#skF_6'
      | k1_xboole_0 = C_387
      | k3_zfmisc_1('#skF_1','#skF_2',C_387) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_4219,c_4323,c_3897])).

tff(c_4331,plain,(
    ! [C_387] :
      ( k1_xboole_0 = C_387
      | k3_zfmisc_1('#skF_1','#skF_2',C_387) != k1_xboole_0 ) ),
    inference(splitLeft,[status(thm)],[c_4330])).

tff(c_4542,plain,(
    ! [C_426] : k1_xboole_0 = C_426 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4381,c_4331])).

tff(c_4664,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4542,c_3819])).

tff(c_4667,plain,(
    ! [D_697] : D_697 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4330])).

tff(c_4978,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4667,c_4323])).

tff(c_4979,plain,(
    ! [D_23,C_22] :
      ( k1_xboole_0 = D_23
      | k1_xboole_0 = C_22 ) ),
    inference(splitRight,[status(thm)],[c_1655])).

tff(c_4981,plain,(
    ! [C_1319] : k1_xboole_0 = C_1319 ),
    inference(splitLeft,[status(thm)],[c_4979])).

tff(c_5007,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4981,c_1582])).

tff(c_5059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_5007])).

tff(c_5104,plain,(
    ! [D_1432] : k1_xboole_0 = D_1432 ),
    inference(splitRight,[status(thm)],[c_4979])).

tff(c_5180,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5104,c_30])).

tff(c_5181,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_5187,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5181])).

tff(c_5188,plain,(
    ! [A_1541,B_1542,C_1543] : k2_zfmisc_1(k2_zfmisc_1(A_1541,B_1542),C_1543) = k3_zfmisc_1(A_1541,B_1542,C_1543) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_5197,plain,(
    ! [A_1,B_2,C_3,C_1543] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_1543) = k2_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),C_1543) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5188])).

tff(c_5220,plain,(
    ! [A_1,B_2,C_3,C_1543] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_1543) = k4_zfmisc_1(A_1,B_2,C_3,C_1543) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_5197])).

tff(c_5182,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_5203,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5182,c_32])).

tff(c_5559,plain,(
    ! [B_1599,C_1598,A_1600,D_1597,E_1595,F_1596] :
      ( E_1595 = B_1599
      | k3_zfmisc_1(A_1600,B_1599,C_1598) = k1_xboole_0
      | k3_zfmisc_1(D_1597,E_1595,F_1596) != k3_zfmisc_1(A_1600,B_1599,C_1598) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6489,plain,(
    ! [C_1687,C_1683,C_1684,A_1688,B_1685,A_1689,B_1686] :
      ( C_1687 = B_1685
      | k3_zfmisc_1(A_1689,B_1685,C_1683) = k1_xboole_0
      | k4_zfmisc_1(A_1688,B_1686,C_1687,C_1684) != k3_zfmisc_1(A_1689,B_1685,C_1683) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5220,c_5559])).

tff(c_6587,plain,(
    ! [B_1693,A_1694,C_1695] :
      ( B_1693 = '#skF_7'
      | k3_zfmisc_1(A_1694,B_1693,C_1695) = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_1694,B_1693,C_1695) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5203,c_6489])).

tff(c_6614,plain,(
    ! [C_3,A_1,B_2,C_1543] :
      ( C_3 = '#skF_7'
      | k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_1543) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,C_1543) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5220,c_6587])).

tff(c_6623,plain,(
    ! [C_3,A_1,B_2,C_1543] :
      ( C_3 = '#skF_7'
      | k4_zfmisc_1(A_1,B_2,C_3,C_1543) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,C_1543) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5220,c_6614])).

tff(c_6650,plain,
    ( '#skF_7' = '#skF_3'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6623])).

tff(c_6651,plain,(
    '#skF_7' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_6650])).

tff(c_6686,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6651,c_5203])).

tff(c_5402,plain,(
    ! [E_1575,A_1580,D_1577,F_1576,C_1578,B_1579] :
      ( F_1576 = C_1578
      | k3_zfmisc_1(A_1580,B_1579,C_1578) = k1_xboole_0
      | k3_zfmisc_1(D_1577,E_1575,F_1576) != k3_zfmisc_1(A_1580,B_1579,C_1578) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5420,plain,(
    ! [C_1543,E_1575,B_2,C_3,A_1,D_1577,F_1576] :
      ( F_1576 = C_1543
      | k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_1543) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,C_1543) != k3_zfmisc_1(D_1577,E_1575,F_1576) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5220,c_5402])).

tff(c_7256,plain,(
    ! [E_1749,B_1744,C_1746,C_1743,A_1747,F_1745,D_1748] :
      ( F_1745 = C_1743
      | k4_zfmisc_1(A_1747,B_1744,C_1746,C_1743) = k1_xboole_0
      | k4_zfmisc_1(A_1747,B_1744,C_1746,C_1743) != k3_zfmisc_1(D_1748,E_1749,F_1745) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5220,c_5420])).

tff(c_7265,plain,(
    ! [F_1745,D_1748,E_1749] :
      ( F_1745 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1748,E_1749,F_1745) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6686,c_7256])).

tff(c_7293,plain,(
    ! [F_1745,D_1748,E_1749] :
      ( F_1745 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1748,E_1749,F_1745) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6686,c_7265])).

tff(c_7317,plain,(
    ! [F_1753,D_1754,E_1755] :
      ( F_1753 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1754,E_1755,F_1753) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_7293])).

tff(c_7332,plain,(
    ! [C_1543,A_1,B_2,C_3] :
      ( C_1543 = '#skF_8'
      | k4_zfmisc_1(A_1,B_2,C_3,C_1543) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5220,c_7317])).

tff(c_7362,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7332])).

tff(c_7364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5187,c_7362])).

tff(c_7365,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5181])).

tff(c_7371,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7365])).

tff(c_7372,plain,(
    ! [A_1760,B_1761,C_1762] : k2_zfmisc_1(k2_zfmisc_1(A_1760,B_1761),C_1762) = k3_zfmisc_1(A_1760,B_1761,C_1762) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7375,plain,(
    ! [A_1760,B_1761,C_1762,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_1760,B_1761),C_1762,C_3) = k2_zfmisc_1(k3_zfmisc_1(A_1760,B_1761,C_1762),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_7372,c_2])).

tff(c_7404,plain,(
    ! [A_1760,B_1761,C_1762,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_1760,B_1761),C_1762,C_3) = k4_zfmisc_1(A_1760,B_1761,C_1762,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7375])).

tff(c_7366,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5181])).

tff(c_7387,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7366,c_5182,c_32])).

tff(c_7452,plain,(
    ! [B_1779,F_1776,E_1775,D_1777,C_1778,A_1780] :
      ( E_1775 = B_1779
      | k3_zfmisc_1(A_1780,B_1779,C_1778) = k1_xboole_0
      | k3_zfmisc_1(D_1777,E_1775,F_1776) != k3_zfmisc_1(A_1780,B_1779,C_1778) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8247,plain,(
    ! [B_1872,A_1869,B_1871,C_1875,C_1870,C_1874,A_1873] :
      ( C_1875 = B_1872
      | k3_zfmisc_1(A_1873,B_1872,C_1870) = k1_xboole_0
      | k4_zfmisc_1(A_1869,B_1871,C_1875,C_1874) != k3_zfmisc_1(A_1873,B_1872,C_1870) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7404,c_7452])).

tff(c_8552,plain,(
    ! [B_1895,A_1896,C_1897] :
      ( B_1895 = '#skF_7'
      | k3_zfmisc_1(A_1896,B_1895,C_1897) = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_1896,B_1895,C_1897) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7387,c_8247])).

tff(c_8576,plain,(
    ! [C_1762,A_1760,B_1761,C_3] :
      ( C_1762 = '#skF_7'
      | k3_zfmisc_1(k2_zfmisc_1(A_1760,B_1761),C_1762,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1760,B_1761,C_1762,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7404,c_8552])).

tff(c_8584,plain,(
    ! [C_1762,A_1760,B_1761,C_3] :
      ( C_1762 = '#skF_7'
      | k4_zfmisc_1(A_1760,B_1761,C_1762,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1760,B_1761,C_1762,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7404,c_8576])).

tff(c_9059,plain,
    ( '#skF_7' = '#skF_3'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8584])).

tff(c_9060,plain,(
    '#skF_7' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_9059])).

tff(c_9095,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9060,c_7387])).

tff(c_7564,plain,(
    ! [D_1794,E_1792,C_1795,F_1793,B_1796,A_1797] :
      ( D_1794 = A_1797
      | k3_zfmisc_1(A_1797,B_1796,C_1795) = k1_xboole_0
      | k3_zfmisc_1(D_1794,E_1792,F_1793) != k3_zfmisc_1(A_1797,B_1796,C_1795) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7576,plain,(
    ! [D_1794,E_1792,C_3,A_1760,F_1793,C_1762,B_1761] :
      ( k2_zfmisc_1(A_1760,B_1761) = D_1794
      | k3_zfmisc_1(k2_zfmisc_1(A_1760,B_1761),C_1762,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1760,B_1761,C_1762,C_3) != k3_zfmisc_1(D_1794,E_1792,F_1793) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7404,c_7564])).

tff(c_10921,plain,(
    ! [C_2124,F_2120,B_2119,D_2122,E_2121,A_2118,C_2123] :
      ( k2_zfmisc_1(A_2118,B_2119) = D_2122
      | k4_zfmisc_1(A_2118,B_2119,C_2124,C_2123) = k1_xboole_0
      | k4_zfmisc_1(A_2118,B_2119,C_2124,C_2123) != k3_zfmisc_1(D_2122,E_2121,F_2120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7404,c_7576])).

tff(c_10924,plain,(
    ! [D_2122,E_2121,F_2120] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_2122
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2122,E_2121,F_2120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9095,c_10921])).

tff(c_10958,plain,(
    ! [D_2122,E_2121,F_2120] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_2122
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2122,E_2121,F_2120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9095,c_10924])).

tff(c_10966,plain,(
    ! [D_2125,E_2126,F_2127] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_2125
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2125,E_2126,F_2127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_10958])).

tff(c_10981,plain,(
    ! [A_1760,B_1761,C_1762,C_3] :
      ( k2_zfmisc_1(A_1760,B_1761) = k2_zfmisc_1('#skF_1','#skF_6')
      | k4_zfmisc_1(A_1760,B_1761,C_1762,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7404,c_10966])).

tff(c_10985,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10981])).

tff(c_11028,plain,(
    ! [C_3] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_3) = k3_zfmisc_1('#skF_1','#skF_6',C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_10985,c_2])).

tff(c_11051,plain,(
    ! [C_2135] : k3_zfmisc_1('#skF_1','#skF_6',C_2135) = k3_zfmisc_1('#skF_1','#skF_2',C_2135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11028])).

tff(c_14,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] :
      ( E_18 = B_15
      | k3_zfmisc_1(A_14,B_15,C_16) = k1_xboole_0
      | k3_zfmisc_1(D_17,E_18,F_19) != k3_zfmisc_1(A_14,B_15,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11157,plain,(
    ! [B_15,A_14,C_16,C_2135] :
      ( B_15 = '#skF_6'
      | k3_zfmisc_1(A_14,B_15,C_16) = k1_xboole_0
      | k3_zfmisc_1(A_14,B_15,C_16) != k3_zfmisc_1('#skF_1','#skF_2',C_2135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11051,c_14])).

tff(c_11764,plain,(
    ! [C_2135] :
      ( '#skF_6' = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_2',C_2135) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11157])).

tff(c_11765,plain,(
    ! [C_2135] : k3_zfmisc_1('#skF_1','#skF_2',C_2135) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_7371,c_11764])).

tff(c_7392,plain,(
    ! [A_1763,B_1764,C_1765,D_1766] : k2_zfmisc_1(k3_zfmisc_1(A_1763,B_1764,C_1765),D_1766) = k4_zfmisc_1(A_1763,B_1764,C_1765,D_1766) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7398,plain,(
    ! [B_1764,C_3,A_1763,D_1766,C_1765] : k3_zfmisc_1(k3_zfmisc_1(A_1763,B_1764,C_1765),D_1766,C_3) = k2_zfmisc_1(k4_zfmisc_1(A_1763,B_1764,C_1765,D_1766),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_7392,c_2])).

tff(c_7405,plain,(
    ! [A_1767,B_1768,C_1769,C_1770] : k3_zfmisc_1(k2_zfmisc_1(A_1767,B_1768),C_1769,C_1770) = k4_zfmisc_1(A_1767,B_1768,C_1769,C_1770) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7375])).

tff(c_7420,plain,(
    ! [C_1769,B_2,C_3,A_1,C_1770] : k4_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_1769,C_1770) = k3_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),C_1769,C_1770) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7405])).

tff(c_7492,plain,(
    ! [B_1788,C_1787,C_1789,C_1786,A_1790] : k4_zfmisc_1(k2_zfmisc_1(A_1790,B_1788),C_1789,C_1786,C_1787) = k2_zfmisc_1(k4_zfmisc_1(A_1790,B_1788,C_1789,C_1786),C_1787) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7398,c_7420])).

tff(c_7506,plain,(
    ! [A_1790,B_1788,C_1789,C_1787] : k2_zfmisc_1(k4_zfmisc_1(A_1790,B_1788,C_1789,k1_xboole_0),C_1787) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7492,c_22])).

tff(c_7533,plain,(
    ! [C_1787] : k2_zfmisc_1(k1_xboole_0,C_1787) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_7506])).

tff(c_7539,plain,(
    ! [C_1791] : k2_zfmisc_1(k1_xboole_0,C_1791) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_7506])).

tff(c_7550,plain,(
    ! [C_1791,C_3] : k3_zfmisc_1(k1_xboole_0,C_1791,C_3) = k2_zfmisc_1(k1_xboole_0,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_7539,c_2])).

tff(c_7556,plain,(
    ! [C_1791,C_3] : k3_zfmisc_1(k1_xboole_0,C_1791,C_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7533,c_7550])).

tff(c_7838,plain,(
    ! [A_1826,B_1828,C_1829,D_1830,F_1825,E_1827] :
      ( E_1827 = B_1828
      | k1_xboole_0 = C_1829
      | k1_xboole_0 = B_1828
      | k1_xboole_0 = A_1826
      | k3_zfmisc_1(D_1830,E_1827,F_1825) != k3_zfmisc_1(A_1826,B_1828,C_1829) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7853,plain,(
    ! [C_1791,B_1828,C_1829,A_1826] :
      ( C_1791 = B_1828
      | k1_xboole_0 = C_1829
      | k1_xboole_0 = B_1828
      | k1_xboole_0 = A_1826
      | k3_zfmisc_1(A_1826,B_1828,C_1829) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7556,c_7838])).

tff(c_11125,plain,(
    ! [C_1791,C_2135] :
      ( C_1791 = '#skF_6'
      | k1_xboole_0 = C_2135
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1('#skF_1','#skF_2',C_2135) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11051,c_7853])).

tff(c_11375,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11125])).

tff(c_11415,plain,(
    ! [C_1787] : k2_zfmisc_1('#skF_1',C_1787) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11375,c_11375,c_7533])).

tff(c_9855,plain,(
    ! [C_2037,C_2036,C_2035,B_2033,A_2034] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_2034,B_2033,C_2037,C_2036),C_2035) != k1_xboole_0
      | k1_xboole_0 = C_2035
      | k1_xboole_0 = C_2036
      | k1_xboole_0 = C_2037
      | k2_zfmisc_1(A_2034,B_2033) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7492,c_18])).

tff(c_9858,plain,(
    ! [C_2035] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_2035) != k1_xboole_0
      | k1_xboole_0 = C_2035
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9095,c_9855])).

tff(c_9895,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9858])).

tff(c_9902,plain,(
    ! [C_1762,C_3] : k4_zfmisc_1('#skF_1','#skF_6',C_1762,C_3) = k3_zfmisc_1(k1_xboole_0,C_1762,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_9895,c_7404])).

tff(c_9909,plain,(
    ! [C_1762,C_3] : k4_zfmisc_1('#skF_1','#skF_6',C_1762,C_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7556,c_9902])).

tff(c_10028,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9909,c_9095])).

tff(c_10030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_10028])).

tff(c_10032,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9858])).

tff(c_11018,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10985,c_10032])).

tff(c_11378,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11375,c_11018])).

tff(c_11471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11415,c_11378])).

tff(c_11472,plain,(
    ! [C_2135,C_1791] :
      ( k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = C_2135
      | k3_zfmisc_1('#skF_1','#skF_2',C_2135) != k1_xboole_0
      | C_1791 = '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_11125])).

tff(c_11474,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11472])).

tff(c_11511,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11474,c_11018])).

tff(c_7636,plain,(
    ! [A_1806,B_1807,C_1808,C_1809] : k2_zfmisc_1(k4_zfmisc_1(A_1806,B_1807,C_1808,C_1809),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7492,c_20])).

tff(c_7647,plain,(
    ! [C_3,C_1808,A_1806,C_1809,B_1807] : k3_zfmisc_1(k4_zfmisc_1(A_1806,B_1807,C_1808,C_1809),k1_xboole_0,C_3) = k2_zfmisc_1(k1_xboole_0,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_7636,c_2])).

tff(c_7665,plain,(
    ! [C_3,C_1808,A_1806,C_1809,B_1807] : k3_zfmisc_1(k4_zfmisc_1(A_1806,B_1807,C_1808,C_1809),k1_xboole_0,C_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7533,c_7647])).

tff(c_7951,plain,(
    ! [B_1840,E_1839,D_1842,C_1841,F_1837,A_1838] :
      ( F_1837 = C_1841
      | k1_xboole_0 = C_1841
      | k1_xboole_0 = B_1840
      | k1_xboole_0 = A_1838
      | k3_zfmisc_1(D_1842,E_1839,F_1837) != k3_zfmisc_1(A_1838,B_1840,C_1841) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8080,plain,(
    ! [C_1850,C_1849,B_1851,A_1852] :
      ( C_1850 = C_1849
      | k1_xboole_0 = C_1850
      | k1_xboole_0 = B_1851
      | k1_xboole_0 = A_1852
      | k3_zfmisc_1(A_1852,B_1851,C_1850) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7665,c_7951])).

tff(c_8771,plain,(
    ! [C_1915,B_1913,A_1912,C_1914,C_1916] :
      ( C_1915 = C_1914
      | k1_xboole_0 = C_1915
      | k1_xboole_0 = C_1916
      | k2_zfmisc_1(A_1912,B_1913) = k1_xboole_0
      | k4_zfmisc_1(A_1912,B_1913,C_1916,C_1915) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7404,c_8080])).

tff(c_8792,plain,(
    ! [D_23,C_1914,C_22,A_20] :
      ( D_23 = C_1914
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8771])).

tff(c_8851,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8792])).

tff(c_11535,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11474,c_11474,c_8851])).

tff(c_11600,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11535,c_10985])).

tff(c_11602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11511,c_11600])).

tff(c_11603,plain,(
    ! [C_1791,C_2135] :
      ( C_1791 = '#skF_6'
      | k1_xboole_0 = C_2135
      | k3_zfmisc_1('#skF_1','#skF_2',C_2135) != k1_xboole_0 ) ),
    inference(splitRight,[status(thm)],[c_11472])).

tff(c_11638,plain,(
    ! [C_2135] :
      ( k1_xboole_0 = C_2135
      | k3_zfmisc_1('#skF_1','#skF_2',C_2135) != k1_xboole_0 ) ),
    inference(splitLeft,[status(thm)],[c_11603])).

tff(c_11955,plain,(
    ! [C_2199] : k1_xboole_0 = C_2199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11765,c_11638])).

tff(c_12077,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_11955,c_11018])).

tff(c_12127,plain,(
    ! [C_2468] : C_2468 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11603])).

tff(c_11604,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11472])).

tff(c_12457,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_12127,c_11604])).

tff(c_12458,plain,(
    ! [D_23,C_1914,C_22] :
      ( D_23 = C_1914
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22 ) ),
    inference(splitRight,[status(thm)],[c_8792])).

tff(c_12460,plain,(
    ! [C_3144] : k1_xboole_0 = C_3144 ),
    inference(splitLeft,[status(thm)],[c_12458])).

tff(c_12506,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12460,c_7387])).

tff(c_12538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_12506])).

tff(c_12539,plain,(
    ! [D_23,C_1914] :
      ( D_23 = C_1914
      | k1_xboole_0 = D_23 ) ),
    inference(splitRight,[status(thm)],[c_12458])).

tff(c_19138,plain,(
    ! [D_4186] : k1_xboole_0 = D_4186 ),
    inference(factorization,[status(thm),theory(equality)],[c_12539])).

tff(c_19214,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_19138,c_30])).

tff(c_19215,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7365])).

tff(c_19221,plain,(
    ! [A_4304,B_4305,C_4306] : k2_zfmisc_1(k2_zfmisc_1(A_4304,B_4305),C_4306) = k3_zfmisc_1(A_4304,B_4305,C_4306) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_19230,plain,(
    ! [A_1,B_2,C_3,C_4306] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_4306) = k2_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),C_4306) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19221])).

tff(c_19253,plain,(
    ! [A_1,B_2,C_3,C_4306] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_4306) = k4_zfmisc_1(A_1,B_2,C_3,C_4306) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_19230])).

tff(c_19216,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7365])).

tff(c_19236,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19216,c_5182,c_7366,c_32])).

tff(c_19592,plain,(
    ! [B_4362,A_4363,F_4359,C_4361,E_4358,D_4360] :
      ( E_4358 = B_4362
      | k3_zfmisc_1(A_4363,B_4362,C_4361) = k1_xboole_0
      | k3_zfmisc_1(D_4360,E_4358,F_4359) != k3_zfmisc_1(A_4363,B_4362,C_4361) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20522,plain,(
    ! [C_4452,A_4447,C_4449,A_4450,B_4451,B_4448,C_4446] :
      ( C_4449 = B_4451
      | k3_zfmisc_1(A_4447,B_4451,C_4446) = k1_xboole_0
      | k4_zfmisc_1(A_4450,B_4448,C_4449,C_4452) != k3_zfmisc_1(A_4447,B_4451,C_4446) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19253,c_19592])).

tff(c_20583,plain,(
    ! [B_4453,A_4454,C_4455] :
      ( B_4453 = '#skF_7'
      | k3_zfmisc_1(A_4454,B_4453,C_4455) = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_4454,B_4453,C_4455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19236,c_20522])).

tff(c_20610,plain,(
    ! [C_3,A_1,B_2,C_4306] :
      ( C_3 = '#skF_7'
      | k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_4306) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,C_4306) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19253,c_20583])).

tff(c_20619,plain,(
    ! [C_3,A_1,B_2,C_4306] :
      ( C_3 = '#skF_7'
      | k4_zfmisc_1(A_1,B_2,C_3,C_4306) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,C_4306) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19253,c_20610])).

tff(c_20647,plain,
    ( '#skF_7' = '#skF_3'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_20619])).

tff(c_20649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_19215,c_20647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:45:24 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.12/3.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.17/3.21  
% 9.17/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.17/3.21  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 9.17/3.21  
% 9.17/3.21  %Foreground sorts:
% 9.17/3.21  
% 9.17/3.21  
% 9.17/3.21  %Background operators:
% 9.17/3.21  
% 9.17/3.21  
% 9.17/3.21  %Foreground operators:
% 9.17/3.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.17/3.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.17/3.21  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 9.17/3.21  tff('#skF_7', type, '#skF_7': $i).
% 9.17/3.21  tff('#skF_5', type, '#skF_5': $i).
% 9.17/3.21  tff('#skF_6', type, '#skF_6': $i).
% 9.17/3.21  tff('#skF_2', type, '#skF_2': $i).
% 9.17/3.21  tff('#skF_3', type, '#skF_3': $i).
% 9.17/3.21  tff('#skF_1', type, '#skF_1': $i).
% 9.17/3.21  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.17/3.21  tff('#skF_8', type, '#skF_8': $i).
% 9.17/3.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.17/3.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.17/3.21  tff('#skF_4', type, '#skF_4': $i).
% 9.17/3.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.17/3.21  
% 9.33/3.25  tff(f_81, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 9.33/3.25  tff(f_27, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.33/3.25  tff(f_29, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 9.33/3.25  tff(f_53, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 9.33/3.25  tff(f_68, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 9.33/3.25  tff(f_43, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 9.33/3.25  tff(c_30, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.33/3.25  tff(c_28, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.33/3.25  tff(c_109, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_28])).
% 9.33/3.25  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3)=k3_zfmisc_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.33/3.25  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_zfmisc_1(k3_zfmisc_1(A_4, B_5, C_6), D_7)=k4_zfmisc_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.33/3.25  tff(c_110, plain, (![A_36, B_37, C_38]: (k2_zfmisc_1(k2_zfmisc_1(A_36, B_37), C_38)=k3_zfmisc_1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.33/3.25  tff(c_113, plain, (![A_36, B_37, C_38, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_36, B_37), C_38, C_3)=k2_zfmisc_1(k3_zfmisc_1(A_36, B_37, C_38), C_3))), inference(superposition, [status(thm), theory('equality')], [c_110, c_2])).
% 9.33/3.25  tff(c_141, plain, (![A_36, B_37, C_38, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_36, B_37), C_38, C_3)=k4_zfmisc_1(A_36, B_37, C_38, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_113])).
% 9.33/3.25  tff(c_32, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.33/3.25  tff(c_387, plain, (![A_85, E_80, F_81, B_84, C_83, D_82]: (F_81=C_83 | k3_zfmisc_1(A_85, B_84, C_83)=k1_xboole_0 | k3_zfmisc_1(D_82, E_80, F_81)!=k3_zfmisc_1(A_85, B_84, C_83))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_1068, plain, (![C_152, C_155, C_156, B_153, A_157, A_151, B_154]: (C_155=C_152 | k3_zfmisc_1(A_157, B_154, C_152)=k1_xboole_0 | k4_zfmisc_1(A_151, B_153, C_156, C_155)!=k3_zfmisc_1(A_157, B_154, C_152))), inference(superposition, [status(thm), theory('equality')], [c_141, c_387])).
% 9.33/3.25  tff(c_1506, plain, (![C_188, A_189, B_190]: (C_188='#skF_8' | k3_zfmisc_1(A_189, B_190, C_188)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_189, B_190, C_188))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1068])).
% 9.33/3.25  tff(c_1533, plain, (![C_3, A_36, B_37, C_38]: (C_3='#skF_8' | k3_zfmisc_1(k2_zfmisc_1(A_36, B_37), C_38, C_3)=k1_xboole_0 | k4_zfmisc_1(A_36, B_37, C_38, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_1506])).
% 9.33/3.25  tff(c_1542, plain, (![C_3, A_36, B_37, C_38]: (C_3='#skF_8' | k4_zfmisc_1(A_36, B_37, C_38, C_3)=k1_xboole_0 | k4_zfmisc_1(A_36, B_37, C_38, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_1533])).
% 9.33/3.25  tff(c_2212, plain, ('#skF_8'='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_1542])).
% 9.33/3.25  tff(c_2213, plain, ('#skF_8'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_30, c_2212])).
% 9.33/3.25  tff(c_260, plain, (![D_63, E_61, A_66, C_64, B_65, F_62]: (E_61=B_65 | k3_zfmisc_1(A_66, B_65, C_64)=k1_xboole_0 | k3_zfmisc_1(D_63, E_61, F_62)!=k3_zfmisc_1(A_66, B_65, C_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_1410, plain, (![A_181, B_178, C_184, C_183, B_182, A_180, C_179]: (C_184=B_178 | k3_zfmisc_1(A_181, B_178, C_179)=k1_xboole_0 | k4_zfmisc_1(A_180, B_182, C_184, C_183)!=k3_zfmisc_1(A_181, B_178, C_179))), inference(superposition, [status(thm), theory('equality')], [c_141, c_260])).
% 9.33/3.25  tff(c_1469, plain, (![B_185, A_186, C_187]: (B_185='#skF_7' | k3_zfmisc_1(A_186, B_185, C_187)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_186, B_185, C_187))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1410])).
% 9.33/3.25  tff(c_1496, plain, (![C_38, A_36, B_37, C_3]: (C_38='#skF_7' | k3_zfmisc_1(k2_zfmisc_1(A_36, B_37), C_38, C_3)=k1_xboole_0 | k4_zfmisc_1(A_36, B_37, C_38, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_1469])).
% 9.33/3.25  tff(c_1505, plain, (![C_38, A_36, B_37, C_3]: (C_38='#skF_7' | k4_zfmisc_1(A_36, B_37, C_38, C_3)=k1_xboole_0 | k4_zfmisc_1(A_36, B_37, C_38, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_1496])).
% 9.33/3.25  tff(c_1546, plain, ('#skF_7'='#skF_3' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_1505])).
% 9.33/3.25  tff(c_1547, plain, ('#skF_7'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_1546])).
% 9.33/3.25  tff(c_1582, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_32])).
% 9.33/3.25  tff(c_2247, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2213, c_1582])).
% 9.33/3.25  tff(c_300, plain, (![D_70, B_72, E_68, C_71, A_73, F_69]: (D_70=A_73 | k3_zfmisc_1(A_73, B_72, C_71)=k1_xboole_0 | k3_zfmisc_1(D_70, E_68, F_69)!=k3_zfmisc_1(A_73, B_72, C_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_312, plain, (![D_70, A_36, C_3, E_68, C_38, F_69, B_37]: (k2_zfmisc_1(A_36, B_37)=D_70 | k3_zfmisc_1(k2_zfmisc_1(A_36, B_37), C_38, C_3)=k1_xboole_0 | k4_zfmisc_1(A_36, B_37, C_38, C_3)!=k3_zfmisc_1(D_70, E_68, F_69))), inference(superposition, [status(thm), theory('equality')], [c_141, c_300])).
% 9.33/3.25  tff(c_3680, plain, (![D_372, B_368, E_371, A_367, F_373, C_369, C_370]: (k2_zfmisc_1(A_367, B_368)=D_372 | k4_zfmisc_1(A_367, B_368, C_370, C_369)=k1_xboole_0 | k4_zfmisc_1(A_367, B_368, C_370, C_369)!=k3_zfmisc_1(D_372, E_371, F_373))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_312])).
% 9.33/3.25  tff(c_3683, plain, (![D_372, E_371, F_373]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_372 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_372, E_371, F_373))), inference(superposition, [status(thm), theory('equality')], [c_2247, c_3680])).
% 9.33/3.25  tff(c_3717, plain, (![D_372, E_371, F_373]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_372 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_372, E_371, F_373))), inference(demodulation, [status(thm), theory('equality')], [c_2247, c_3683])).
% 9.33/3.25  tff(c_3732, plain, (![D_375, E_376, F_377]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_375 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_375, E_376, F_377))), inference(negUnitSimplification, [status(thm)], [c_30, c_3717])).
% 9.33/3.25  tff(c_3747, plain, (![A_36, B_37, C_38, C_3]: (k2_zfmisc_1(A_36, B_37)=k2_zfmisc_1('#skF_5', '#skF_6') | k4_zfmisc_1(A_36, B_37, C_38, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_3732])).
% 9.33/3.25  tff(c_3751, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_3747])).
% 9.33/3.25  tff(c_3829, plain, (![C_3]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_3)=k3_zfmisc_1('#skF_5', '#skF_6', C_3))), inference(superposition, [status(thm), theory('equality')], [c_3751, c_2])).
% 9.33/3.25  tff(c_3836, plain, (![C_387]: (k3_zfmisc_1('#skF_5', '#skF_6', C_387)=k3_zfmisc_1('#skF_1', '#skF_2', C_387))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3829])).
% 9.33/3.25  tff(c_16, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (D_17=A_14 | k3_zfmisc_1(A_14, B_15, C_16)=k1_xboole_0 | k3_zfmisc_1(D_17, E_18, F_19)!=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_3918, plain, (![A_14, B_15, C_16, C_387]: (A_14='#skF_5' | k3_zfmisc_1(A_14, B_15, C_16)=k1_xboole_0 | k3_zfmisc_1(A_14, B_15, C_16)!=k3_zfmisc_1('#skF_1', '#skF_2', C_387))), inference(superposition, [status(thm), theory('equality')], [c_3836, c_16])).
% 9.33/3.25  tff(c_4380, plain, (![C_387]: ('#skF_5'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_2', C_387)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_3918])).
% 9.33/3.25  tff(c_4381, plain, (![C_387]: (k3_zfmisc_1('#skF_1', '#skF_2', C_387)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_109, c_4380])).
% 9.33/3.25  tff(c_20, plain, (![A_20, B_21, C_22]: (k4_zfmisc_1(A_20, B_21, C_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.33/3.25  tff(c_142, plain, (![A_43, B_44, C_45, C_46]: (k3_zfmisc_1(k2_zfmisc_1(A_43, B_44), C_45, C_46)=k4_zfmisc_1(A_43, B_44, C_45, C_46))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_113])).
% 9.33/3.25  tff(c_209, plain, (![B_59, C_56, A_58, C_57, D_60]: (k4_zfmisc_1(k2_zfmisc_1(A_58, B_59), C_56, C_57, D_60)=k2_zfmisc_1(k4_zfmisc_1(A_58, B_59, C_56, C_57), D_60))), inference(superposition, [status(thm), theory('equality')], [c_142, c_4])).
% 9.33/3.25  tff(c_22, plain, (![A_20, B_21, D_23]: (k4_zfmisc_1(A_20, B_21, k1_xboole_0, D_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.33/3.25  tff(c_223, plain, (![A_58, B_59, C_56, D_60]: (k2_zfmisc_1(k4_zfmisc_1(A_58, B_59, C_56, k1_xboole_0), D_60)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_22])).
% 9.33/3.25  tff(c_250, plain, (![D_60]: (k2_zfmisc_1(k1_xboole_0, D_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_223])).
% 9.33/3.25  tff(c_346, plain, (![A_76, B_77, B_78, C_79]: (k2_zfmisc_1(k4_zfmisc_1(A_76, B_77, B_78, C_79), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_209])).
% 9.33/3.25  tff(c_357, plain, (![B_77, A_76, B_78, C_3, C_79]: (k3_zfmisc_1(k4_zfmisc_1(A_76, B_77, B_78, C_79), k1_xboole_0, C_3)=k2_zfmisc_1(k1_xboole_0, C_3))), inference(superposition, [status(thm), theory('equality')], [c_346, c_2])).
% 9.33/3.25  tff(c_375, plain, (![B_77, A_76, B_78, C_3, C_79]: (k3_zfmisc_1(k4_zfmisc_1(A_76, B_77, B_78, C_79), k1_xboole_0, C_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_357])).
% 9.33/3.25  tff(c_800, plain, (![C_126, D_127, B_125, A_123, E_124, F_122]: (F_122=C_126 | k1_xboole_0=C_126 | k1_xboole_0=B_125 | k1_xboole_0=A_123 | k3_zfmisc_1(D_127, E_124, F_122)!=k3_zfmisc_1(A_123, B_125, C_126))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.33/3.25  tff(c_821, plain, (![C_3, C_126, B_125, A_123]: (C_3=C_126 | k1_xboole_0=C_126 | k1_xboole_0=B_125 | k1_xboole_0=A_123 | k3_zfmisc_1(A_123, B_125, C_126)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_375, c_800])).
% 9.33/3.25  tff(c_3895, plain, (![C_387, C_3]: (C_387=C_3 | k1_xboole_0=C_387 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k3_zfmisc_1('#skF_1', '#skF_2', C_387)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3836, c_821])).
% 9.33/3.25  tff(c_4151, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3895])).
% 9.33/3.25  tff(c_275, plain, (![D_67]: (k2_zfmisc_1(k1_xboole_0, D_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_223])).
% 9.33/3.25  tff(c_286, plain, (![D_67, C_3]: (k3_zfmisc_1(k1_xboole_0, D_67, C_3)=k2_zfmisc_1(k1_xboole_0, C_3))), inference(superposition, [status(thm), theory('equality')], [c_275, c_2])).
% 9.33/3.25  tff(c_292, plain, (![D_67, C_3]: (k3_zfmisc_1(k1_xboole_0, D_67, C_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_286])).
% 9.33/3.25  tff(c_18, plain, (![A_20, B_21, C_22, D_23]: (k4_zfmisc_1(A_20, B_21, C_22, D_23)!=k1_xboole_0 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.33/3.25  tff(c_2650, plain, (![C_306, A_307, D_309, B_305, C_308]: (k2_zfmisc_1(k4_zfmisc_1(A_307, B_305, C_306, C_308), D_309)!=k1_xboole_0 | k1_xboole_0=D_309 | k1_xboole_0=C_308 | k1_xboole_0=C_306 | k2_zfmisc_1(A_307, B_305)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_18])).
% 9.33/3.25  tff(c_2653, plain, (![D_309]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), D_309)!=k1_xboole_0 | k1_xboole_0=D_309 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2247, c_2650])).
% 9.33/3.25  tff(c_2745, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2653])).
% 9.33/3.25  tff(c_2752, plain, (![C_38, C_3]: (k4_zfmisc_1('#skF_5', '#skF_6', C_38, C_3)=k3_zfmisc_1(k1_xboole_0, C_38, C_3))), inference(superposition, [status(thm), theory('equality')], [c_2745, c_141])).
% 9.33/3.25  tff(c_2759, plain, (![C_38, C_3]: (k4_zfmisc_1('#skF_5', '#skF_6', C_38, C_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_292, c_2752])).
% 9.33/3.25  tff(c_2878, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2759, c_2247])).
% 9.33/3.25  tff(c_2880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2878])).
% 9.33/3.25  tff(c_2882, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2653])).
% 9.33/3.25  tff(c_3819, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3751, c_2882])).
% 9.33/3.25  tff(c_4155, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4151, c_3819])).
% 9.33/3.25  tff(c_4186, plain, (![D_60]: (k2_zfmisc_1('#skF_5', D_60)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4151, c_4151, c_250])).
% 9.33/3.25  tff(c_4199, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4186, c_3751])).
% 9.33/3.25  tff(c_4217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4155, c_4199])).
% 9.33/3.25  tff(c_4219, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_3895])).
% 9.33/3.25  tff(c_4218, plain, (![C_387, C_3]: (k1_xboole_0='#skF_6' | C_387=C_3 | k1_xboole_0=C_387 | k3_zfmisc_1('#skF_1', '#skF_2', C_387)!=k1_xboole_0)), inference(splitRight, [status(thm)], [c_3895])).
% 9.33/3.25  tff(c_4253, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_4218])).
% 9.33/3.25  tff(c_4258, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4253, c_3819])).
% 9.33/3.25  tff(c_24, plain, (![A_20, C_22, D_23]: (k4_zfmisc_1(A_20, k1_xboole_0, C_22, D_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.33/3.25  tff(c_574, plain, (![B_104, A_102, C_105, F_101, E_103, D_106]: (E_103=B_104 | k1_xboole_0=C_105 | k1_xboole_0=B_104 | k1_xboole_0=A_102 | k3_zfmisc_1(D_106, E_103, F_101)!=k3_zfmisc_1(A_102, B_104, C_105))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.33/3.25  tff(c_764, plain, (![B_119, C_120, A_121]: (k1_xboole_0=B_119 | k1_xboole_0=C_120 | k1_xboole_0=B_119 | k1_xboole_0=A_121 | k3_zfmisc_1(A_121, B_119, C_120)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_375, c_574])).
% 9.33/3.25  tff(c_1627, plain, (![C_195, C_196, A_197, B_198]: (k1_xboole_0=C_195 | k1_xboole_0=C_196 | k1_xboole_0=C_195 | k2_zfmisc_1(A_197, B_198)=k1_xboole_0 | k4_zfmisc_1(A_197, B_198, C_195, C_196)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_141, c_764])).
% 9.33/3.25  tff(c_1655, plain, (![D_23, C_22, A_20]: (k1_xboole_0=D_23 | k1_xboole_0=C_22 | k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_1627])).
% 9.33/3.25  tff(c_1658, plain, (![A_20]: (k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1655])).
% 9.33/3.25  tff(c_4278, plain, (![A_20]: (k2_zfmisc_1(A_20, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4253, c_4253, c_1658])).
% 9.33/3.25  tff(c_4319, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4278, c_3751])).
% 9.33/3.25  tff(c_4321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4258, c_4319])).
% 9.33/3.25  tff(c_4323, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_4218])).
% 9.33/3.25  tff(c_589, plain, (![D_67, B_104, C_105, A_102]: (D_67=B_104 | k1_xboole_0=C_105 | k1_xboole_0=B_104 | k1_xboole_0=A_102 | k3_zfmisc_1(A_102, B_104, C_105)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_292, c_574])).
% 9.33/3.25  tff(c_3897, plain, (![D_67, C_387]: (D_67='#skF_6' | k1_xboole_0=C_387 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k3_zfmisc_1('#skF_1', '#skF_2', C_387)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3836, c_589])).
% 9.33/3.25  tff(c_4330, plain, (![D_67, C_387]: (D_67='#skF_6' | k1_xboole_0=C_387 | k3_zfmisc_1('#skF_1', '#skF_2', C_387)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_4219, c_4323, c_3897])).
% 9.33/3.25  tff(c_4331, plain, (![C_387]: (k1_xboole_0=C_387 | k3_zfmisc_1('#skF_1', '#skF_2', C_387)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4330])).
% 9.33/3.25  tff(c_4542, plain, (![C_426]: (k1_xboole_0=C_426)), inference(demodulation, [status(thm), theory('equality')], [c_4381, c_4331])).
% 9.33/3.25  tff(c_4664, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4542, c_3819])).
% 9.33/3.25  tff(c_4667, plain, (![D_697]: (D_697='#skF_6')), inference(splitRight, [status(thm)], [c_4330])).
% 9.33/3.25  tff(c_4978, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4667, c_4323])).
% 9.33/3.25  tff(c_4979, plain, (![D_23, C_22]: (k1_xboole_0=D_23 | k1_xboole_0=C_22)), inference(splitRight, [status(thm)], [c_1655])).
% 9.33/3.25  tff(c_4981, plain, (![C_1319]: (k1_xboole_0=C_1319)), inference(splitLeft, [status(thm)], [c_4979])).
% 9.33/3.25  tff(c_5007, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4981, c_1582])).
% 9.33/3.25  tff(c_5059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_5007])).
% 9.33/3.25  tff(c_5104, plain, (![D_1432]: (k1_xboole_0=D_1432)), inference(splitRight, [status(thm)], [c_4979])).
% 9.33/3.25  tff(c_5180, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5104, c_30])).
% 9.33/3.25  tff(c_5181, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 9.33/3.25  tff(c_5187, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_5181])).
% 9.33/3.25  tff(c_5188, plain, (![A_1541, B_1542, C_1543]: (k2_zfmisc_1(k2_zfmisc_1(A_1541, B_1542), C_1543)=k3_zfmisc_1(A_1541, B_1542, C_1543))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.33/3.25  tff(c_5197, plain, (![A_1, B_2, C_3, C_1543]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_1543)=k2_zfmisc_1(k3_zfmisc_1(A_1, B_2, C_3), C_1543))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5188])).
% 9.33/3.25  tff(c_5220, plain, (![A_1, B_2, C_3, C_1543]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_1543)=k4_zfmisc_1(A_1, B_2, C_3, C_1543))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_5197])).
% 9.33/3.25  tff(c_5182, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_28])).
% 9.33/3.25  tff(c_5203, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5182, c_32])).
% 9.33/3.25  tff(c_5559, plain, (![B_1599, C_1598, A_1600, D_1597, E_1595, F_1596]: (E_1595=B_1599 | k3_zfmisc_1(A_1600, B_1599, C_1598)=k1_xboole_0 | k3_zfmisc_1(D_1597, E_1595, F_1596)!=k3_zfmisc_1(A_1600, B_1599, C_1598))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_6489, plain, (![C_1687, C_1683, C_1684, A_1688, B_1685, A_1689, B_1686]: (C_1687=B_1685 | k3_zfmisc_1(A_1689, B_1685, C_1683)=k1_xboole_0 | k4_zfmisc_1(A_1688, B_1686, C_1687, C_1684)!=k3_zfmisc_1(A_1689, B_1685, C_1683))), inference(superposition, [status(thm), theory('equality')], [c_5220, c_5559])).
% 9.33/3.25  tff(c_6587, plain, (![B_1693, A_1694, C_1695]: (B_1693='#skF_7' | k3_zfmisc_1(A_1694, B_1693, C_1695)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_1694, B_1693, C_1695))), inference(superposition, [status(thm), theory('equality')], [c_5203, c_6489])).
% 9.33/3.25  tff(c_6614, plain, (![C_3, A_1, B_2, C_1543]: (C_3='#skF_7' | k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_1543)=k1_xboole_0 | k4_zfmisc_1(A_1, B_2, C_3, C_1543)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5220, c_6587])).
% 9.33/3.25  tff(c_6623, plain, (![C_3, A_1, B_2, C_1543]: (C_3='#skF_7' | k4_zfmisc_1(A_1, B_2, C_3, C_1543)=k1_xboole_0 | k4_zfmisc_1(A_1, B_2, C_3, C_1543)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5220, c_6614])).
% 9.33/3.25  tff(c_6650, plain, ('#skF_7'='#skF_3' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_6623])).
% 9.33/3.25  tff(c_6651, plain, ('#skF_7'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_6650])).
% 9.33/3.25  tff(c_6686, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6651, c_5203])).
% 9.33/3.25  tff(c_5402, plain, (![E_1575, A_1580, D_1577, F_1576, C_1578, B_1579]: (F_1576=C_1578 | k3_zfmisc_1(A_1580, B_1579, C_1578)=k1_xboole_0 | k3_zfmisc_1(D_1577, E_1575, F_1576)!=k3_zfmisc_1(A_1580, B_1579, C_1578))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_5420, plain, (![C_1543, E_1575, B_2, C_3, A_1, D_1577, F_1576]: (F_1576=C_1543 | k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_1543)=k1_xboole_0 | k4_zfmisc_1(A_1, B_2, C_3, C_1543)!=k3_zfmisc_1(D_1577, E_1575, F_1576))), inference(superposition, [status(thm), theory('equality')], [c_5220, c_5402])).
% 9.33/3.25  tff(c_7256, plain, (![E_1749, B_1744, C_1746, C_1743, A_1747, F_1745, D_1748]: (F_1745=C_1743 | k4_zfmisc_1(A_1747, B_1744, C_1746, C_1743)=k1_xboole_0 | k4_zfmisc_1(A_1747, B_1744, C_1746, C_1743)!=k3_zfmisc_1(D_1748, E_1749, F_1745))), inference(demodulation, [status(thm), theory('equality')], [c_5220, c_5420])).
% 9.33/3.25  tff(c_7265, plain, (![F_1745, D_1748, E_1749]: (F_1745='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1748, E_1749, F_1745))), inference(superposition, [status(thm), theory('equality')], [c_6686, c_7256])).
% 9.33/3.25  tff(c_7293, plain, (![F_1745, D_1748, E_1749]: (F_1745='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1748, E_1749, F_1745))), inference(demodulation, [status(thm), theory('equality')], [c_6686, c_7265])).
% 9.33/3.25  tff(c_7317, plain, (![F_1753, D_1754, E_1755]: (F_1753='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1754, E_1755, F_1753))), inference(negUnitSimplification, [status(thm)], [c_30, c_7293])).
% 9.33/3.25  tff(c_7332, plain, (![C_1543, A_1, B_2, C_3]: (C_1543='#skF_8' | k4_zfmisc_1(A_1, B_2, C_3, C_1543)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5220, c_7317])).
% 9.33/3.25  tff(c_7362, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_7332])).
% 9.33/3.25  tff(c_7364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5187, c_7362])).
% 9.33/3.25  tff(c_7365, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_5181])).
% 9.33/3.25  tff(c_7371, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_7365])).
% 9.33/3.25  tff(c_7372, plain, (![A_1760, B_1761, C_1762]: (k2_zfmisc_1(k2_zfmisc_1(A_1760, B_1761), C_1762)=k3_zfmisc_1(A_1760, B_1761, C_1762))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.33/3.25  tff(c_7375, plain, (![A_1760, B_1761, C_1762, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_1760, B_1761), C_1762, C_3)=k2_zfmisc_1(k3_zfmisc_1(A_1760, B_1761, C_1762), C_3))), inference(superposition, [status(thm), theory('equality')], [c_7372, c_2])).
% 9.33/3.25  tff(c_7404, plain, (![A_1760, B_1761, C_1762, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_1760, B_1761), C_1762, C_3)=k4_zfmisc_1(A_1760, B_1761, C_1762, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7375])).
% 9.33/3.25  tff(c_7366, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_5181])).
% 9.33/3.25  tff(c_7387, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7366, c_5182, c_32])).
% 9.33/3.25  tff(c_7452, plain, (![B_1779, F_1776, E_1775, D_1777, C_1778, A_1780]: (E_1775=B_1779 | k3_zfmisc_1(A_1780, B_1779, C_1778)=k1_xboole_0 | k3_zfmisc_1(D_1777, E_1775, F_1776)!=k3_zfmisc_1(A_1780, B_1779, C_1778))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_8247, plain, (![B_1872, A_1869, B_1871, C_1875, C_1870, C_1874, A_1873]: (C_1875=B_1872 | k3_zfmisc_1(A_1873, B_1872, C_1870)=k1_xboole_0 | k4_zfmisc_1(A_1869, B_1871, C_1875, C_1874)!=k3_zfmisc_1(A_1873, B_1872, C_1870))), inference(superposition, [status(thm), theory('equality')], [c_7404, c_7452])).
% 9.33/3.25  tff(c_8552, plain, (![B_1895, A_1896, C_1897]: (B_1895='#skF_7' | k3_zfmisc_1(A_1896, B_1895, C_1897)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_1896, B_1895, C_1897))), inference(superposition, [status(thm), theory('equality')], [c_7387, c_8247])).
% 9.33/3.25  tff(c_8576, plain, (![C_1762, A_1760, B_1761, C_3]: (C_1762='#skF_7' | k3_zfmisc_1(k2_zfmisc_1(A_1760, B_1761), C_1762, C_3)=k1_xboole_0 | k4_zfmisc_1(A_1760, B_1761, C_1762, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7404, c_8552])).
% 9.33/3.25  tff(c_8584, plain, (![C_1762, A_1760, B_1761, C_3]: (C_1762='#skF_7' | k4_zfmisc_1(A_1760, B_1761, C_1762, C_3)=k1_xboole_0 | k4_zfmisc_1(A_1760, B_1761, C_1762, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7404, c_8576])).
% 9.33/3.25  tff(c_9059, plain, ('#skF_7'='#skF_3' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_8584])).
% 9.33/3.25  tff(c_9060, plain, ('#skF_7'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_9059])).
% 9.33/3.25  tff(c_9095, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9060, c_7387])).
% 9.33/3.25  tff(c_7564, plain, (![D_1794, E_1792, C_1795, F_1793, B_1796, A_1797]: (D_1794=A_1797 | k3_zfmisc_1(A_1797, B_1796, C_1795)=k1_xboole_0 | k3_zfmisc_1(D_1794, E_1792, F_1793)!=k3_zfmisc_1(A_1797, B_1796, C_1795))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_7576, plain, (![D_1794, E_1792, C_3, A_1760, F_1793, C_1762, B_1761]: (k2_zfmisc_1(A_1760, B_1761)=D_1794 | k3_zfmisc_1(k2_zfmisc_1(A_1760, B_1761), C_1762, C_3)=k1_xboole_0 | k4_zfmisc_1(A_1760, B_1761, C_1762, C_3)!=k3_zfmisc_1(D_1794, E_1792, F_1793))), inference(superposition, [status(thm), theory('equality')], [c_7404, c_7564])).
% 9.33/3.25  tff(c_10921, plain, (![C_2124, F_2120, B_2119, D_2122, E_2121, A_2118, C_2123]: (k2_zfmisc_1(A_2118, B_2119)=D_2122 | k4_zfmisc_1(A_2118, B_2119, C_2124, C_2123)=k1_xboole_0 | k4_zfmisc_1(A_2118, B_2119, C_2124, C_2123)!=k3_zfmisc_1(D_2122, E_2121, F_2120))), inference(demodulation, [status(thm), theory('equality')], [c_7404, c_7576])).
% 9.33/3.25  tff(c_10924, plain, (![D_2122, E_2121, F_2120]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_2122 | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2122, E_2121, F_2120))), inference(superposition, [status(thm), theory('equality')], [c_9095, c_10921])).
% 9.33/3.25  tff(c_10958, plain, (![D_2122, E_2121, F_2120]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_2122 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2122, E_2121, F_2120))), inference(demodulation, [status(thm), theory('equality')], [c_9095, c_10924])).
% 9.33/3.25  tff(c_10966, plain, (![D_2125, E_2126, F_2127]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_2125 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2125, E_2126, F_2127))), inference(negUnitSimplification, [status(thm)], [c_30, c_10958])).
% 9.33/3.25  tff(c_10981, plain, (![A_1760, B_1761, C_1762, C_3]: (k2_zfmisc_1(A_1760, B_1761)=k2_zfmisc_1('#skF_1', '#skF_6') | k4_zfmisc_1(A_1760, B_1761, C_1762, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7404, c_10966])).
% 9.33/3.25  tff(c_10985, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_10981])).
% 9.33/3.25  tff(c_11028, plain, (![C_3]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_3)=k3_zfmisc_1('#skF_1', '#skF_6', C_3))), inference(superposition, [status(thm), theory('equality')], [c_10985, c_2])).
% 9.33/3.25  tff(c_11051, plain, (![C_2135]: (k3_zfmisc_1('#skF_1', '#skF_6', C_2135)=k3_zfmisc_1('#skF_1', '#skF_2', C_2135))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11028])).
% 9.33/3.25  tff(c_14, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (E_18=B_15 | k3_zfmisc_1(A_14, B_15, C_16)=k1_xboole_0 | k3_zfmisc_1(D_17, E_18, F_19)!=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_11157, plain, (![B_15, A_14, C_16, C_2135]: (B_15='#skF_6' | k3_zfmisc_1(A_14, B_15, C_16)=k1_xboole_0 | k3_zfmisc_1(A_14, B_15, C_16)!=k3_zfmisc_1('#skF_1', '#skF_2', C_2135))), inference(superposition, [status(thm), theory('equality')], [c_11051, c_14])).
% 9.33/3.25  tff(c_11764, plain, (![C_2135]: ('#skF_6'='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_2', C_2135)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_11157])).
% 9.33/3.25  tff(c_11765, plain, (![C_2135]: (k3_zfmisc_1('#skF_1', '#skF_2', C_2135)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_7371, c_11764])).
% 9.33/3.25  tff(c_7392, plain, (![A_1763, B_1764, C_1765, D_1766]: (k2_zfmisc_1(k3_zfmisc_1(A_1763, B_1764, C_1765), D_1766)=k4_zfmisc_1(A_1763, B_1764, C_1765, D_1766))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.33/3.25  tff(c_7398, plain, (![B_1764, C_3, A_1763, D_1766, C_1765]: (k3_zfmisc_1(k3_zfmisc_1(A_1763, B_1764, C_1765), D_1766, C_3)=k2_zfmisc_1(k4_zfmisc_1(A_1763, B_1764, C_1765, D_1766), C_3))), inference(superposition, [status(thm), theory('equality')], [c_7392, c_2])).
% 9.33/3.25  tff(c_7405, plain, (![A_1767, B_1768, C_1769, C_1770]: (k3_zfmisc_1(k2_zfmisc_1(A_1767, B_1768), C_1769, C_1770)=k4_zfmisc_1(A_1767, B_1768, C_1769, C_1770))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7375])).
% 9.33/3.25  tff(c_7420, plain, (![C_1769, B_2, C_3, A_1, C_1770]: (k4_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_1769, C_1770)=k3_zfmisc_1(k3_zfmisc_1(A_1, B_2, C_3), C_1769, C_1770))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7405])).
% 9.33/3.25  tff(c_7492, plain, (![B_1788, C_1787, C_1789, C_1786, A_1790]: (k4_zfmisc_1(k2_zfmisc_1(A_1790, B_1788), C_1789, C_1786, C_1787)=k2_zfmisc_1(k4_zfmisc_1(A_1790, B_1788, C_1789, C_1786), C_1787))), inference(demodulation, [status(thm), theory('equality')], [c_7398, c_7420])).
% 9.33/3.25  tff(c_7506, plain, (![A_1790, B_1788, C_1789, C_1787]: (k2_zfmisc_1(k4_zfmisc_1(A_1790, B_1788, C_1789, k1_xboole_0), C_1787)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7492, c_22])).
% 9.33/3.25  tff(c_7533, plain, (![C_1787]: (k2_zfmisc_1(k1_xboole_0, C_1787)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_7506])).
% 9.33/3.25  tff(c_7539, plain, (![C_1791]: (k2_zfmisc_1(k1_xboole_0, C_1791)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_7506])).
% 9.33/3.25  tff(c_7550, plain, (![C_1791, C_3]: (k3_zfmisc_1(k1_xboole_0, C_1791, C_3)=k2_zfmisc_1(k1_xboole_0, C_3))), inference(superposition, [status(thm), theory('equality')], [c_7539, c_2])).
% 9.33/3.25  tff(c_7556, plain, (![C_1791, C_3]: (k3_zfmisc_1(k1_xboole_0, C_1791, C_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7533, c_7550])).
% 9.33/3.25  tff(c_7838, plain, (![A_1826, B_1828, C_1829, D_1830, F_1825, E_1827]: (E_1827=B_1828 | k1_xboole_0=C_1829 | k1_xboole_0=B_1828 | k1_xboole_0=A_1826 | k3_zfmisc_1(D_1830, E_1827, F_1825)!=k3_zfmisc_1(A_1826, B_1828, C_1829))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.33/3.25  tff(c_7853, plain, (![C_1791, B_1828, C_1829, A_1826]: (C_1791=B_1828 | k1_xboole_0=C_1829 | k1_xboole_0=B_1828 | k1_xboole_0=A_1826 | k3_zfmisc_1(A_1826, B_1828, C_1829)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7556, c_7838])).
% 9.33/3.25  tff(c_11125, plain, (![C_1791, C_2135]: (C_1791='#skF_6' | k1_xboole_0=C_2135 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_2', C_2135)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11051, c_7853])).
% 9.33/3.25  tff(c_11375, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_11125])).
% 9.33/3.25  tff(c_11415, plain, (![C_1787]: (k2_zfmisc_1('#skF_1', C_1787)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11375, c_11375, c_7533])).
% 9.33/3.25  tff(c_9855, plain, (![C_2037, C_2036, C_2035, B_2033, A_2034]: (k2_zfmisc_1(k4_zfmisc_1(A_2034, B_2033, C_2037, C_2036), C_2035)!=k1_xboole_0 | k1_xboole_0=C_2035 | k1_xboole_0=C_2036 | k1_xboole_0=C_2037 | k2_zfmisc_1(A_2034, B_2033)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7492, c_18])).
% 9.33/3.25  tff(c_9858, plain, (![C_2035]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_2035)!=k1_xboole_0 | k1_xboole_0=C_2035 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9095, c_9855])).
% 9.33/3.25  tff(c_9895, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9858])).
% 9.33/3.25  tff(c_9902, plain, (![C_1762, C_3]: (k4_zfmisc_1('#skF_1', '#skF_6', C_1762, C_3)=k3_zfmisc_1(k1_xboole_0, C_1762, C_3))), inference(superposition, [status(thm), theory('equality')], [c_9895, c_7404])).
% 9.33/3.25  tff(c_9909, plain, (![C_1762, C_3]: (k4_zfmisc_1('#skF_1', '#skF_6', C_1762, C_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7556, c_9902])).
% 9.33/3.25  tff(c_10028, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9909, c_9095])).
% 9.33/3.25  tff(c_10030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_10028])).
% 9.33/3.25  tff(c_10032, plain, (k2_zfmisc_1('#skF_1', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_9858])).
% 9.33/3.25  tff(c_11018, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10985, c_10032])).
% 9.33/3.25  tff(c_11378, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11375, c_11018])).
% 9.33/3.25  tff(c_11471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11415, c_11378])).
% 9.33/3.25  tff(c_11472, plain, (![C_2135, C_1791]: (k1_xboole_0='#skF_6' | k1_xboole_0=C_2135 | k3_zfmisc_1('#skF_1', '#skF_2', C_2135)!=k1_xboole_0 | C_1791='#skF_6')), inference(splitRight, [status(thm)], [c_11125])).
% 9.33/3.25  tff(c_11474, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_11472])).
% 9.33/3.25  tff(c_11511, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11474, c_11018])).
% 9.33/3.25  tff(c_7636, plain, (![A_1806, B_1807, C_1808, C_1809]: (k2_zfmisc_1(k4_zfmisc_1(A_1806, B_1807, C_1808, C_1809), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7492, c_20])).
% 9.33/3.25  tff(c_7647, plain, (![C_3, C_1808, A_1806, C_1809, B_1807]: (k3_zfmisc_1(k4_zfmisc_1(A_1806, B_1807, C_1808, C_1809), k1_xboole_0, C_3)=k2_zfmisc_1(k1_xboole_0, C_3))), inference(superposition, [status(thm), theory('equality')], [c_7636, c_2])).
% 9.33/3.25  tff(c_7665, plain, (![C_3, C_1808, A_1806, C_1809, B_1807]: (k3_zfmisc_1(k4_zfmisc_1(A_1806, B_1807, C_1808, C_1809), k1_xboole_0, C_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7533, c_7647])).
% 9.33/3.25  tff(c_7951, plain, (![B_1840, E_1839, D_1842, C_1841, F_1837, A_1838]: (F_1837=C_1841 | k1_xboole_0=C_1841 | k1_xboole_0=B_1840 | k1_xboole_0=A_1838 | k3_zfmisc_1(D_1842, E_1839, F_1837)!=k3_zfmisc_1(A_1838, B_1840, C_1841))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.33/3.25  tff(c_8080, plain, (![C_1850, C_1849, B_1851, A_1852]: (C_1850=C_1849 | k1_xboole_0=C_1850 | k1_xboole_0=B_1851 | k1_xboole_0=A_1852 | k3_zfmisc_1(A_1852, B_1851, C_1850)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7665, c_7951])).
% 9.33/3.25  tff(c_8771, plain, (![C_1915, B_1913, A_1912, C_1914, C_1916]: (C_1915=C_1914 | k1_xboole_0=C_1915 | k1_xboole_0=C_1916 | k2_zfmisc_1(A_1912, B_1913)=k1_xboole_0 | k4_zfmisc_1(A_1912, B_1913, C_1916, C_1915)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7404, c_8080])).
% 9.33/3.25  tff(c_8792, plain, (![D_23, C_1914, C_22, A_20]: (D_23=C_1914 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_8771])).
% 9.33/3.25  tff(c_8851, plain, (![A_20]: (k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8792])).
% 9.33/3.25  tff(c_11535, plain, (![A_20]: (k2_zfmisc_1(A_20, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11474, c_11474, c_8851])).
% 9.33/3.25  tff(c_11600, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11535, c_10985])).
% 9.33/3.25  tff(c_11602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11511, c_11600])).
% 9.33/3.25  tff(c_11603, plain, (![C_1791, C_2135]: (C_1791='#skF_6' | k1_xboole_0=C_2135 | k3_zfmisc_1('#skF_1', '#skF_2', C_2135)!=k1_xboole_0)), inference(splitRight, [status(thm)], [c_11472])).
% 9.33/3.25  tff(c_11638, plain, (![C_2135]: (k1_xboole_0=C_2135 | k3_zfmisc_1('#skF_1', '#skF_2', C_2135)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11603])).
% 9.33/3.25  tff(c_11955, plain, (![C_2199]: (k1_xboole_0=C_2199)), inference(demodulation, [status(thm), theory('equality')], [c_11765, c_11638])).
% 9.33/3.25  tff(c_12077, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_11955, c_11018])).
% 9.33/3.25  tff(c_12127, plain, (![C_2468]: (C_2468='#skF_6')), inference(splitRight, [status(thm)], [c_11603])).
% 9.33/3.25  tff(c_11604, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_11472])).
% 9.33/3.25  tff(c_12457, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_12127, c_11604])).
% 9.33/3.25  tff(c_12458, plain, (![D_23, C_1914, C_22]: (D_23=C_1914 | k1_xboole_0=D_23 | k1_xboole_0=C_22)), inference(splitRight, [status(thm)], [c_8792])).
% 9.33/3.25  tff(c_12460, plain, (![C_3144]: (k1_xboole_0=C_3144)), inference(splitLeft, [status(thm)], [c_12458])).
% 9.33/3.25  tff(c_12506, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12460, c_7387])).
% 9.33/3.25  tff(c_12538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_12506])).
% 9.33/3.25  tff(c_12539, plain, (![D_23, C_1914]: (D_23=C_1914 | k1_xboole_0=D_23)), inference(splitRight, [status(thm)], [c_12458])).
% 9.33/3.25  tff(c_19138, plain, (![D_4186]: (k1_xboole_0=D_4186)), inference(factorization, [status(thm), theory('equality')], [c_12539])).
% 9.33/3.25  tff(c_19214, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_19138, c_30])).
% 9.33/3.25  tff(c_19215, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_7365])).
% 9.33/3.25  tff(c_19221, plain, (![A_4304, B_4305, C_4306]: (k2_zfmisc_1(k2_zfmisc_1(A_4304, B_4305), C_4306)=k3_zfmisc_1(A_4304, B_4305, C_4306))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.33/3.25  tff(c_19230, plain, (![A_1, B_2, C_3, C_4306]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_4306)=k2_zfmisc_1(k3_zfmisc_1(A_1, B_2, C_3), C_4306))), inference(superposition, [status(thm), theory('equality')], [c_2, c_19221])).
% 9.33/3.25  tff(c_19253, plain, (![A_1, B_2, C_3, C_4306]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_4306)=k4_zfmisc_1(A_1, B_2, C_3, C_4306))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_19230])).
% 9.33/3.25  tff(c_19216, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_7365])).
% 9.33/3.25  tff(c_19236, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19216, c_5182, c_7366, c_32])).
% 9.33/3.25  tff(c_19592, plain, (![B_4362, A_4363, F_4359, C_4361, E_4358, D_4360]: (E_4358=B_4362 | k3_zfmisc_1(A_4363, B_4362, C_4361)=k1_xboole_0 | k3_zfmisc_1(D_4360, E_4358, F_4359)!=k3_zfmisc_1(A_4363, B_4362, C_4361))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.25  tff(c_20522, plain, (![C_4452, A_4447, C_4449, A_4450, B_4451, B_4448, C_4446]: (C_4449=B_4451 | k3_zfmisc_1(A_4447, B_4451, C_4446)=k1_xboole_0 | k4_zfmisc_1(A_4450, B_4448, C_4449, C_4452)!=k3_zfmisc_1(A_4447, B_4451, C_4446))), inference(superposition, [status(thm), theory('equality')], [c_19253, c_19592])).
% 9.33/3.25  tff(c_20583, plain, (![B_4453, A_4454, C_4455]: (B_4453='#skF_7' | k3_zfmisc_1(A_4454, B_4453, C_4455)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_4454, B_4453, C_4455))), inference(superposition, [status(thm), theory('equality')], [c_19236, c_20522])).
% 9.33/3.25  tff(c_20610, plain, (![C_3, A_1, B_2, C_4306]: (C_3='#skF_7' | k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_4306)=k1_xboole_0 | k4_zfmisc_1(A_1, B_2, C_3, C_4306)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_19253, c_20583])).
% 9.33/3.25  tff(c_20619, plain, (![C_3, A_1, B_2, C_4306]: (C_3='#skF_7' | k4_zfmisc_1(A_1, B_2, C_3, C_4306)=k1_xboole_0 | k4_zfmisc_1(A_1, B_2, C_3, C_4306)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19253, c_20610])).
% 9.33/3.25  tff(c_20647, plain, ('#skF_7'='#skF_3' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_20619])).
% 9.33/3.25  tff(c_20649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_19215, c_20647])).
% 9.33/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.25  
% 9.33/3.25  Inference rules
% 9.33/3.25  ----------------------
% 9.33/3.25  #Ref     : 47
% 9.33/3.25  #Sup     : 4661
% 9.33/3.25  #Fact    : 6
% 9.33/3.25  #Define  : 0
% 9.33/3.25  #Split   : 24
% 9.33/3.25  #Chain   : 0
% 9.33/3.25  #Close   : 0
% 9.33/3.25  
% 9.33/3.25  Ordering : KBO
% 9.33/3.25  
% 9.33/3.25  Simplification rules
% 9.33/3.25  ----------------------
% 9.33/3.25  #Subsume      : 1167
% 9.33/3.25  #Demod        : 3820
% 9.33/3.25  #Tautology    : 2260
% 9.33/3.25  #SimpNegUnit  : 103
% 9.33/3.25  #BackRed      : 396
% 9.33/3.25  
% 9.33/3.25  #Partial instantiations: 2664
% 9.33/3.25  #Strategies tried      : 1
% 9.33/3.25  
% 9.33/3.25  Timing (in seconds)
% 9.33/3.25  ----------------------
% 9.33/3.25  Preprocessing        : 0.31
% 9.33/3.25  Parsing              : 0.17
% 9.33/3.25  CNF conversion       : 0.02
% 9.33/3.25  Main loop            : 2.12
% 9.33/3.25  Inferencing          : 0.64
% 9.33/3.25  Reduction            : 0.65
% 9.33/3.25  Demodulation         : 0.49
% 9.33/3.25  BG Simplification    : 0.07
% 9.33/3.25  Subsumption          : 0.64
% 9.33/3.25  Abstraction          : 0.11
% 9.33/3.25  MUC search           : 0.00
% 9.33/3.25  Cooper               : 0.00
% 9.33/3.25  Total                : 2.51
% 9.33/3.25  Index Insertion      : 0.00
% 9.33/3.25  Index Deletion       : 0.00
% 9.33/3.25  Index Matching       : 0.00
% 9.33/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
