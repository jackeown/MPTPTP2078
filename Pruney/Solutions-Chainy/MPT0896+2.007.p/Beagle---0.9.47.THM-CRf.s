%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:46 EST 2020

% Result     : Theorem 8.58s
% Output     : CNFRefutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :  287 (6920 expanded)
%              Number of leaves         :   21 (2136 expanded)
%              Depth                    :   31
%              Number of atoms          :  558 (18250 expanded)
%              Number of equality atoms :  538 (18230 expanded)
%              Maximal formula depth    :   18 (   4 average)
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

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_149,plain,(
    ! [A_36,B_37,C_38] : k2_zfmisc_1(k2_zfmisc_1(A_36,B_37),C_38) = k3_zfmisc_1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    ! [A_3,B_4,C_5,C_38] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_38) = k2_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_149])).

tff(c_286,plain,(
    ! [A_3,B_4,C_5,C_38] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_38) = k4_zfmisc_1(A_3,B_4,C_5,C_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_165])).

tff(c_38,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_513,plain,(
    ! [A_76,D_77,C_79,B_74,F_78,E_75] :
      ( F_78 = C_79
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_76
      | k3_zfmisc_1(D_77,E_75,F_78) != k3_zfmisc_1(A_76,B_74,C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_959,plain,(
    ! [D_149,C_151,C_152,E_148,A_150,B_153,F_147] :
      ( F_147 = C_151
      | k1_xboole_0 = C_151
      | k1_xboole_0 = C_152
      | k2_zfmisc_1(A_150,B_153) = k1_xboole_0
      | k4_zfmisc_1(A_150,B_153,C_152,C_151) != k3_zfmisc_1(D_149,E_148,F_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_513])).

tff(c_980,plain,(
    ! [F_147,D_149,E_148] :
      ( F_147 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_149,E_148,F_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_959])).

tff(c_1068,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_980])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1087,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_2])).

tff(c_1090,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1087])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [B_2,C_38] : k3_zfmisc_1(k1_xboole_0,B_2,C_38) = k2_zfmisc_1(k1_xboole_0,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_149])).

tff(c_182,plain,(
    ! [B_2,C_38] : k3_zfmisc_1(k1_xboole_0,B_2,C_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_178])).

tff(c_1075,plain,(
    ! [C_5,C_38] : k4_zfmisc_1('#skF_5','#skF_6',C_5,C_38) = k3_zfmisc_1(k1_xboole_0,C_5,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_286])).

tff(c_1085,plain,(
    ! [C_5,C_38] : k4_zfmisc_1('#skF_5','#skF_6',C_5,C_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_1075])).

tff(c_1383,plain,(
    ! [C_5,C_38] : k4_zfmisc_1('#skF_5','#skF_6',C_5,C_38) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_1085])).

tff(c_1384,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_38])).

tff(c_233,plain,(
    ! [A_45,B_46,C_47,D_48] : k2_zfmisc_1(k3_zfmisc_1(A_45,B_46,C_47),D_48) = k4_zfmisc_1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_338,plain,(
    ! [D_56,A_57,B_58,C_59] :
      ( k1_xboole_0 = D_56
      | k3_zfmisc_1(A_57,B_58,C_59) = k1_xboole_0
      | k4_zfmisc_1(A_57,B_58,C_59,D_56) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_2])).

tff(c_341,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_338])).

tff(c_386,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_1107,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_386])).

tff(c_1641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_1107])).

tff(c_1642,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1087])).

tff(c_1981,plain,(
    ! [C_5,C_38] : k4_zfmisc_1('#skF_5','#skF_6',C_5,C_38) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_1085])).

tff(c_1982,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1981,c_38])).

tff(c_1660,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_386])).

tff(c_2123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_1660])).

tff(c_2125,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_287,plain,(
    ! [A_52,B_53,C_54,C_55] : k3_zfmisc_1(k2_zfmisc_1(A_52,B_53),C_54,C_55) = k4_zfmisc_1(A_52,B_53,C_54,C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_165])).

tff(c_447,plain,(
    ! [C_73,A_70,D_72,C_69,B_71] : k4_zfmisc_1(k2_zfmisc_1(A_70,B_71),C_73,C_69,D_72) = k2_zfmisc_1(k4_zfmisc_1(A_70,B_71,C_73,C_69),D_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_10])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( k4_zfmisc_1(A_16,B_17,C_18,D_19) != k1_xboole_0
      | k1_xboole_0 = D_19
      | k1_xboole_0 = C_18
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1002,plain,(
    ! [C_158,D_155,A_154,C_156,B_157] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_154,B_157,C_158,C_156),D_155) != k1_xboole_0
      | k1_xboole_0 = D_155
      | k1_xboole_0 = C_156
      | k1_xboole_0 = C_158
      | k2_zfmisc_1(A_154,B_157) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_18])).

tff(c_1011,plain,(
    ! [D_155] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),D_155) != k1_xboole_0
      | k1_xboole_0 = D_155
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1002])).

tff(c_1067,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1011])).

tff(c_2126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2125,c_1067])).

tff(c_2128,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1011])).

tff(c_2127,plain,(
    ! [D_155] :
      ( k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_8'
      | k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),D_155) != k1_xboole_0
      | k1_xboole_0 = D_155 ) ),
    inference(splitRight,[status(thm)],[c_1011])).

tff(c_2129,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2127])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2200,plain,(
    ! [A_16,B_17,C_18] : k4_zfmisc_1(A_16,B_17,C_18,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_2129,c_20])).

tff(c_2389,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2200,c_38])).

tff(c_2190,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_386])).

tff(c_2596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2389,c_2190])).

tff(c_2597,plain,(
    ! [D_155] :
      ( k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),D_155) != k1_xboole_0
      | k1_xboole_0 = D_155 ) ),
    inference(splitRight,[status(thm)],[c_2127])).

tff(c_2599,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2597])).

tff(c_22,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,k1_xboole_0,D_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2626,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_7',D_19) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2599,c_2599,c_22])).

tff(c_3043,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2626,c_38])).

tff(c_2617,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2599,c_386])).

tff(c_3146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3043,c_2617])).

tff(c_3148,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2597])).

tff(c_2598,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2127])).

tff(c_3339,plain,(
    ! [F_368,D_369,E_370] :
      ( F_368 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_369,E_370,F_368) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2128,c_3148,c_2598,c_980])).

tff(c_3345,plain,(
    ! [C_38,A_3,B_4,C_5] :
      ( C_38 = '#skF_8'
      | k4_zfmisc_1(A_3,B_4,C_5,C_38) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_3339])).

tff(c_3375,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3345])).

tff(c_3404,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3375,c_38])).

tff(c_568,plain,(
    ! [C_89,B_84,F_88,E_85,D_87,A_86] :
      ( D_87 = A_86
      | k1_xboole_0 = C_89
      | k1_xboole_0 = B_84
      | k1_xboole_0 = A_86
      | k3_zfmisc_1(D_87,E_85,F_88) != k3_zfmisc_1(A_86,B_84,C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3473,plain,(
    ! [E_381,C_386,A_383,D_384,F_382,C_385,B_387] :
      ( k2_zfmisc_1(A_383,B_387) = D_384
      | k1_xboole_0 = C_385
      | k1_xboole_0 = C_386
      | k2_zfmisc_1(A_383,B_387) = k1_xboole_0
      | k4_zfmisc_1(A_383,B_387,C_386,C_385) != k3_zfmisc_1(D_384,E_381,F_382) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_568])).

tff(c_3476,plain,(
    ! [D_384,E_381,F_382] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_384
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_384,E_381,F_382) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3404,c_3473])).

tff(c_3553,plain,(
    ! [D_392,E_393,F_394] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_392
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_392,E_393,F_394) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2128,c_3148,c_30,c_3476])).

tff(c_3559,plain,(
    ! [A_3,B_4,C_5,C_38] :
      ( k2_zfmisc_1(A_3,B_4) = k2_zfmisc_1('#skF_5','#skF_6')
      | k4_zfmisc_1(A_3,B_4,C_5,C_38) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_3553])).

tff(c_3857,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3559])).

tff(c_3891,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3857,c_2128])).

tff(c_28,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_3901,plain,(
    ! [C_5] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_5) = k3_zfmisc_1('#skF_5','#skF_6',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_3857,c_8])).

tff(c_3911,plain,(
    ! [C_436] : k3_zfmisc_1('#skF_5','#skF_6',C_436) = k3_zfmisc_1('#skF_1','#skF_2',C_436) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3901])).

tff(c_14,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( E_14 = B_11
      | k1_xboole_0 = C_12
      | k1_xboole_0 = B_11
      | k1_xboole_0 = A_10
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3961,plain,(
    ! [E_14,C_436,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k1_xboole_0 = C_436
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_436) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3911,c_14])).

tff(c_5835,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3961])).

tff(c_5849,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5835,c_3891])).

tff(c_5884,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5835,c_5835,c_6])).

tff(c_5905,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5884,c_3857])).

tff(c_5980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5849,c_5905])).

tff(c_5982,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3961])).

tff(c_5981,plain,(
    ! [E_14,C_436,D_13,F_15] :
      ( k1_xboole_0 = '#skF_6'
      | E_14 = '#skF_6'
      | k1_xboole_0 = C_436
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_436) ) ),
    inference(splitRight,[status(thm)],[c_3961])).

tff(c_6015,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5981])).

tff(c_6031,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6015,c_3891])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6065,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6015,c_6015,c_4])).

tff(c_6092,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6065,c_3857])).

tff(c_6161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6031,c_6092])).

tff(c_6162,plain,(
    ! [E_14,C_436,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k1_xboole_0 = C_436
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_436) ) ),
    inference(splitRight,[status(thm)],[c_5981])).

tff(c_6166,plain,(
    ! [C_436] :
      ( '#skF_6' = '#skF_2'
      | k1_xboole_0 = C_436 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6162])).

tff(c_6194,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6166])).

tff(c_3909,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_5','#skF_6',C_5) = k3_zfmisc_1('#skF_1','#skF_2',C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3901])).

tff(c_6226,plain,(
    ! [C_1123] : k3_zfmisc_1('#skF_5','#skF_2',C_1123) = k3_zfmisc_1('#skF_1','#skF_2',C_1123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6194,c_3909])).

tff(c_16,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( D_13 = A_10
      | k1_xboole_0 = C_12
      | k1_xboole_0 = B_11
      | k1_xboole_0 = A_10
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6305,plain,(
    ! [D_13,C_1123,E_14,F_15] :
      ( D_13 = '#skF_5'
      | k1_xboole_0 = C_1123
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_1123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6226,c_16])).

tff(c_6346,plain,(
    ! [D_13,C_1123,E_14,F_15] :
      ( D_13 = '#skF_5'
      | k1_xboole_0 = C_1123
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_1123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5982,c_34,c_6305])).

tff(c_6572,plain,(
    ! [C_1123] :
      ( '#skF_5' = '#skF_1'
      | k1_xboole_0 = C_1123 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6346])).

tff(c_6600,plain,(
    ! [C_1144] : k1_xboole_0 = C_1144 ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6572])).

tff(c_6201,plain,(
    k2_zfmisc_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6194,c_3857])).

tff(c_6630,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6600,c_6201])).

tff(c_6731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3891,c_6630])).

tff(c_6734,plain,(
    ! [C_1451] : k1_xboole_0 = C_1451 ),
    inference(splitRight,[status(thm)],[c_6166])).

tff(c_645,plain,(
    ! [C_102,A_99,D_100,F_101,E_98,B_97] :
      ( E_98 = B_97
      | k1_xboole_0 = C_102
      | k1_xboole_0 = B_97
      | k1_xboole_0 = A_99
      | k3_zfmisc_1(D_100,E_98,F_101) != k3_zfmisc_1(A_99,B_97,C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3294,plain,(
    ! [C_364,F_361,C_365,E_367,D_363,A_362,B_366] :
      ( E_367 = C_365
      | k1_xboole_0 = C_364
      | k1_xboole_0 = C_365
      | k2_zfmisc_1(A_362,B_366) = k1_xboole_0
      | k4_zfmisc_1(A_362,B_366,C_365,C_364) != k3_zfmisc_1(D_363,E_367,F_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_645])).

tff(c_3315,plain,(
    ! [E_367,D_363,F_361] :
      ( E_367 = '#skF_7'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_363,E_367,F_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3294])).

tff(c_3356,plain,(
    ! [E_371,D_372,F_373] :
      ( E_371 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_372,E_371,F_373) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2128,c_3148,c_2598,c_3315])).

tff(c_3362,plain,(
    ! [C_5,A_3,B_4,C_38] :
      ( C_5 = '#skF_7'
      | k4_zfmisc_1(A_3,B_4,C_5,C_38) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_3356])).

tff(c_3519,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3362])).

tff(c_3546,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3519,c_3404])).

tff(c_239,plain,(
    ! [D_48,C_47,A_45,B_46,C_5] : k3_zfmisc_1(k3_zfmisc_1(A_45,B_46,C_47),D_48,C_5) = k2_zfmisc_1(k4_zfmisc_1(A_45,B_46,C_47,D_48),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_8])).

tff(c_3805,plain,(
    ! [A_427,B_425,C_431,F_424,C_430,D_429,E_426,D_428] :
      ( F_424 = C_431
      | k1_xboole_0 = C_431
      | k1_xboole_0 = D_429
      | k3_zfmisc_1(A_427,B_425,C_430) = k1_xboole_0
      | k3_zfmisc_1(D_428,E_426,F_424) != k2_zfmisc_1(k4_zfmisc_1(A_427,B_425,C_430,D_429),C_431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_513])).

tff(c_3808,plain,(
    ! [F_424,C_431,D_428,E_426] :
      ( F_424 = C_431
      | k1_xboole_0 = C_431
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0
      | k3_zfmisc_1(D_428,E_426,F_424) != k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3546,c_3805])).

tff(c_3846,plain,(
    ! [F_424,C_431,D_428,E_426] :
      ( F_424 = C_431
      | k1_xboole_0 = C_431
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0
      | k3_zfmisc_1(D_428,E_426,F_424) != k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_431) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3808])).

tff(c_4177,plain,(
    ! [F_424,C_431,D_428,E_426] :
      ( F_424 = C_431
      | k1_xboole_0 = C_431
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0
      | k3_zfmisc_1(D_428,E_426,F_424) != k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3909,c_3846])).

tff(c_4178,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4177])).

tff(c_158,plain,(
    ! [C_38,A_36,B_37] :
      ( k1_xboole_0 = C_38
      | k2_zfmisc_1(A_36,B_37) = k1_xboole_0
      | k3_zfmisc_1(A_36,B_37,C_38) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2])).

tff(c_3983,plain,(
    ! [C_436] :
      ( k1_xboole_0 = C_436
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2',C_436) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3911,c_158])).

tff(c_4001,plain,(
    ! [C_436] :
      ( k1_xboole_0 = C_436
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2',C_436) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3857,c_3983])).

tff(c_4002,plain,(
    ! [C_436] :
      ( k1_xboole_0 = C_436
      | k3_zfmisc_1('#skF_1','#skF_2',C_436) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3891,c_4001])).

tff(c_4182,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4178,c_4002])).

tff(c_4224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4182])).

tff(c_4226,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4177])).

tff(c_6866,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_6734,c_4226])).

tff(c_6868,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_6873,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6868,c_18])).

tff(c_6882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_6873])).

tff(c_6883,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6894,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6883])).

tff(c_6937,plain,(
    ! [A_1763,B_1764,C_1765] : k2_zfmisc_1(k2_zfmisc_1(A_1763,B_1764),C_1765) = k3_zfmisc_1(A_1763,B_1764,C_1765) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6940,plain,(
    ! [A_1763,B_1764,C_1765,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_1763,B_1764),C_1765,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_1763,B_1764,C_1765),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6937,c_8])).

tff(c_7095,plain,(
    ! [A_1763,B_1764,C_1765,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_1763,B_1764),C_1765,C_5) = k4_zfmisc_1(A_1763,B_1764,C_1765,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6940])).

tff(c_6884,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6889,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6884,c_38])).

tff(c_7270,plain,(
    ! [B_1811,C_1816,E_1812,D_1814,A_1813,F_1815] :
      ( F_1815 = C_1816
      | k1_xboole_0 = C_1816
      | k1_xboole_0 = B_1811
      | k1_xboole_0 = A_1813
      | k3_zfmisc_1(D_1814,E_1812,F_1815) != k3_zfmisc_1(A_1813,B_1811,C_1816) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7545,plain,(
    ! [B_1840,C_1845,A_1842,C_1846,C_1841,B_1843,A_1844] :
      ( C_1846 = C_1845
      | k1_xboole_0 = C_1845
      | k1_xboole_0 = B_1843
      | k1_xboole_0 = A_1844
      | k4_zfmisc_1(A_1842,B_1840,C_1841,C_1846) != k3_zfmisc_1(A_1844,B_1843,C_1845) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7095,c_7270])).

tff(c_7636,plain,(
    ! [C_1857,B_1858,A_1859] :
      ( C_1857 = '#skF_8'
      | k1_xboole_0 = C_1857
      | k1_xboole_0 = B_1858
      | k1_xboole_0 = A_1859
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_1859,B_1858,C_1857) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6889,c_7545])).

tff(c_7642,plain,(
    ! [C_5,C_1765,A_1763,B_1764] :
      ( C_5 = '#skF_8'
      | k1_xboole_0 = C_5
      | k1_xboole_0 = C_1765
      | k2_zfmisc_1(A_1763,B_1764) = k1_xboole_0
      | k4_zfmisc_1(A_1763,B_1764,C_1765,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7095,c_7636])).

tff(c_9268,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7642])).

tff(c_9269,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_6894,c_9268])).

tff(c_9313,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9269,c_2])).

tff(c_9322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_9313])).

tff(c_9323,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6883])).

tff(c_9330,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9323])).

tff(c_9373,plain,(
    ! [A_2011,B_2012,C_2013] : k2_zfmisc_1(k2_zfmisc_1(A_2011,B_2012),C_2013) = k3_zfmisc_1(A_2011,B_2012,C_2013) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9389,plain,(
    ! [A_3,B_4,C_5,C_2013] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_2013) = k2_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),C_2013) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_9373])).

tff(c_9510,plain,(
    ! [A_3,B_4,C_5,C_2013] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_2013) = k4_zfmisc_1(A_3,B_4,C_5,C_2013) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9389])).

tff(c_9324,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6883])).

tff(c_9325,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9324,c_6889])).

tff(c_9511,plain,(
    ! [A_2027,B_2028,C_2029,C_2030] : k3_zfmisc_1(k2_zfmisc_1(A_2027,B_2028),C_2029,C_2030) = k4_zfmisc_1(A_2027,B_2028,C_2029,C_2030) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9389])).

tff(c_9857,plain,(
    ! [A_2080,C_2077,D_2078,B_2079,C_2081] : k4_zfmisc_1(k2_zfmisc_1(A_2080,B_2079),C_2081,C_2077,D_2078) = k2_zfmisc_1(k4_zfmisc_1(A_2080,B_2079,C_2081,C_2077),D_2078) ),
    inference(superposition,[status(thm),theory(equality)],[c_9511,c_10])).

tff(c_10185,plain,(
    ! [D_2124,C_2125,A_2126,B_2123,C_2127] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_2126,B_2123,C_2127,C_2125),D_2124) != k1_xboole_0
      | k1_xboole_0 = D_2124
      | k1_xboole_0 = C_2125
      | k1_xboole_0 = C_2127
      | k2_zfmisc_1(A_2126,B_2123) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9857,c_18])).

tff(c_10194,plain,(
    ! [D_2124] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),D_2124) != k1_xboole_0
      | k1_xboole_0 = D_2124
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9325,c_10185])).

tff(c_10213,plain,(
    ! [D_2124] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),D_2124) != k1_xboole_0
      | k1_xboole_0 = D_2124
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_10194])).

tff(c_10226,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10213])).

tff(c_10239,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_10226,c_2])).

tff(c_10247,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_10239])).

tff(c_9561,plain,(
    ! [A_2031,B_2032,C_2033,D_2034] :
      ( k4_zfmisc_1(A_2031,B_2032,C_2033,D_2034) != k1_xboole_0
      | k1_xboole_0 = D_2034
      | k1_xboole_0 = C_2033
      | k1_xboole_0 = B_2032
      | k1_xboole_0 = A_2031 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9564,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9325,c_9561])).

tff(c_9577,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_30,c_9564])).

tff(c_9586,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9577])).

tff(c_10264,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_9586])).

tff(c_24,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,k1_xboole_0,C_18,D_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10271,plain,(
    ! [A_16,C_18,D_19] : k4_zfmisc_1(A_16,'#skF_6',C_18,D_19) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_10247,c_24])).

tff(c_10561,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10271,c_9325])).

tff(c_10563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10264,c_10561])).

tff(c_10565,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10213])).

tff(c_10564,plain,(
    ! [D_2124] :
      ( k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),D_2124) != k1_xboole_0
      | k1_xboole_0 = D_2124 ) ),
    inference(splitRight,[status(thm)],[c_10213])).

tff(c_10566,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_10564])).

tff(c_10582,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10566,c_9586])).

tff(c_10590,plain,(
    ! [A_16,B_17,D_19] : k4_zfmisc_1(A_16,B_17,'#skF_7',D_19) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10566,c_10566,c_22])).

tff(c_10836,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10590,c_9325])).

tff(c_10838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10582,c_10836])).

tff(c_10840,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10564])).

tff(c_9664,plain,(
    ! [A_2051,F_2053,E_2050,C_2054,B_2049,D_2052] :
      ( E_2050 = B_2049
      | k1_xboole_0 = C_2054
      | k1_xboole_0 = B_2049
      | k1_xboole_0 = A_2051
      | k3_zfmisc_1(D_2052,E_2050,F_2053) != k3_zfmisc_1(A_2051,B_2049,C_2054) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10908,plain,(
    ! [B_2185,E_2181,F_2182,D_2184,A_2180,C_2183,C_2179] :
      ( E_2181 = C_2183
      | k1_xboole_0 = C_2179
      | k1_xboole_0 = C_2183
      | k2_zfmisc_1(A_2180,B_2185) = k1_xboole_0
      | k4_zfmisc_1(A_2180,B_2185,C_2183,C_2179) != k3_zfmisc_1(D_2184,E_2181,F_2182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9510,c_9664])).

tff(c_10926,plain,(
    ! [E_2181,D_2184,F_2182] :
      ( E_2181 = '#skF_7'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2184,E_2181,F_2182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9325,c_10908])).

tff(c_10996,plain,(
    ! [E_2193,D_2194,F_2195] :
      ( E_2193 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2194,E_2193,F_2195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10565,c_10840,c_30,c_10926])).

tff(c_11002,plain,(
    ! [C_5,A_3,B_4,C_2013] :
      ( C_5 = '#skF_7'
      | k4_zfmisc_1(A_3,B_4,C_5,C_2013) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9510,c_10996])).

tff(c_11032,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11002])).

tff(c_11089,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11032,c_9325])).

tff(c_9711,plain,(
    ! [E_2060,F_2063,A_2061,D_2062,B_2059,C_2064] :
      ( D_2062 = A_2061
      | k1_xboole_0 = C_2064
      | k1_xboole_0 = B_2059
      | k1_xboole_0 = A_2061
      | k3_zfmisc_1(D_2062,E_2060,F_2063) != k3_zfmisc_1(A_2061,B_2059,C_2064) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11333,plain,(
    ! [C_2239,E_2245,C_2243,F_2240,B_2244,A_2242,D_2241] :
      ( k2_zfmisc_1(A_2242,B_2244) = D_2241
      | k1_xboole_0 = C_2239
      | k1_xboole_0 = C_2243
      | k2_zfmisc_1(A_2242,B_2244) = k1_xboole_0
      | k4_zfmisc_1(A_2242,B_2244,C_2243,C_2239) != k3_zfmisc_1(D_2241,E_2245,F_2240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9510,c_9711])).

tff(c_11336,plain,(
    ! [D_2241,E_2245,F_2240] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_2241
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2241,E_2245,F_2240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11089,c_11333])).

tff(c_11377,plain,(
    ! [D_2246,E_2247,F_2248] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_2246
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2246,E_2247,F_2248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10565,c_32,c_30,c_11336])).

tff(c_11383,plain,(
    ! [A_3,B_4,C_5,C_2013] :
      ( k2_zfmisc_1(A_3,B_4) = k2_zfmisc_1('#skF_1','#skF_6')
      | k4_zfmisc_1(A_3,B_4,C_5,C_2013) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9510,c_11377])).

tff(c_11396,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11383])).

tff(c_11436,plain,(
    ! [C_5,C_2013] : k3_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_5,C_2013) = k4_zfmisc_1('#skF_1','#skF_6',C_5,C_2013) ),
    inference(superposition,[status(thm),theory(equality)],[c_11396,c_9510])).

tff(c_11560,plain,(
    ! [C_2255,C_2256] : k4_zfmisc_1('#skF_1','#skF_6',C_2255,C_2256) = k4_zfmisc_1('#skF_1','#skF_2',C_2255,C_2256) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9510,c_11436])).

tff(c_11612,plain,(
    ! [C_2255,C_2256] :
      ( k4_zfmisc_1('#skF_1','#skF_2',C_2255,C_2256) != k1_xboole_0
      | k1_xboole_0 = C_2256
      | k1_xboole_0 = C_2255
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11560,c_18])).

tff(c_11649,plain,(
    ! [C_2255,C_2256] :
      ( k4_zfmisc_1('#skF_1','#skF_2',C_2255,C_2256) != k1_xboole_0
      | k1_xboole_0 = C_2256
      | k1_xboole_0 = C_2255
      | k1_xboole_0 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_11612])).

tff(c_11722,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11649])).

tff(c_11429,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11396,c_10565])).

tff(c_11726,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11722,c_11429])).

tff(c_11758,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11722,c_11722,c_4])).

tff(c_11809,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11758,c_11396])).

tff(c_11864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11726,c_11809])).

tff(c_11866,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11649])).

tff(c_11439,plain,(
    ! [C_5] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_5) = k3_zfmisc_1('#skF_1','#skF_6',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_11396,c_8])).

tff(c_11451,plain,(
    ! [C_2253] : k3_zfmisc_1('#skF_1','#skF_6',C_2253) = k3_zfmisc_1('#skF_1','#skF_2',C_2253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11439])).

tff(c_11506,plain,(
    ! [E_14,C_2253,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k1_xboole_0 = C_2253
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_2253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11451,c_14])).

tff(c_11543,plain,(
    ! [E_14,C_2253,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k1_xboole_0 = C_2253
      | k1_xboole_0 = '#skF_6'
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_2253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_11506])).

tff(c_12035,plain,(
    ! [E_14,C_2253,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k1_xboole_0 = C_2253
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_2253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11866,c_11543])).

tff(c_12038,plain,(
    ! [C_2253] :
      ( '#skF_6' = '#skF_2'
      | k1_xboole_0 = C_2253 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12035])).

tff(c_12066,plain,(
    ! [C_2309] : k1_xboole_0 = C_2309 ),
    inference(negUnitSimplification,[status(thm)],[c_9330,c_12038])).

tff(c_12187,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_12066,c_11429])).

tff(c_12188,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_9577])).

tff(c_12222,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_12188])).

tff(c_12239,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12222,c_36])).

tff(c_12236,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12222,c_34])).

tff(c_12238,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12222,c_32])).

tff(c_12237,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12222,c_30])).

tff(c_12189,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9577])).

tff(c_12402,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12222,c_12189])).

tff(c_9457,plain,(
    ! [A_2020,B_2021,C_2022,D_2023] : k2_zfmisc_1(k3_zfmisc_1(A_2020,B_2021,C_2022),D_2023) = k4_zfmisc_1(A_2020,B_2021,C_2022,D_2023) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9466,plain,(
    ! [D_2023,A_2020,B_2021,C_2022] :
      ( k1_xboole_0 = D_2023
      | k3_zfmisc_1(A_2020,B_2021,C_2022) = k1_xboole_0
      | k4_zfmisc_1(A_2020,B_2021,C_2022,D_2023) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9457,c_2])).

tff(c_12571,plain,(
    ! [D_2623,A_2624,B_2625,C_2626] :
      ( D_2623 = '#skF_7'
      | k3_zfmisc_1(A_2624,B_2625,C_2626) = '#skF_7'
      | k4_zfmisc_1(A_2624,B_2625,C_2626,D_2623) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12222,c_12222,c_12222,c_9466])).

tff(c_12586,plain,
    ( '#skF_7' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_12402,c_12571])).

tff(c_12597,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_12237,c_12586])).

tff(c_12527,plain,(
    ! [B_2618,A_2619] :
      ( B_2618 = '#skF_7'
      | A_2619 = '#skF_7'
      | k2_zfmisc_1(A_2619,B_2618) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12222,c_12222,c_12222,c_2])).

tff(c_12539,plain,(
    ! [C_5,A_3,B_4] :
      ( C_5 = '#skF_7'
      | k2_zfmisc_1(A_3,B_4) = '#skF_7'
      | k3_zfmisc_1(A_3,B_4,C_5) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_12527])).

tff(c_12676,plain,
    ( '#skF_7' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_12597,c_12539])).

tff(c_12697,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_12238,c_12676])).

tff(c_12229,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_7'
      | A_1 = '#skF_7'
      | k2_zfmisc_1(A_1,B_2) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12222,c_12222,c_12222,c_2])).

tff(c_12705,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12697,c_12229])).

tff(c_12717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12239,c_12236,c_12705])).

tff(c_12718,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12188])).

tff(c_12736,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_36])).

tff(c_12735,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_32])).

tff(c_12734,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_30])).

tff(c_12900,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_12189])).

tff(c_13074,plain,(
    ! [D_2669,A_2670,B_2671,C_2672] :
      ( D_2669 = '#skF_6'
      | k3_zfmisc_1(A_2670,B_2671,C_2672) = '#skF_6'
      | k4_zfmisc_1(A_2670,B_2671,C_2672,D_2669) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_12718,c_12718,c_9466])).

tff(c_13089,plain,
    ( '#skF_6' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_12900,c_13074])).

tff(c_13100,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_12734,c_13089])).

tff(c_13029,plain,(
    ! [B_2664,A_2665] :
      ( B_2664 = '#skF_6'
      | A_2665 = '#skF_6'
      | k2_zfmisc_1(A_2665,B_2664) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_12718,c_12718,c_2])).

tff(c_13041,plain,(
    ! [C_5,A_3,B_4] :
      ( C_5 = '#skF_6'
      | k2_zfmisc_1(A_3,B_4) = '#skF_6'
      | k3_zfmisc_1(A_3,B_4,C_5) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_13029])).

tff(c_13104,plain,
    ( '#skF_6' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_13100,c_13041])).

tff(c_13124,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_12735,c_13104])).

tff(c_12726,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_6'
      | A_1 = '#skF_6'
      | k2_zfmisc_1(A_1,B_2) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_12718,c_12718,c_2])).

tff(c_13132,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13124,c_12726])).

tff(c_13144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12736,c_9330,c_13132])).

tff(c_13146,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9323])).

tff(c_13151,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13146,c_9325])).

tff(c_13282,plain,(
    ! [A_2687,B_2688,C_2689,D_2690] : k2_zfmisc_1(k3_zfmisc_1(A_2687,B_2688,C_2689),D_2690) = k4_zfmisc_1(A_2687,B_2688,C_2689,D_2690) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13288,plain,(
    ! [A_2687,C_2689,D_2690,B_2688,C_5] : k3_zfmisc_1(k3_zfmisc_1(A_2687,B_2688,C_2689),D_2690,C_5) = k2_zfmisc_1(k4_zfmisc_1(A_2687,B_2688,C_2689,D_2690),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_13282,c_8])).

tff(c_13198,plain,(
    ! [A_2678,B_2679,C_2680] : k2_zfmisc_1(k2_zfmisc_1(A_2678,B_2679),C_2680) = k3_zfmisc_1(A_2678,B_2679,C_2680) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13214,plain,(
    ! [A_3,B_4,C_5,C_2680] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_2680) = k2_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),C_2680) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_13198])).

tff(c_13336,plain,(
    ! [A_2694,B_2695,C_2696,C_2697] : k3_zfmisc_1(k2_zfmisc_1(A_2694,B_2695),C_2696,C_2697) = k4_zfmisc_1(A_2694,B_2695,C_2696,C_2697) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13214])).

tff(c_13370,plain,(
    ! [A_3,C_5,C_2696,B_4,C_2697] : k4_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_2696,C_2697) = k3_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),C_2696,C_2697) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_13336])).

tff(c_13554,plain,(
    ! [B_2725,C_2722,C_2721,A_2723,C_2724] : k4_zfmisc_1(k2_zfmisc_1(A_2723,B_2725),C_2724,C_2721,C_2722) = k2_zfmisc_1(k4_zfmisc_1(A_2723,B_2725,C_2724,C_2721),C_2722) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13288,c_13370])).

tff(c_13991,plain,(
    ! [A_2791,C_2788,C_2787,C_2789,B_2790] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_2791,B_2790,C_2788,C_2787),C_2789) != k1_xboole_0
      | k1_xboole_0 = C_2789
      | k1_xboole_0 = C_2787
      | k1_xboole_0 = C_2788
      | k2_zfmisc_1(A_2791,B_2790) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13554,c_18])).

tff(c_14000,plain,(
    ! [C_2789] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_2789) != k1_xboole_0
      | k1_xboole_0 = C_2789
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13151,c_13991])).

tff(c_14019,plain,(
    ! [C_2789] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_2789) != k1_xboole_0
      | k1_xboole_0 = C_2789
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_14000])).

tff(c_14033,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14019])).

tff(c_14046,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14033,c_2])).

tff(c_14055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_14046])).

tff(c_14057,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14019])).

tff(c_13145,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9323])).

tff(c_13335,plain,(
    ! [A_3,B_4,C_5,C_2680] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_2680) = k4_zfmisc_1(A_3,B_4,C_5,C_2680) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13214])).

tff(c_13442,plain,(
    ! [C_2711,E_2707,D_2709,A_2708,F_2710,B_2706] :
      ( E_2707 = B_2706
      | k1_xboole_0 = C_2711
      | k1_xboole_0 = B_2706
      | k1_xboole_0 = A_2708
      | k3_zfmisc_1(D_2709,E_2707,F_2710) != k3_zfmisc_1(A_2708,B_2706,C_2711) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_13868,plain,(
    ! [B_2771,A_2767,C_2766,C_2769,A_2770,B_2768,C_2765] :
      ( C_2769 = B_2768
      | k1_xboole_0 = C_2765
      | k1_xboole_0 = B_2768
      | k1_xboole_0 = A_2770
      | k4_zfmisc_1(A_2767,B_2771,C_2769,C_2766) != k3_zfmisc_1(A_2770,B_2768,C_2765) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13335,c_13442])).

tff(c_13949,plain,(
    ! [B_2779,C_2780,A_2781] :
      ( B_2779 = '#skF_7'
      | k1_xboole_0 = C_2780
      | k1_xboole_0 = B_2779
      | k1_xboole_0 = A_2781
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_2781,B_2779,C_2780) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13151,c_13868])).

tff(c_13955,plain,(
    ! [C_5,C_2680,A_3,B_4] :
      ( C_5 = '#skF_7'
      | k1_xboole_0 = C_2680
      | k1_xboole_0 = C_5
      | k2_zfmisc_1(A_3,B_4) = k1_xboole_0
      | k4_zfmisc_1(A_3,B_4,C_5,C_2680) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13335,c_13949])).

tff(c_14523,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13955])).

tff(c_14525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14057,c_32,c_30,c_13145,c_14523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.58/3.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.06  
% 8.79/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.07  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 8.79/3.07  
% 8.79/3.07  %Foreground sorts:
% 8.79/3.07  
% 8.79/3.07  
% 8.79/3.07  %Background operators:
% 8.79/3.07  
% 8.79/3.07  
% 8.79/3.07  %Foreground operators:
% 8.79/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.79/3.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.79/3.07  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 8.79/3.07  tff('#skF_7', type, '#skF_7': $i).
% 8.79/3.07  tff('#skF_5', type, '#skF_5': $i).
% 8.79/3.07  tff('#skF_6', type, '#skF_6': $i).
% 8.79/3.07  tff('#skF_2', type, '#skF_2': $i).
% 8.79/3.07  tff('#skF_3', type, '#skF_3': $i).
% 8.79/3.07  tff('#skF_1', type, '#skF_1': $i).
% 8.79/3.07  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.79/3.07  tff('#skF_8', type, '#skF_8': $i).
% 8.79/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.79/3.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.79/3.07  tff('#skF_4', type, '#skF_4': $i).
% 8.79/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.79/3.07  
% 8.79/3.10  tff(f_83, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_mcart_1)).
% 8.79/3.10  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 8.79/3.10  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.79/3.10  tff(f_49, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 8.79/3.10  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.79/3.10  tff(f_64, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 8.79/3.10  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.79/3.10  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.79/3.10  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.79/3.10  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.79/3.10  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.79/3.10  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.79/3.10  tff(c_149, plain, (![A_36, B_37, C_38]: (k2_zfmisc_1(k2_zfmisc_1(A_36, B_37), C_38)=k3_zfmisc_1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.79/3.10  tff(c_165, plain, (![A_3, B_4, C_5, C_38]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_38)=k2_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), C_38))), inference(superposition, [status(thm), theory('equality')], [c_8, c_149])).
% 8.79/3.10  tff(c_286, plain, (![A_3, B_4, C_5, C_38]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_38)=k4_zfmisc_1(A_3, B_4, C_5, C_38))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_165])).
% 8.79/3.10  tff(c_38, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.79/3.10  tff(c_513, plain, (![A_76, D_77, C_79, B_74, F_78, E_75]: (F_78=C_79 | k1_xboole_0=C_79 | k1_xboole_0=B_74 | k1_xboole_0=A_76 | k3_zfmisc_1(D_77, E_75, F_78)!=k3_zfmisc_1(A_76, B_74, C_79))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.10  tff(c_959, plain, (![D_149, C_151, C_152, E_148, A_150, B_153, F_147]: (F_147=C_151 | k1_xboole_0=C_151 | k1_xboole_0=C_152 | k2_zfmisc_1(A_150, B_153)=k1_xboole_0 | k4_zfmisc_1(A_150, B_153, C_152, C_151)!=k3_zfmisc_1(D_149, E_148, F_147))), inference(superposition, [status(thm), theory('equality')], [c_286, c_513])).
% 8.79/3.10  tff(c_980, plain, (![F_147, D_149, E_148]: (F_147='#skF_8' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_149, E_148, F_147))), inference(superposition, [status(thm), theory('equality')], [c_38, c_959])).
% 8.79/3.10  tff(c_1068, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_980])).
% 8.79/3.10  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.79/3.10  tff(c_1087, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1068, c_2])).
% 8.79/3.10  tff(c_1090, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1087])).
% 8.79/3.10  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.79/3.10  tff(c_178, plain, (![B_2, C_38]: (k3_zfmisc_1(k1_xboole_0, B_2, C_38)=k2_zfmisc_1(k1_xboole_0, C_38))), inference(superposition, [status(thm), theory('equality')], [c_6, c_149])).
% 8.79/3.10  tff(c_182, plain, (![B_2, C_38]: (k3_zfmisc_1(k1_xboole_0, B_2, C_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_178])).
% 8.79/3.10  tff(c_1075, plain, (![C_5, C_38]: (k4_zfmisc_1('#skF_5', '#skF_6', C_5, C_38)=k3_zfmisc_1(k1_xboole_0, C_5, C_38))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_286])).
% 8.79/3.10  tff(c_1085, plain, (![C_5, C_38]: (k4_zfmisc_1('#skF_5', '#skF_6', C_5, C_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_182, c_1075])).
% 8.79/3.10  tff(c_1383, plain, (![C_5, C_38]: (k4_zfmisc_1('#skF_5', '#skF_6', C_5, C_38)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_1085])).
% 8.79/3.10  tff(c_1384, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_38])).
% 8.79/3.10  tff(c_233, plain, (![A_45, B_46, C_47, D_48]: (k2_zfmisc_1(k3_zfmisc_1(A_45, B_46, C_47), D_48)=k4_zfmisc_1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.79/3.10  tff(c_338, plain, (![D_56, A_57, B_58, C_59]: (k1_xboole_0=D_56 | k3_zfmisc_1(A_57, B_58, C_59)=k1_xboole_0 | k4_zfmisc_1(A_57, B_58, C_59, D_56)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_233, c_2])).
% 8.79/3.10  tff(c_341, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_338])).
% 8.79/3.10  tff(c_386, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_341])).
% 8.79/3.10  tff(c_1107, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_386])).
% 8.79/3.10  tff(c_1641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1384, c_1107])).
% 8.79/3.10  tff(c_1642, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1087])).
% 8.79/3.10  tff(c_1981, plain, (![C_5, C_38]: (k4_zfmisc_1('#skF_5', '#skF_6', C_5, C_38)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1642, c_1085])).
% 8.79/3.10  tff(c_1982, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1981, c_38])).
% 8.79/3.10  tff(c_1660, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1642, c_386])).
% 8.79/3.10  tff(c_2123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1982, c_1660])).
% 8.79/3.10  tff(c_2125, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_980])).
% 8.79/3.10  tff(c_287, plain, (![A_52, B_53, C_54, C_55]: (k3_zfmisc_1(k2_zfmisc_1(A_52, B_53), C_54, C_55)=k4_zfmisc_1(A_52, B_53, C_54, C_55))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_165])).
% 8.79/3.10  tff(c_447, plain, (![C_73, A_70, D_72, C_69, B_71]: (k4_zfmisc_1(k2_zfmisc_1(A_70, B_71), C_73, C_69, D_72)=k2_zfmisc_1(k4_zfmisc_1(A_70, B_71, C_73, C_69), D_72))), inference(superposition, [status(thm), theory('equality')], [c_287, c_10])).
% 8.79/3.10  tff(c_18, plain, (![A_16, B_17, C_18, D_19]: (k4_zfmisc_1(A_16, B_17, C_18, D_19)!=k1_xboole_0 | k1_xboole_0=D_19 | k1_xboole_0=C_18 | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.79/3.10  tff(c_1002, plain, (![C_158, D_155, A_154, C_156, B_157]: (k2_zfmisc_1(k4_zfmisc_1(A_154, B_157, C_158, C_156), D_155)!=k1_xboole_0 | k1_xboole_0=D_155 | k1_xboole_0=C_156 | k1_xboole_0=C_158 | k2_zfmisc_1(A_154, B_157)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_447, c_18])).
% 8.79/3.10  tff(c_1011, plain, (![D_155]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), D_155)!=k1_xboole_0 | k1_xboole_0=D_155 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_1002])).
% 8.79/3.10  tff(c_1067, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1011])).
% 8.79/3.10  tff(c_2126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2125, c_1067])).
% 8.79/3.10  tff(c_2128, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1011])).
% 8.79/3.10  tff(c_2127, plain, (![D_155]: (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8' | k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), D_155)!=k1_xboole_0 | k1_xboole_0=D_155)), inference(splitRight, [status(thm)], [c_1011])).
% 8.79/3.10  tff(c_2129, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_2127])).
% 8.79/3.10  tff(c_20, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.79/3.10  tff(c_2200, plain, (![A_16, B_17, C_18]: (k4_zfmisc_1(A_16, B_17, C_18, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2129, c_2129, c_20])).
% 8.79/3.10  tff(c_2389, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2200, c_38])).
% 8.79/3.10  tff(c_2190, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2129, c_386])).
% 8.79/3.10  tff(c_2596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2389, c_2190])).
% 8.79/3.10  tff(c_2597, plain, (![D_155]: (k1_xboole_0='#skF_7' | k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), D_155)!=k1_xboole_0 | k1_xboole_0=D_155)), inference(splitRight, [status(thm)], [c_2127])).
% 8.79/3.10  tff(c_2599, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_2597])).
% 8.79/3.11  tff(c_22, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, k1_xboole_0, D_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.79/3.11  tff(c_2626, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_7', D_19)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2599, c_2599, c_22])).
% 8.79/3.11  tff(c_3043, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2626, c_38])).
% 8.79/3.11  tff(c_2617, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2599, c_386])).
% 8.79/3.11  tff(c_3146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3043, c_2617])).
% 8.79/3.11  tff(c_3148, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_2597])).
% 8.79/3.11  tff(c_2598, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_2127])).
% 8.79/3.11  tff(c_3339, plain, (![F_368, D_369, E_370]: (F_368='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_369, E_370, F_368))), inference(negUnitSimplification, [status(thm)], [c_2128, c_3148, c_2598, c_980])).
% 8.79/3.11  tff(c_3345, plain, (![C_38, A_3, B_4, C_5]: (C_38='#skF_8' | k4_zfmisc_1(A_3, B_4, C_5, C_38)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_3339])).
% 8.79/3.11  tff(c_3375, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_3345])).
% 8.79/3.11  tff(c_3404, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3375, c_38])).
% 8.79/3.11  tff(c_568, plain, (![C_89, B_84, F_88, E_85, D_87, A_86]: (D_87=A_86 | k1_xboole_0=C_89 | k1_xboole_0=B_84 | k1_xboole_0=A_86 | k3_zfmisc_1(D_87, E_85, F_88)!=k3_zfmisc_1(A_86, B_84, C_89))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.11  tff(c_3473, plain, (![E_381, C_386, A_383, D_384, F_382, C_385, B_387]: (k2_zfmisc_1(A_383, B_387)=D_384 | k1_xboole_0=C_385 | k1_xboole_0=C_386 | k2_zfmisc_1(A_383, B_387)=k1_xboole_0 | k4_zfmisc_1(A_383, B_387, C_386, C_385)!=k3_zfmisc_1(D_384, E_381, F_382))), inference(superposition, [status(thm), theory('equality')], [c_286, c_568])).
% 8.79/3.11  tff(c_3476, plain, (![D_384, E_381, F_382]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_384 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_384, E_381, F_382))), inference(superposition, [status(thm), theory('equality')], [c_3404, c_3473])).
% 8.79/3.11  tff(c_3553, plain, (![D_392, E_393, F_394]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_392 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_392, E_393, F_394))), inference(negUnitSimplification, [status(thm)], [c_2128, c_3148, c_30, c_3476])).
% 8.79/3.11  tff(c_3559, plain, (![A_3, B_4, C_5, C_38]: (k2_zfmisc_1(A_3, B_4)=k2_zfmisc_1('#skF_5', '#skF_6') | k4_zfmisc_1(A_3, B_4, C_5, C_38)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_3553])).
% 8.79/3.11  tff(c_3857, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_3559])).
% 8.79/3.11  tff(c_3891, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3857, c_2128])).
% 8.79/3.11  tff(c_28, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.79/3.11  tff(c_106, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_28])).
% 8.79/3.11  tff(c_3901, plain, (![C_5]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_5)=k3_zfmisc_1('#skF_5', '#skF_6', C_5))), inference(superposition, [status(thm), theory('equality')], [c_3857, c_8])).
% 8.79/3.11  tff(c_3911, plain, (![C_436]: (k3_zfmisc_1('#skF_5', '#skF_6', C_436)=k3_zfmisc_1('#skF_1', '#skF_2', C_436))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3901])).
% 8.79/3.11  tff(c_14, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (E_14=B_11 | k1_xboole_0=C_12 | k1_xboole_0=B_11 | k1_xboole_0=A_10 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.11  tff(c_3961, plain, (![E_14, C_436, D_13, F_15]: (E_14='#skF_6' | k1_xboole_0=C_436 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_436))), inference(superposition, [status(thm), theory('equality')], [c_3911, c_14])).
% 8.79/3.11  tff(c_5835, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3961])).
% 8.79/3.11  tff(c_5849, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5835, c_3891])).
% 8.79/3.11  tff(c_5884, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5835, c_5835, c_6])).
% 8.79/3.11  tff(c_5905, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5884, c_3857])).
% 8.79/3.11  tff(c_5980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5849, c_5905])).
% 8.79/3.11  tff(c_5982, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_3961])).
% 8.79/3.11  tff(c_5981, plain, (![E_14, C_436, D_13, F_15]: (k1_xboole_0='#skF_6' | E_14='#skF_6' | k1_xboole_0=C_436 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_436))), inference(splitRight, [status(thm)], [c_3961])).
% 8.79/3.11  tff(c_6015, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_5981])).
% 8.79/3.11  tff(c_6031, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6015, c_3891])).
% 8.79/3.11  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.79/3.11  tff(c_6065, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6015, c_6015, c_4])).
% 8.79/3.11  tff(c_6092, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6065, c_3857])).
% 8.79/3.11  tff(c_6161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6031, c_6092])).
% 8.79/3.11  tff(c_6162, plain, (![E_14, C_436, D_13, F_15]: (E_14='#skF_6' | k1_xboole_0=C_436 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_436))), inference(splitRight, [status(thm)], [c_5981])).
% 8.79/3.11  tff(c_6166, plain, (![C_436]: ('#skF_6'='#skF_2' | k1_xboole_0=C_436)), inference(reflexivity, [status(thm), theory('equality')], [c_6162])).
% 8.79/3.11  tff(c_6194, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_6166])).
% 8.79/3.11  tff(c_3909, plain, (![C_5]: (k3_zfmisc_1('#skF_5', '#skF_6', C_5)=k3_zfmisc_1('#skF_1', '#skF_2', C_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3901])).
% 8.79/3.11  tff(c_6226, plain, (![C_1123]: (k3_zfmisc_1('#skF_5', '#skF_2', C_1123)=k3_zfmisc_1('#skF_1', '#skF_2', C_1123))), inference(demodulation, [status(thm), theory('equality')], [c_6194, c_3909])).
% 8.79/3.11  tff(c_16, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (D_13=A_10 | k1_xboole_0=C_12 | k1_xboole_0=B_11 | k1_xboole_0=A_10 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.11  tff(c_6305, plain, (![D_13, C_1123, E_14, F_15]: (D_13='#skF_5' | k1_xboole_0=C_1123 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_5' | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1123))), inference(superposition, [status(thm), theory('equality')], [c_6226, c_16])).
% 8.79/3.11  tff(c_6346, plain, (![D_13, C_1123, E_14, F_15]: (D_13='#skF_5' | k1_xboole_0=C_1123 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1123))), inference(negUnitSimplification, [status(thm)], [c_5982, c_34, c_6305])).
% 8.79/3.11  tff(c_6572, plain, (![C_1123]: ('#skF_5'='#skF_1' | k1_xboole_0=C_1123)), inference(reflexivity, [status(thm), theory('equality')], [c_6346])).
% 8.79/3.11  tff(c_6600, plain, (![C_1144]: (k1_xboole_0=C_1144)), inference(negUnitSimplification, [status(thm)], [c_106, c_6572])).
% 8.79/3.11  tff(c_6201, plain, (k2_zfmisc_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6194, c_3857])).
% 8.79/3.11  tff(c_6630, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6600, c_6201])).
% 8.79/3.11  tff(c_6731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3891, c_6630])).
% 8.79/3.11  tff(c_6734, plain, (![C_1451]: (k1_xboole_0=C_1451)), inference(splitRight, [status(thm)], [c_6166])).
% 8.79/3.11  tff(c_645, plain, (![C_102, A_99, D_100, F_101, E_98, B_97]: (E_98=B_97 | k1_xboole_0=C_102 | k1_xboole_0=B_97 | k1_xboole_0=A_99 | k3_zfmisc_1(D_100, E_98, F_101)!=k3_zfmisc_1(A_99, B_97, C_102))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.11  tff(c_3294, plain, (![C_364, F_361, C_365, E_367, D_363, A_362, B_366]: (E_367=C_365 | k1_xboole_0=C_364 | k1_xboole_0=C_365 | k2_zfmisc_1(A_362, B_366)=k1_xboole_0 | k4_zfmisc_1(A_362, B_366, C_365, C_364)!=k3_zfmisc_1(D_363, E_367, F_361))), inference(superposition, [status(thm), theory('equality')], [c_286, c_645])).
% 8.79/3.11  tff(c_3315, plain, (![E_367, D_363, F_361]: (E_367='#skF_7' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_363, E_367, F_361))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3294])).
% 8.79/3.11  tff(c_3356, plain, (![E_371, D_372, F_373]: (E_371='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_372, E_371, F_373))), inference(negUnitSimplification, [status(thm)], [c_2128, c_3148, c_2598, c_3315])).
% 8.79/3.11  tff(c_3362, plain, (![C_5, A_3, B_4, C_38]: (C_5='#skF_7' | k4_zfmisc_1(A_3, B_4, C_5, C_38)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_3356])).
% 8.79/3.11  tff(c_3519, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_3362])).
% 8.79/3.11  tff(c_3546, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3519, c_3404])).
% 8.79/3.11  tff(c_239, plain, (![D_48, C_47, A_45, B_46, C_5]: (k3_zfmisc_1(k3_zfmisc_1(A_45, B_46, C_47), D_48, C_5)=k2_zfmisc_1(k4_zfmisc_1(A_45, B_46, C_47, D_48), C_5))), inference(superposition, [status(thm), theory('equality')], [c_233, c_8])).
% 8.79/3.11  tff(c_3805, plain, (![A_427, B_425, C_431, F_424, C_430, D_429, E_426, D_428]: (F_424=C_431 | k1_xboole_0=C_431 | k1_xboole_0=D_429 | k3_zfmisc_1(A_427, B_425, C_430)=k1_xboole_0 | k3_zfmisc_1(D_428, E_426, F_424)!=k2_zfmisc_1(k4_zfmisc_1(A_427, B_425, C_430, D_429), C_431))), inference(superposition, [status(thm), theory('equality')], [c_239, c_513])).
% 8.79/3.11  tff(c_3808, plain, (![F_424, C_431, D_428, E_426]: (F_424=C_431 | k1_xboole_0=C_431 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0 | k3_zfmisc_1(D_428, E_426, F_424)!=k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_431))), inference(superposition, [status(thm), theory('equality')], [c_3546, c_3805])).
% 8.79/3.11  tff(c_3846, plain, (![F_424, C_431, D_428, E_426]: (F_424=C_431 | k1_xboole_0=C_431 | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0 | k3_zfmisc_1(D_428, E_426, F_424)!=k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_431))), inference(negUnitSimplification, [status(thm)], [c_30, c_3808])).
% 8.79/3.11  tff(c_4177, plain, (![F_424, C_431, D_428, E_426]: (F_424=C_431 | k1_xboole_0=C_431 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0 | k3_zfmisc_1(D_428, E_426, F_424)!=k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_431))), inference(demodulation, [status(thm), theory('equality')], [c_3909, c_3846])).
% 8.79/3.11  tff(c_4178, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4177])).
% 8.79/3.11  tff(c_158, plain, (![C_38, A_36, B_37]: (k1_xboole_0=C_38 | k2_zfmisc_1(A_36, B_37)=k1_xboole_0 | k3_zfmisc_1(A_36, B_37, C_38)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_149, c_2])).
% 8.79/3.11  tff(c_3983, plain, (![C_436]: (k1_xboole_0=C_436 | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', C_436)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3911, c_158])).
% 8.79/3.11  tff(c_4001, plain, (![C_436]: (k1_xboole_0=C_436 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', C_436)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3857, c_3983])).
% 8.79/3.11  tff(c_4002, plain, (![C_436]: (k1_xboole_0=C_436 | k3_zfmisc_1('#skF_1', '#skF_2', C_436)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3891, c_4001])).
% 8.79/3.11  tff(c_4182, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4178, c_4002])).
% 8.79/3.11  tff(c_4224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_4182])).
% 8.79/3.11  tff(c_4226, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_4177])).
% 8.79/3.11  tff(c_6866, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_6734, c_4226])).
% 8.79/3.11  tff(c_6868, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_341])).
% 8.79/3.11  tff(c_6873, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6868, c_18])).
% 8.79/3.11  tff(c_6882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_6873])).
% 8.79/3.11  tff(c_6883, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 8.79/3.11  tff(c_6894, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_6883])).
% 8.79/3.11  tff(c_6937, plain, (![A_1763, B_1764, C_1765]: (k2_zfmisc_1(k2_zfmisc_1(A_1763, B_1764), C_1765)=k3_zfmisc_1(A_1763, B_1764, C_1765))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.79/3.11  tff(c_6940, plain, (![A_1763, B_1764, C_1765, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_1763, B_1764), C_1765, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_1763, B_1764, C_1765), C_5))), inference(superposition, [status(thm), theory('equality')], [c_6937, c_8])).
% 8.79/3.11  tff(c_7095, plain, (![A_1763, B_1764, C_1765, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_1763, B_1764), C_1765, C_5)=k4_zfmisc_1(A_1763, B_1764, C_1765, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6940])).
% 8.79/3.11  tff(c_6884, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_28])).
% 8.79/3.11  tff(c_6889, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6884, c_38])).
% 8.79/3.11  tff(c_7270, plain, (![B_1811, C_1816, E_1812, D_1814, A_1813, F_1815]: (F_1815=C_1816 | k1_xboole_0=C_1816 | k1_xboole_0=B_1811 | k1_xboole_0=A_1813 | k3_zfmisc_1(D_1814, E_1812, F_1815)!=k3_zfmisc_1(A_1813, B_1811, C_1816))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.11  tff(c_7545, plain, (![B_1840, C_1845, A_1842, C_1846, C_1841, B_1843, A_1844]: (C_1846=C_1845 | k1_xboole_0=C_1845 | k1_xboole_0=B_1843 | k1_xboole_0=A_1844 | k4_zfmisc_1(A_1842, B_1840, C_1841, C_1846)!=k3_zfmisc_1(A_1844, B_1843, C_1845))), inference(superposition, [status(thm), theory('equality')], [c_7095, c_7270])).
% 8.79/3.11  tff(c_7636, plain, (![C_1857, B_1858, A_1859]: (C_1857='#skF_8' | k1_xboole_0=C_1857 | k1_xboole_0=B_1858 | k1_xboole_0=A_1859 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_1859, B_1858, C_1857))), inference(superposition, [status(thm), theory('equality')], [c_6889, c_7545])).
% 8.79/3.11  tff(c_7642, plain, (![C_5, C_1765, A_1763, B_1764]: (C_5='#skF_8' | k1_xboole_0=C_5 | k1_xboole_0=C_1765 | k2_zfmisc_1(A_1763, B_1764)=k1_xboole_0 | k4_zfmisc_1(A_1763, B_1764, C_1765, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7095, c_7636])).
% 8.79/3.11  tff(c_9268, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_7642])).
% 8.79/3.11  tff(c_9269, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_6894, c_9268])).
% 8.79/3.11  tff(c_9313, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9269, c_2])).
% 8.79/3.11  tff(c_9322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_9313])).
% 8.79/3.11  tff(c_9323, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_6883])).
% 8.79/3.11  tff(c_9330, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_9323])).
% 8.79/3.11  tff(c_9373, plain, (![A_2011, B_2012, C_2013]: (k2_zfmisc_1(k2_zfmisc_1(A_2011, B_2012), C_2013)=k3_zfmisc_1(A_2011, B_2012, C_2013))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.79/3.11  tff(c_9389, plain, (![A_3, B_4, C_5, C_2013]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_2013)=k2_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), C_2013))), inference(superposition, [status(thm), theory('equality')], [c_8, c_9373])).
% 8.79/3.11  tff(c_9510, plain, (![A_3, B_4, C_5, C_2013]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_2013)=k4_zfmisc_1(A_3, B_4, C_5, C_2013))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9389])).
% 8.79/3.11  tff(c_9324, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_6883])).
% 8.79/3.11  tff(c_9325, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9324, c_6889])).
% 8.79/3.11  tff(c_9511, plain, (![A_2027, B_2028, C_2029, C_2030]: (k3_zfmisc_1(k2_zfmisc_1(A_2027, B_2028), C_2029, C_2030)=k4_zfmisc_1(A_2027, B_2028, C_2029, C_2030))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9389])).
% 8.79/3.11  tff(c_9857, plain, (![A_2080, C_2077, D_2078, B_2079, C_2081]: (k4_zfmisc_1(k2_zfmisc_1(A_2080, B_2079), C_2081, C_2077, D_2078)=k2_zfmisc_1(k4_zfmisc_1(A_2080, B_2079, C_2081, C_2077), D_2078))), inference(superposition, [status(thm), theory('equality')], [c_9511, c_10])).
% 8.79/3.11  tff(c_10185, plain, (![D_2124, C_2125, A_2126, B_2123, C_2127]: (k2_zfmisc_1(k4_zfmisc_1(A_2126, B_2123, C_2127, C_2125), D_2124)!=k1_xboole_0 | k1_xboole_0=D_2124 | k1_xboole_0=C_2125 | k1_xboole_0=C_2127 | k2_zfmisc_1(A_2126, B_2123)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9857, c_18])).
% 8.79/3.11  tff(c_10194, plain, (![D_2124]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), D_2124)!=k1_xboole_0 | k1_xboole_0=D_2124 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9325, c_10185])).
% 8.79/3.11  tff(c_10213, plain, (![D_2124]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), D_2124)!=k1_xboole_0 | k1_xboole_0=D_2124 | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_30, c_10194])).
% 8.79/3.11  tff(c_10226, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10213])).
% 8.79/3.11  tff(c_10239, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_10226, c_2])).
% 8.79/3.11  tff(c_10247, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_36, c_10239])).
% 8.79/3.11  tff(c_9561, plain, (![A_2031, B_2032, C_2033, D_2034]: (k4_zfmisc_1(A_2031, B_2032, C_2033, D_2034)!=k1_xboole_0 | k1_xboole_0=D_2034 | k1_xboole_0=C_2033 | k1_xboole_0=B_2032 | k1_xboole_0=A_2031)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.79/3.11  tff(c_9564, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9325, c_9561])).
% 8.79/3.11  tff(c_9577, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_36, c_30, c_9564])).
% 8.79/3.11  tff(c_9586, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9577])).
% 8.79/3.11  tff(c_10264, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_9586])).
% 8.79/3.11  tff(c_24, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, k1_xboole_0, C_18, D_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.79/3.11  tff(c_10271, plain, (![A_16, C_18, D_19]: (k4_zfmisc_1(A_16, '#skF_6', C_18, D_19)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_10247, c_24])).
% 8.79/3.11  tff(c_10561, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10271, c_9325])).
% 8.79/3.11  tff(c_10563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10264, c_10561])).
% 8.79/3.11  tff(c_10565, plain, (k2_zfmisc_1('#skF_1', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_10213])).
% 8.79/3.11  tff(c_10564, plain, (![D_2124]: (k1_xboole_0='#skF_7' | k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), D_2124)!=k1_xboole_0 | k1_xboole_0=D_2124)), inference(splitRight, [status(thm)], [c_10213])).
% 8.79/3.11  tff(c_10566, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_10564])).
% 8.79/3.11  tff(c_10582, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10566, c_9586])).
% 8.79/3.11  tff(c_10590, plain, (![A_16, B_17, D_19]: (k4_zfmisc_1(A_16, B_17, '#skF_7', D_19)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10566, c_10566, c_22])).
% 8.79/3.11  tff(c_10836, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10590, c_9325])).
% 8.79/3.11  tff(c_10838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10582, c_10836])).
% 8.79/3.11  tff(c_10840, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_10564])).
% 8.79/3.11  tff(c_9664, plain, (![A_2051, F_2053, E_2050, C_2054, B_2049, D_2052]: (E_2050=B_2049 | k1_xboole_0=C_2054 | k1_xboole_0=B_2049 | k1_xboole_0=A_2051 | k3_zfmisc_1(D_2052, E_2050, F_2053)!=k3_zfmisc_1(A_2051, B_2049, C_2054))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.11  tff(c_10908, plain, (![B_2185, E_2181, F_2182, D_2184, A_2180, C_2183, C_2179]: (E_2181=C_2183 | k1_xboole_0=C_2179 | k1_xboole_0=C_2183 | k2_zfmisc_1(A_2180, B_2185)=k1_xboole_0 | k4_zfmisc_1(A_2180, B_2185, C_2183, C_2179)!=k3_zfmisc_1(D_2184, E_2181, F_2182))), inference(superposition, [status(thm), theory('equality')], [c_9510, c_9664])).
% 8.79/3.11  tff(c_10926, plain, (![E_2181, D_2184, F_2182]: (E_2181='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2184, E_2181, F_2182))), inference(superposition, [status(thm), theory('equality')], [c_9325, c_10908])).
% 8.79/3.11  tff(c_10996, plain, (![E_2193, D_2194, F_2195]: (E_2193='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2194, E_2193, F_2195))), inference(negUnitSimplification, [status(thm)], [c_10565, c_10840, c_30, c_10926])).
% 8.79/3.11  tff(c_11002, plain, (![C_5, A_3, B_4, C_2013]: (C_5='#skF_7' | k4_zfmisc_1(A_3, B_4, C_5, C_2013)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9510, c_10996])).
% 8.79/3.11  tff(c_11032, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_11002])).
% 8.79/3.11  tff(c_11089, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11032, c_9325])).
% 8.79/3.11  tff(c_9711, plain, (![E_2060, F_2063, A_2061, D_2062, B_2059, C_2064]: (D_2062=A_2061 | k1_xboole_0=C_2064 | k1_xboole_0=B_2059 | k1_xboole_0=A_2061 | k3_zfmisc_1(D_2062, E_2060, F_2063)!=k3_zfmisc_1(A_2061, B_2059, C_2064))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.11  tff(c_11333, plain, (![C_2239, E_2245, C_2243, F_2240, B_2244, A_2242, D_2241]: (k2_zfmisc_1(A_2242, B_2244)=D_2241 | k1_xboole_0=C_2239 | k1_xboole_0=C_2243 | k2_zfmisc_1(A_2242, B_2244)=k1_xboole_0 | k4_zfmisc_1(A_2242, B_2244, C_2243, C_2239)!=k3_zfmisc_1(D_2241, E_2245, F_2240))), inference(superposition, [status(thm), theory('equality')], [c_9510, c_9711])).
% 8.79/3.11  tff(c_11336, plain, (![D_2241, E_2245, F_2240]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_2241 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2241, E_2245, F_2240))), inference(superposition, [status(thm), theory('equality')], [c_11089, c_11333])).
% 8.79/3.11  tff(c_11377, plain, (![D_2246, E_2247, F_2248]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_2246 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2246, E_2247, F_2248))), inference(negUnitSimplification, [status(thm)], [c_10565, c_32, c_30, c_11336])).
% 8.79/3.11  tff(c_11383, plain, (![A_3, B_4, C_5, C_2013]: (k2_zfmisc_1(A_3, B_4)=k2_zfmisc_1('#skF_1', '#skF_6') | k4_zfmisc_1(A_3, B_4, C_5, C_2013)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9510, c_11377])).
% 8.79/3.11  tff(c_11396, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_11383])).
% 8.79/3.11  tff(c_11436, plain, (![C_5, C_2013]: (k3_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_5, C_2013)=k4_zfmisc_1('#skF_1', '#skF_6', C_5, C_2013))), inference(superposition, [status(thm), theory('equality')], [c_11396, c_9510])).
% 8.79/3.11  tff(c_11560, plain, (![C_2255, C_2256]: (k4_zfmisc_1('#skF_1', '#skF_6', C_2255, C_2256)=k4_zfmisc_1('#skF_1', '#skF_2', C_2255, C_2256))), inference(demodulation, [status(thm), theory('equality')], [c_9510, c_11436])).
% 8.79/3.11  tff(c_11612, plain, (![C_2255, C_2256]: (k4_zfmisc_1('#skF_1', '#skF_2', C_2255, C_2256)!=k1_xboole_0 | k1_xboole_0=C_2256 | k1_xboole_0=C_2255 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11560, c_18])).
% 8.79/3.11  tff(c_11649, plain, (![C_2255, C_2256]: (k4_zfmisc_1('#skF_1', '#skF_2', C_2255, C_2256)!=k1_xboole_0 | k1_xboole_0=C_2256 | k1_xboole_0=C_2255 | k1_xboole_0='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_36, c_11612])).
% 8.79/3.11  tff(c_11722, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_11649])).
% 8.79/3.11  tff(c_11429, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11396, c_10565])).
% 8.79/3.11  tff(c_11726, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11722, c_11429])).
% 8.79/3.11  tff(c_11758, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11722, c_11722, c_4])).
% 8.79/3.11  tff(c_11809, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11758, c_11396])).
% 8.79/3.11  tff(c_11864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11726, c_11809])).
% 8.79/3.11  tff(c_11866, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_11649])).
% 8.79/3.11  tff(c_11439, plain, (![C_5]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_5)=k3_zfmisc_1('#skF_1', '#skF_6', C_5))), inference(superposition, [status(thm), theory('equality')], [c_11396, c_8])).
% 8.79/3.11  tff(c_11451, plain, (![C_2253]: (k3_zfmisc_1('#skF_1', '#skF_6', C_2253)=k3_zfmisc_1('#skF_1', '#skF_2', C_2253))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11439])).
% 8.79/3.11  tff(c_11506, plain, (![E_14, C_2253, D_13, F_15]: (E_14='#skF_6' | k1_xboole_0=C_2253 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_2253))), inference(superposition, [status(thm), theory('equality')], [c_11451, c_14])).
% 8.79/3.11  tff(c_11543, plain, (![E_14, C_2253, D_13, F_15]: (E_14='#skF_6' | k1_xboole_0=C_2253 | k1_xboole_0='#skF_6' | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_2253))), inference(negUnitSimplification, [status(thm)], [c_36, c_11506])).
% 8.79/3.11  tff(c_12035, plain, (![E_14, C_2253, D_13, F_15]: (E_14='#skF_6' | k1_xboole_0=C_2253 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_2253))), inference(negUnitSimplification, [status(thm)], [c_11866, c_11543])).
% 8.79/3.11  tff(c_12038, plain, (![C_2253]: ('#skF_6'='#skF_2' | k1_xboole_0=C_2253)), inference(reflexivity, [status(thm), theory('equality')], [c_12035])).
% 8.79/3.11  tff(c_12066, plain, (![C_2309]: (k1_xboole_0=C_2309)), inference(negUnitSimplification, [status(thm)], [c_9330, c_12038])).
% 8.79/3.11  tff(c_12187, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_12066, c_11429])).
% 8.79/3.11  tff(c_12188, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_9577])).
% 8.79/3.11  tff(c_12222, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_12188])).
% 8.79/3.11  tff(c_12239, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12222, c_36])).
% 8.79/3.11  tff(c_12236, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12222, c_34])).
% 8.79/3.11  tff(c_12238, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12222, c_32])).
% 8.79/3.11  tff(c_12237, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12222, c_30])).
% 8.79/3.11  tff(c_12189, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_9577])).
% 8.79/3.11  tff(c_12402, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12222, c_12189])).
% 8.79/3.11  tff(c_9457, plain, (![A_2020, B_2021, C_2022, D_2023]: (k2_zfmisc_1(k3_zfmisc_1(A_2020, B_2021, C_2022), D_2023)=k4_zfmisc_1(A_2020, B_2021, C_2022, D_2023))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.79/3.11  tff(c_9466, plain, (![D_2023, A_2020, B_2021, C_2022]: (k1_xboole_0=D_2023 | k3_zfmisc_1(A_2020, B_2021, C_2022)=k1_xboole_0 | k4_zfmisc_1(A_2020, B_2021, C_2022, D_2023)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9457, c_2])).
% 8.79/3.11  tff(c_12571, plain, (![D_2623, A_2624, B_2625, C_2626]: (D_2623='#skF_7' | k3_zfmisc_1(A_2624, B_2625, C_2626)='#skF_7' | k4_zfmisc_1(A_2624, B_2625, C_2626, D_2623)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12222, c_12222, c_12222, c_9466])).
% 8.79/3.11  tff(c_12586, plain, ('#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_12402, c_12571])).
% 8.79/3.11  tff(c_12597, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_12237, c_12586])).
% 8.79/3.11  tff(c_12527, plain, (![B_2618, A_2619]: (B_2618='#skF_7' | A_2619='#skF_7' | k2_zfmisc_1(A_2619, B_2618)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12222, c_12222, c_12222, c_2])).
% 8.79/3.11  tff(c_12539, plain, (![C_5, A_3, B_4]: (C_5='#skF_7' | k2_zfmisc_1(A_3, B_4)='#skF_7' | k3_zfmisc_1(A_3, B_4, C_5)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8, c_12527])).
% 8.79/3.11  tff(c_12676, plain, ('#skF_7'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_12597, c_12539])).
% 8.79/3.11  tff(c_12697, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_12238, c_12676])).
% 8.79/3.11  tff(c_12229, plain, (![B_2, A_1]: (B_2='#skF_7' | A_1='#skF_7' | k2_zfmisc_1(A_1, B_2)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12222, c_12222, c_12222, c_2])).
% 8.79/3.11  tff(c_12705, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12697, c_12229])).
% 8.79/3.11  tff(c_12717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12239, c_12236, c_12705])).
% 8.79/3.11  tff(c_12718, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12188])).
% 8.79/3.11  tff(c_12736, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_36])).
% 8.79/3.11  tff(c_12735, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_32])).
% 8.79/3.11  tff(c_12734, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_30])).
% 8.79/3.11  tff(c_12900, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_12189])).
% 8.79/3.11  tff(c_13074, plain, (![D_2669, A_2670, B_2671, C_2672]: (D_2669='#skF_6' | k3_zfmisc_1(A_2670, B_2671, C_2672)='#skF_6' | k4_zfmisc_1(A_2670, B_2671, C_2672, D_2669)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_12718, c_12718, c_9466])).
% 8.79/3.11  tff(c_13089, plain, ('#skF_6'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_12900, c_13074])).
% 8.79/3.11  tff(c_13100, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_12734, c_13089])).
% 8.79/3.11  tff(c_13029, plain, (![B_2664, A_2665]: (B_2664='#skF_6' | A_2665='#skF_6' | k2_zfmisc_1(A_2665, B_2664)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_12718, c_12718, c_2])).
% 8.79/3.11  tff(c_13041, plain, (![C_5, A_3, B_4]: (C_5='#skF_6' | k2_zfmisc_1(A_3, B_4)='#skF_6' | k3_zfmisc_1(A_3, B_4, C_5)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8, c_13029])).
% 8.79/3.11  tff(c_13104, plain, ('#skF_6'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_13100, c_13041])).
% 8.79/3.11  tff(c_13124, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_12735, c_13104])).
% 8.79/3.11  tff(c_12726, plain, (![B_2, A_1]: (B_2='#skF_6' | A_1='#skF_6' | k2_zfmisc_1(A_1, B_2)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_12718, c_12718, c_2])).
% 8.79/3.11  tff(c_13132, plain, ('#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13124, c_12726])).
% 8.79/3.11  tff(c_13144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12736, c_9330, c_13132])).
% 8.79/3.11  tff(c_13146, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_9323])).
% 8.79/3.11  tff(c_13151, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13146, c_9325])).
% 8.79/3.11  tff(c_13282, plain, (![A_2687, B_2688, C_2689, D_2690]: (k2_zfmisc_1(k3_zfmisc_1(A_2687, B_2688, C_2689), D_2690)=k4_zfmisc_1(A_2687, B_2688, C_2689, D_2690))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.79/3.11  tff(c_13288, plain, (![A_2687, C_2689, D_2690, B_2688, C_5]: (k3_zfmisc_1(k3_zfmisc_1(A_2687, B_2688, C_2689), D_2690, C_5)=k2_zfmisc_1(k4_zfmisc_1(A_2687, B_2688, C_2689, D_2690), C_5))), inference(superposition, [status(thm), theory('equality')], [c_13282, c_8])).
% 8.79/3.11  tff(c_13198, plain, (![A_2678, B_2679, C_2680]: (k2_zfmisc_1(k2_zfmisc_1(A_2678, B_2679), C_2680)=k3_zfmisc_1(A_2678, B_2679, C_2680))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.79/3.11  tff(c_13214, plain, (![A_3, B_4, C_5, C_2680]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_2680)=k2_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), C_2680))), inference(superposition, [status(thm), theory('equality')], [c_8, c_13198])).
% 8.79/3.11  tff(c_13336, plain, (![A_2694, B_2695, C_2696, C_2697]: (k3_zfmisc_1(k2_zfmisc_1(A_2694, B_2695), C_2696, C_2697)=k4_zfmisc_1(A_2694, B_2695, C_2696, C_2697))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13214])).
% 8.79/3.11  tff(c_13370, plain, (![A_3, C_5, C_2696, B_4, C_2697]: (k4_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_2696, C_2697)=k3_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), C_2696, C_2697))), inference(superposition, [status(thm), theory('equality')], [c_8, c_13336])).
% 8.79/3.11  tff(c_13554, plain, (![B_2725, C_2722, C_2721, A_2723, C_2724]: (k4_zfmisc_1(k2_zfmisc_1(A_2723, B_2725), C_2724, C_2721, C_2722)=k2_zfmisc_1(k4_zfmisc_1(A_2723, B_2725, C_2724, C_2721), C_2722))), inference(demodulation, [status(thm), theory('equality')], [c_13288, c_13370])).
% 8.79/3.11  tff(c_13991, plain, (![A_2791, C_2788, C_2787, C_2789, B_2790]: (k2_zfmisc_1(k4_zfmisc_1(A_2791, B_2790, C_2788, C_2787), C_2789)!=k1_xboole_0 | k1_xboole_0=C_2789 | k1_xboole_0=C_2787 | k1_xboole_0=C_2788 | k2_zfmisc_1(A_2791, B_2790)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13554, c_18])).
% 8.79/3.11  tff(c_14000, plain, (![C_2789]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_2789)!=k1_xboole_0 | k1_xboole_0=C_2789 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13151, c_13991])).
% 8.79/3.11  tff(c_14019, plain, (![C_2789]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_2789)!=k1_xboole_0 | k1_xboole_0=C_2789 | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_30, c_14000])).
% 8.79/3.11  tff(c_14033, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14019])).
% 8.79/3.11  tff(c_14046, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14033, c_2])).
% 8.79/3.11  tff(c_14055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_14046])).
% 8.79/3.11  tff(c_14057, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_14019])).
% 8.79/3.11  tff(c_13145, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_9323])).
% 8.79/3.11  tff(c_13335, plain, (![A_3, B_4, C_5, C_2680]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_2680)=k4_zfmisc_1(A_3, B_4, C_5, C_2680))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13214])).
% 8.79/3.11  tff(c_13442, plain, (![C_2711, E_2707, D_2709, A_2708, F_2710, B_2706]: (E_2707=B_2706 | k1_xboole_0=C_2711 | k1_xboole_0=B_2706 | k1_xboole_0=A_2708 | k3_zfmisc_1(D_2709, E_2707, F_2710)!=k3_zfmisc_1(A_2708, B_2706, C_2711))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.11  tff(c_13868, plain, (![B_2771, A_2767, C_2766, C_2769, A_2770, B_2768, C_2765]: (C_2769=B_2768 | k1_xboole_0=C_2765 | k1_xboole_0=B_2768 | k1_xboole_0=A_2770 | k4_zfmisc_1(A_2767, B_2771, C_2769, C_2766)!=k3_zfmisc_1(A_2770, B_2768, C_2765))), inference(superposition, [status(thm), theory('equality')], [c_13335, c_13442])).
% 8.79/3.11  tff(c_13949, plain, (![B_2779, C_2780, A_2781]: (B_2779='#skF_7' | k1_xboole_0=C_2780 | k1_xboole_0=B_2779 | k1_xboole_0=A_2781 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_2781, B_2779, C_2780))), inference(superposition, [status(thm), theory('equality')], [c_13151, c_13868])).
% 8.79/3.11  tff(c_13955, plain, (![C_5, C_2680, A_3, B_4]: (C_5='#skF_7' | k1_xboole_0=C_2680 | k1_xboole_0=C_5 | k2_zfmisc_1(A_3, B_4)=k1_xboole_0 | k4_zfmisc_1(A_3, B_4, C_5, C_2680)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13335, c_13949])).
% 8.79/3.11  tff(c_14523, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_13955])).
% 8.79/3.11  tff(c_14525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14057, c_32, c_30, c_13145, c_14523])).
% 8.79/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.11  
% 8.79/3.11  Inference rules
% 8.79/3.11  ----------------------
% 8.79/3.11  #Ref     : 42
% 8.79/3.11  #Sup     : 3640
% 8.79/3.11  #Fact    : 0
% 8.79/3.11  #Define  : 0
% 8.79/3.11  #Split   : 33
% 8.79/3.11  #Chain   : 0
% 8.79/3.11  #Close   : 0
% 8.79/3.11  
% 8.79/3.11  Ordering : KBO
% 8.79/3.11  
% 8.79/3.11  Simplification rules
% 8.79/3.11  ----------------------
% 8.79/3.11  #Subsume      : 972
% 8.79/3.11  #Demod        : 3241
% 8.79/3.11  #Tautology    : 1680
% 8.79/3.11  #SimpNegUnit  : 248
% 8.79/3.11  #BackRed      : 696
% 8.79/3.11  
% 8.79/3.11  #Partial instantiations: 1240
% 8.79/3.11  #Strategies tried      : 1
% 8.79/3.11  
% 8.79/3.11  Timing (in seconds)
% 8.79/3.11  ----------------------
% 8.79/3.11  Preprocessing        : 0.29
% 8.79/3.11  Parsing              : 0.15
% 8.79/3.11  CNF conversion       : 0.02
% 8.79/3.11  Main loop            : 2.00
% 8.79/3.11  Inferencing          : 0.58
% 8.79/3.11  Reduction            : 0.55
% 8.79/3.11  Demodulation         : 0.39
% 8.79/3.11  BG Simplification    : 0.07
% 8.79/3.11  Subsumption          : 0.68
% 8.79/3.11  Abstraction          : 0.10
% 8.79/3.11  MUC search           : 0.00
% 8.79/3.11  Cooper               : 0.00
% 8.79/3.11  Total                : 2.37
% 8.79/3.11  Index Insertion      : 0.00
% 8.79/3.11  Index Deletion       : 0.00
% 8.79/3.11  Index Matching       : 0.00
% 8.79/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
