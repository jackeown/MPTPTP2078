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
% DateTime   : Thu Dec  3 10:09:47 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :  276 (7717 expanded)
%              Number of leaves         :   22 (2392 expanded)
%              Depth                    :   29
%              Number of atoms          :  527 (20742 expanded)
%              Number of equality atoms :  510 (20725 expanded)
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

tff(f_99,negated_conjecture,(
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

tff(f_27,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_114,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_zfmisc_1(k3_zfmisc_1(A_4,B_5,C_6),D_7) = k4_zfmisc_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [A_45,B_46,C_47] : k2_zfmisc_1(k2_zfmisc_1(A_45,B_46),C_47) = k3_zfmisc_1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_172,plain,(
    ! [A_45,B_46,C_47,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_45,B_46),C_47,C_3) = k2_zfmisc_1(k3_zfmisc_1(A_45,B_46,C_47),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2])).

tff(c_241,plain,(
    ! [A_45,B_46,C_47,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_45,B_46),C_47,C_3) = k4_zfmisc_1(A_45,B_46,C_47,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_172])).

tff(c_46,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_288,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k4_zfmisc_1(A_60,B_61,C_62,D_63) != k1_xboole_0
      | k1_xboole_0 = D_63
      | k1_xboole_0 = C_62
      | k1_xboole_0 = B_61
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_291,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_288])).

tff(c_440,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_445,plain,(
    ! [E_84,C_79,B_81,F_82,D_83,A_80] :
      ( F_82 = C_79
      | k3_zfmisc_1(A_80,B_81,C_79) = k1_xboole_0
      | k3_zfmisc_1(D_83,E_84,F_82) != k3_zfmisc_1(A_80,B_81,C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_861,plain,(
    ! [C_137,A_134,B_133,C_136,B_132,A_131,C_135] :
      ( C_137 = C_136
      | k3_zfmisc_1(A_131,B_132,C_137) = k1_xboole_0
      | k4_zfmisc_1(A_134,B_133,C_135,C_136) != k3_zfmisc_1(A_131,B_132,C_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_445])).

tff(c_995,plain,(
    ! [C_147,A_148,B_149] :
      ( C_147 = '#skF_8'
      | k3_zfmisc_1(A_148,B_149,C_147) = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_148,B_149,C_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_861])).

tff(c_1001,plain,(
    ! [C_3,A_45,B_46,C_47] :
      ( C_3 = '#skF_8'
      | k3_zfmisc_1(k2_zfmisc_1(A_45,B_46),C_47,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_45,B_46,C_47,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_995])).

tff(c_1012,plain,(
    ! [C_3,A_45,B_46,C_47] :
      ( C_3 = '#skF_8'
      | k4_zfmisc_1(A_45,B_46,C_47,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_45,B_46,C_47,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_1001])).

tff(c_1243,plain,
    ( '#skF_8' = '#skF_4'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1012])).

tff(c_1244,plain,(
    '#skF_8' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_1243])).

tff(c_671,plain,(
    ! [D_104,E_105,A_101,B_102,C_100,F_103] :
      ( E_105 = B_102
      | k3_zfmisc_1(A_101,B_102,C_100) = k1_xboole_0
      | k3_zfmisc_1(D_104,E_105,F_103) != k3_zfmisc_1(A_101,B_102,C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_683,plain,(
    ! [D_104,C_3,C_47,A_45,E_105,B_46,F_103] :
      ( E_105 = C_47
      | k3_zfmisc_1(k2_zfmisc_1(A_45,B_46),C_47,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_45,B_46,C_47,C_3) != k3_zfmisc_1(D_104,E_105,F_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_671])).

tff(c_1017,plain,(
    ! [A_152,B_150,F_153,C_154,E_151,D_155,C_156] :
      ( E_151 = C_154
      | k4_zfmisc_1(A_152,B_150,C_154,C_156) = k1_xboole_0
      | k4_zfmisc_1(A_152,B_150,C_154,C_156) != k3_zfmisc_1(D_155,E_151,F_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_683])).

tff(c_1032,plain,(
    ! [E_151,D_155,F_153] :
      ( E_151 = '#skF_7'
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_155,E_151,F_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1017])).

tff(c_1056,plain,(
    ! [E_151,D_155,F_153] :
      ( E_151 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_155,E_151,F_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1032])).

tff(c_1062,plain,(
    ! [E_157,D_158,F_159] :
      ( E_157 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_158,E_157,F_159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_1056])).

tff(c_1068,plain,(
    ! [C_47,A_45,B_46,C_3] :
      ( C_47 = '#skF_7'
      | k4_zfmisc_1(A_45,B_46,C_47,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_1062])).

tff(c_1080,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1068])).

tff(c_1107,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_46])).

tff(c_1279,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1107])).

tff(c_403,plain,(
    ! [A_74,D_77,B_75,C_73,F_76,E_78] :
      ( D_77 = A_74
      | k3_zfmisc_1(A_74,B_75,C_73) = k1_xboole_0
      | k3_zfmisc_1(D_77,E_78,F_76) != k3_zfmisc_1(A_74,B_75,C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_415,plain,(
    ! [D_77,C_3,C_47,A_45,F_76,B_46,E_78] :
      ( k2_zfmisc_1(A_45,B_46) = D_77
      | k3_zfmisc_1(k2_zfmisc_1(A_45,B_46),C_47,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_45,B_46,C_47,C_3) != k3_zfmisc_1(D_77,E_78,F_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_403])).

tff(c_3092,plain,(
    ! [C_379,C_381,A_377,E_380,D_378,B_376,F_375] :
      ( k2_zfmisc_1(A_377,B_376) = D_378
      | k4_zfmisc_1(A_377,B_376,C_379,C_381) = k1_xboole_0
      | k4_zfmisc_1(A_377,B_376,C_379,C_381) != k3_zfmisc_1(D_378,E_380,F_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_415])).

tff(c_3095,plain,(
    ! [D_378,E_380,F_375] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_378
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_378,E_380,F_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1279,c_3092])).

tff(c_3129,plain,(
    ! [D_378,E_380,F_375] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_378
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_378,E_380,F_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_3095])).

tff(c_3137,plain,(
    ! [D_382,E_383,F_384] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_382
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_382,E_383,F_384) ) ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_3129])).

tff(c_3143,plain,(
    ! [A_45,B_46,C_47,C_3] :
      ( k2_zfmisc_1(A_45,B_46) = k2_zfmisc_1('#skF_5','#skF_6')
      | k4_zfmisc_1(A_45,B_46,C_47,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_3137])).

tff(c_3155,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3143])).

tff(c_3196,plain,(
    ! [C_3] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_3) = k3_zfmisc_1('#skF_5','#skF_6',C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_3155,c_2])).

tff(c_3204,plain,(
    ! [C_389] : k3_zfmisc_1('#skF_5','#skF_6',C_389) = k3_zfmisc_1('#skF_1','#skF_2',C_389) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3196])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10] :
      ( k3_zfmisc_1(A_8,B_9,C_10) != k1_xboole_0
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3303,plain,(
    ! [C_389] :
      ( k3_zfmisc_1('#skF_1','#skF_2',C_389) != k1_xboole_0
      | k1_xboole_0 = C_389
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3204,c_6])).

tff(c_3457,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3303])).

tff(c_12,plain,(
    ! [B_9,C_10] : k3_zfmisc_1(k1_xboole_0,B_9,C_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3545,plain,(
    ! [B_9,C_10] : k3_zfmisc_1('#skF_5',B_9,C_10) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3457,c_3457,c_12])).

tff(c_3201,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_5','#skF_6',C_3) = k3_zfmisc_1('#skF_1','#skF_2',C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3196])).

tff(c_3635,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_1','#skF_2',C_3) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3545,c_3201])).

tff(c_188,plain,(
    ! [A_48,B_49,C_50,D_51] : k2_zfmisc_1(k3_zfmisc_1(A_48,B_49,C_50),D_51) = k4_zfmisc_1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_312,plain,(
    ! [C_67,A_66,C_68,D_64,B_65] : k3_zfmisc_1(k3_zfmisc_1(A_66,B_65,C_67),D_64,C_68) = k2_zfmisc_1(k4_zfmisc_1(A_66,B_65,C_67,D_64),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_1362,plain,(
    ! [C_196,B_192,A_193,D_195,C_194] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_193,B_192,C_194,D_195),C_196) != k1_xboole_0
      | k1_xboole_0 = C_196
      | k1_xboole_0 = D_195
      | k3_zfmisc_1(A_193,B_192,C_194) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_6])).

tff(c_1365,plain,(
    ! [C_196] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_196) != k1_xboole_0
      | k1_xboole_0 = C_196
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1279,c_1362])).

tff(c_1388,plain,(
    ! [C_196] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_196) != k1_xboole_0
      | k1_xboole_0 = C_196
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1365])).

tff(c_1436,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1388])).

tff(c_1482,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_6])).

tff(c_1498,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1482])).

tff(c_1501,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1498])).

tff(c_1515,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_440])).

tff(c_30,plain,(
    ! [A_23,B_24,D_26] : k4_zfmisc_1(A_23,B_24,k1_xboole_0,D_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_8,B_9] : k3_zfmisc_1(A_8,B_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_200,plain,(
    ! [A_8,B_9,D_51] : k4_zfmisc_1(A_8,B_9,k1_xboole_0,D_51) = k2_zfmisc_1(k1_xboole_0,D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_188])).

tff(c_209,plain,(
    ! [D_51] : k2_zfmisc_1(k1_xboole_0,D_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_200])).

tff(c_1485,plain,(
    ! [D_7] : k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_7) = k2_zfmisc_1(k1_xboole_0,D_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_4])).

tff(c_1499,plain,(
    ! [D_7] : k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_1485])).

tff(c_1793,plain,(
    ! [D_7] : k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_1499])).

tff(c_1794,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1793,c_1279])).

tff(c_2073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1515,c_1794])).

tff(c_2074,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1498])).

tff(c_2089,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_440])).

tff(c_2366,plain,(
    ! [D_7] : k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_7) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_1499])).

tff(c_2367,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2366,c_1279])).

tff(c_2434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2089,c_2367])).

tff(c_2436,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1388])).

tff(c_3203,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_2436])).

tff(c_3506,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3457,c_3203])).

tff(c_3808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3506])).

tff(c_3810,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3303])).

tff(c_22,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] :
      ( E_21 = B_18
      | k3_zfmisc_1(A_17,B_18,C_19) = k1_xboole_0
      | k3_zfmisc_1(D_20,E_21,F_22) != k3_zfmisc_1(A_17,B_18,C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3285,plain,(
    ! [E_21,C_389,D_20,F_22] :
      ( E_21 = '#skF_6'
      | k3_zfmisc_1('#skF_5','#skF_6',C_389) = k1_xboole_0
      | k3_zfmisc_1(D_20,E_21,F_22) != k3_zfmisc_1('#skF_1','#skF_2',C_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3204,c_22])).

tff(c_3325,plain,(
    ! [E_21,C_389,D_20,F_22] :
      ( E_21 = '#skF_6'
      | k3_zfmisc_1('#skF_1','#skF_2',C_389) = k1_xboole_0
      | k3_zfmisc_1(D_20,E_21,F_22) != k3_zfmisc_1('#skF_1','#skF_2',C_389) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_3285])).

tff(c_4261,plain,(
    ! [C_389] :
      ( '#skF_6' = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_2',C_389) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3325])).

tff(c_4288,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4261])).

tff(c_4344,plain,(
    ! [C_463] : k3_zfmisc_1('#skF_5','#skF_2',C_463) = k3_zfmisc_1('#skF_1','#skF_2',C_463) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_3201])).

tff(c_18,plain,(
    ! [F_16,D_14,E_15,B_12,A_11,C_13] :
      ( D_14 = A_11
      | k1_xboole_0 = C_13
      | k1_xboole_0 = B_12
      | k1_xboole_0 = A_11
      | k3_zfmisc_1(D_14,E_15,F_16) != k3_zfmisc_1(A_11,B_12,C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4425,plain,(
    ! [D_14,C_463,E_15,F_16] :
      ( D_14 = '#skF_5'
      | k1_xboole_0 = C_463
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | k3_zfmisc_1(D_14,E_15,F_16) != k3_zfmisc_1('#skF_1','#skF_2',C_463) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4344,c_18])).

tff(c_4478,plain,(
    ! [D_14,C_463,E_15,F_16] :
      ( D_14 = '#skF_5'
      | k1_xboole_0 = C_463
      | k3_zfmisc_1(D_14,E_15,F_16) != k3_zfmisc_1('#skF_1','#skF_2',C_463) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3810,c_42,c_4425])).

tff(c_4702,plain,(
    ! [C_463] :
      ( '#skF_5' = '#skF_1'
      | k1_xboole_0 = C_463 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4478])).

tff(c_4758,plain,(
    ! [C_486] : k1_xboole_0 = C_486 ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_4702])).

tff(c_4879,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4758,c_3203])).

tff(c_4880,plain,(
    ! [C_389] : k3_zfmisc_1('#skF_1','#skF_2',C_389) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4261])).

tff(c_4889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_3203])).

tff(c_4891,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k4_zfmisc_1(A_23,B_24,C_25,D_26) != k1_xboole_0
      | k1_xboole_0 = D_26
      | k1_xboole_0 = C_25
      | k1_xboole_0 = B_24
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4898,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4891,c_26])).

tff(c_4905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_4898])).

tff(c_4906,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_4912,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4906])).

tff(c_4972,plain,(
    ! [A_781,B_782,C_783] : k2_zfmisc_1(k2_zfmisc_1(A_781,B_782),C_783) = k3_zfmisc_1(A_781,B_782,C_783) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4975,plain,(
    ! [A_781,B_782,C_783,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_781,B_782),C_783,C_3) = k2_zfmisc_1(k3_zfmisc_1(A_781,B_782,C_783),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4972,c_2])).

tff(c_5092,plain,(
    ! [A_781,B_782,C_783,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_781,B_782),C_783,C_3) = k4_zfmisc_1(A_781,B_782,C_783,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4975])).

tff(c_4907,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_4967,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4907,c_46])).

tff(c_5039,plain,(
    ! [A_792,B_793,C_794,D_795] :
      ( k4_zfmisc_1(A_792,B_793,C_794,D_795) != k1_xboole_0
      | k1_xboole_0 = D_795
      | k1_xboole_0 = C_794
      | k1_xboole_0 = B_793
      | k1_xboole_0 = A_792 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5042,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4967,c_5039])).

tff(c_5055,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_5042])).

tff(c_5065,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5055])).

tff(c_5353,plain,(
    ! [A_827,B_828,F_829,D_830,C_826,E_831] :
      ( F_829 = C_826
      | k3_zfmisc_1(A_827,B_828,C_826) = k1_xboole_0
      | k3_zfmisc_1(D_830,E_831,F_829) != k3_zfmisc_1(A_827,B_828,C_826) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5365,plain,(
    ! [C_3,F_829,B_782,C_783,D_830,A_781,E_831] :
      ( F_829 = C_3
      | k3_zfmisc_1(k2_zfmisc_1(A_781,B_782),C_783,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_781,B_782,C_783,C_3) != k3_zfmisc_1(D_830,E_831,F_829) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5092,c_5353])).

tff(c_5760,plain,(
    ! [B_884,F_882,D_887,C_885,E_881,A_886,C_883] :
      ( F_882 = C_885
      | k4_zfmisc_1(A_886,B_884,C_883,C_885) = k1_xboole_0
      | k4_zfmisc_1(A_886,B_884,C_883,C_885) != k3_zfmisc_1(D_887,E_881,F_882) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5092,c_5365])).

tff(c_5775,plain,(
    ! [F_882,D_887,E_881] :
      ( F_882 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_887,E_881,F_882) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4967,c_5760])).

tff(c_5799,plain,(
    ! [F_882,D_887,E_881] :
      ( F_882 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_887,E_881,F_882) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_5775])).

tff(c_5805,plain,(
    ! [F_888,D_889,E_890] :
      ( F_888 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_889,E_890,F_888) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5065,c_5799])).

tff(c_5811,plain,(
    ! [C_3,A_781,B_782,C_783] :
      ( C_3 = '#skF_8'
      | k4_zfmisc_1(A_781,B_782,C_783,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5092,c_5805])).

tff(c_5823,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5811])).

tff(c_5825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4912,c_5823])).

tff(c_5826,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5055])).

tff(c_5854,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5826])).

tff(c_5869,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5854,c_44])).

tff(c_5866,plain,(
    '#skF_2' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5854,c_42])).

tff(c_5868,plain,(
    '#skF_3' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5854,c_40])).

tff(c_5827,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5055])).

tff(c_5993,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5854,c_5827])).

tff(c_6301,plain,(
    ! [A_950,B_951,C_952,D_953] :
      ( k4_zfmisc_1(A_950,B_951,C_952,D_953) != '#skF_8'
      | D_953 = '#skF_8'
      | C_952 = '#skF_8'
      | B_951 = '#skF_8'
      | A_950 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5854,c_5854,c_5854,c_5854,c_5854,c_26])).

tff(c_6310,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_5993,c_6301])).

tff(c_6324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5869,c_5866,c_5868,c_4912,c_6310])).

tff(c_6325,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5826])).

tff(c_6353,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6325])).

tff(c_6370,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6353,c_44])).

tff(c_6367,plain,(
    '#skF_6' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6353,c_42])).

tff(c_6369,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6353,c_40])).

tff(c_6368,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6353,c_38])).

tff(c_6470,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6353,c_5827])).

tff(c_6839,plain,(
    ! [A_1019,B_1020,C_1021,D_1022] :
      ( k4_zfmisc_1(A_1019,B_1020,C_1021,D_1022) != '#skF_6'
      | D_1022 = '#skF_6'
      | C_1021 = '#skF_6'
      | B_1020 = '#skF_6'
      | A_1019 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6353,c_6353,c_6353,c_6353,c_6353,c_26])).

tff(c_6854,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6470,c_6839])).

tff(c_6866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6370,c_6367,c_6369,c_6368,c_6854])).

tff(c_6867,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6325])).

tff(c_6912,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_44])).

tff(c_6909,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_42])).

tff(c_6911,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_40])).

tff(c_6910,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_38])).

tff(c_7014,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_5827])).

tff(c_7341,plain,(
    ! [A_1082,B_1083,C_1084,D_1085] :
      ( k4_zfmisc_1(A_1082,B_1083,C_1084,D_1085) != '#skF_7'
      | D_1085 = '#skF_7'
      | C_1084 = '#skF_7'
      | B_1083 = '#skF_7'
      | A_1082 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_6867,c_6867,c_6867,c_6867,c_26])).

tff(c_7356,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7014,c_7341])).

tff(c_7368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6912,c_6909,c_6911,c_6910,c_7356])).

tff(c_7369,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4906])).

tff(c_7375,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7369])).

tff(c_7430,plain,(
    ! [A_1092,B_1093,C_1094] : k2_zfmisc_1(k2_zfmisc_1(A_1092,B_1093),C_1094) = k3_zfmisc_1(A_1092,B_1093,C_1094) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7433,plain,(
    ! [A_1092,B_1093,C_1094,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_1092,B_1093),C_1094,C_3) = k2_zfmisc_1(k3_zfmisc_1(A_1092,B_1093,C_1094),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_7430,c_2])).

tff(c_7555,plain,(
    ! [A_1092,B_1093,C_1094,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_1092,B_1093),C_1094,C_3) = k4_zfmisc_1(A_1092,B_1093,C_1094,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7433])).

tff(c_7370,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4906])).

tff(c_7445,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7370,c_4907,c_46])).

tff(c_7490,plain,(
    ! [A_1102,B_1103,C_1104,D_1105] :
      ( k4_zfmisc_1(A_1102,B_1103,C_1104,D_1105) != k1_xboole_0
      | k1_xboole_0 = D_1105
      | k1_xboole_0 = C_1104
      | k1_xboole_0 = B_1103
      | k1_xboole_0 = A_1102 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7493,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7445,c_7490])).

tff(c_7506,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_7493])).

tff(c_7528,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7506])).

tff(c_7556,plain,(
    ! [A_1113,B_1114,C_1115,C_1116] : k3_zfmisc_1(k2_zfmisc_1(A_1113,B_1114),C_1115,C_1116) = k4_zfmisc_1(A_1113,B_1114,C_1115,C_1116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7433])).

tff(c_8125,plain,(
    ! [C_1178,A_1179,A_1180,B_1181,C_1184,B_1182,C_1183] :
      ( C_1184 = B_1181
      | k3_zfmisc_1(A_1180,B_1181,C_1178) = k1_xboole_0
      | k4_zfmisc_1(A_1179,B_1182,C_1184,C_1183) != k3_zfmisc_1(A_1180,B_1181,C_1178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7556,c_22])).

tff(c_8238,plain,(
    ! [B_1191,A_1192,C_1193] :
      ( B_1191 = '#skF_7'
      | k3_zfmisc_1(A_1192,B_1191,C_1193) = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_1192,B_1191,C_1193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7445,c_8125])).

tff(c_8244,plain,(
    ! [C_1094,A_1092,B_1093,C_3] :
      ( C_1094 = '#skF_7'
      | k3_zfmisc_1(k2_zfmisc_1(A_1092,B_1093),C_1094,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1092,B_1093,C_1094,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7555,c_8238])).

tff(c_8255,plain,(
    ! [C_1094,A_1092,B_1093,C_3] :
      ( C_1094 = '#skF_7'
      | k4_zfmisc_1(A_1092,B_1093,C_1094,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1092,B_1093,C_1094,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7555,c_8244])).

tff(c_8301,plain,
    ( '#skF_7' = '#skF_3'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8255])).

tff(c_8302,plain,(
    '#skF_7' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_7528,c_8301])).

tff(c_8337,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8302,c_7445])).

tff(c_7677,plain,(
    ! [D_1126,F_1125,B_1124,C_1122,E_1127,A_1123] :
      ( D_1126 = A_1123
      | k3_zfmisc_1(A_1123,B_1124,C_1122) = k1_xboole_0
      | k3_zfmisc_1(D_1126,E_1127,F_1125) != k3_zfmisc_1(A_1123,B_1124,C_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7689,plain,(
    ! [B_1093,C_1094,D_1126,F_1125,A_1092,C_3,E_1127] :
      ( k2_zfmisc_1(A_1092,B_1093) = D_1126
      | k3_zfmisc_1(k2_zfmisc_1(A_1092,B_1093),C_1094,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1092,B_1093,C_1094,C_3) != k3_zfmisc_1(D_1126,E_1127,F_1125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7555,c_7677])).

tff(c_9830,plain,(
    ! [D_1377,C_1381,F_1379,B_1378,E_1376,C_1375,A_1380] :
      ( k2_zfmisc_1(A_1380,B_1378) = D_1377
      | k4_zfmisc_1(A_1380,B_1378,C_1375,C_1381) = k1_xboole_0
      | k4_zfmisc_1(A_1380,B_1378,C_1375,C_1381) != k3_zfmisc_1(D_1377,E_1376,F_1379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7555,c_7689])).

tff(c_9833,plain,(
    ! [D_1377,E_1376,F_1379] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1377
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1377,E_1376,F_1379) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8337,c_9830])).

tff(c_9867,plain,(
    ! [D_1377,E_1376,F_1379] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1377
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1377,E_1376,F_1379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8337,c_9833])).

tff(c_9875,plain,(
    ! [D_1382,E_1383,F_1384] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1382
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1382,E_1383,F_1384) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7528,c_9867])).

tff(c_9881,plain,(
    ! [A_1092,B_1093,C_1094,C_3] :
      ( k2_zfmisc_1(A_1092,B_1093) = k2_zfmisc_1('#skF_1','#skF_6')
      | k4_zfmisc_1(A_1092,B_1093,C_1094,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7555,c_9875])).

tff(c_9893,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9881])).

tff(c_9933,plain,(
    ! [C_3] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_3) = k3_zfmisc_1('#skF_1','#skF_6',C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_9893,c_2])).

tff(c_9942,plain,(
    ! [C_1389] : k3_zfmisc_1('#skF_1','#skF_6',C_1389) = k3_zfmisc_1('#skF_1','#skF_2',C_1389) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9933])).

tff(c_10044,plain,(
    ! [C_1389] :
      ( k3_zfmisc_1('#skF_1','#skF_2',C_1389) != k1_xboole_0
      | k1_xboole_0 = C_1389
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9942,c_6])).

tff(c_10076,plain,(
    ! [C_1389] :
      ( k3_zfmisc_1('#skF_1','#skF_2',C_1389) != k1_xboole_0
      | k1_xboole_0 = C_1389
      | k1_xboole_0 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_10044])).

tff(c_10080,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10076])).

tff(c_10,plain,(
    ! [A_8,C_10] : k3_zfmisc_1(A_8,k1_xboole_0,C_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10119,plain,(
    ! [A_8,C_10] : k3_zfmisc_1(A_8,'#skF_6',C_10) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10080,c_10080,c_10])).

tff(c_9938,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_1','#skF_6',C_3) = k3_zfmisc_1('#skF_1','#skF_2',C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9933])).

tff(c_10290,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_1','#skF_2',C_3) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10119,c_9938])).

tff(c_7466,plain,(
    ! [A_1098,B_1099,C_1100,D_1101] : k2_zfmisc_1(k3_zfmisc_1(A_1098,B_1099,C_1100),D_1101) = k4_zfmisc_1(A_1098,B_1099,C_1100,D_1101) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7609,plain,(
    ! [A_1117,D_1120,C_1119,C_1118,B_1121] : k3_zfmisc_1(k3_zfmisc_1(A_1117,B_1121,C_1119),D_1120,C_1118) = k2_zfmisc_1(k4_zfmisc_1(A_1117,B_1121,C_1119,D_1120),C_1118) ),
    inference(superposition,[status(thm),theory(equality)],[c_7466,c_2])).

tff(c_8642,plain,(
    ! [C_1251,D_1252,B_1254,A_1250,C_1253] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_1250,B_1254,C_1253,D_1252),C_1251) != k1_xboole_0
      | k1_xboole_0 = C_1251
      | k1_xboole_0 = D_1252
      | k3_zfmisc_1(A_1250,B_1254,C_1253) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7609,c_6])).

tff(c_8645,plain,(
    ! [C_1251] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_1251) != k1_xboole_0
      | k1_xboole_0 = C_1251
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8337,c_8642])).

tff(c_8668,plain,(
    ! [C_1251] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_1251) != k1_xboole_0
      | k1_xboole_0 = C_1251
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_8645])).

tff(c_8727,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8668])).

tff(c_8776,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8727,c_6])).

tff(c_8790,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_8776])).

tff(c_8809,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8790,c_7528])).

tff(c_32,plain,(
    ! [A_23,C_25,D_26] : k4_zfmisc_1(A_23,k1_xboole_0,C_25,D_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8813,plain,(
    ! [A_23,C_25,D_26] : k4_zfmisc_1(A_23,'#skF_6',C_25,D_26) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8790,c_8790,c_32])).

tff(c_9205,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8813,c_8337])).

tff(c_9324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8809,c_9205])).

tff(c_9326,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8668])).

tff(c_9941,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9938,c_9326])).

tff(c_10081,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10080,c_9941])).

tff(c_10458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10290,c_10081])).

tff(c_10460,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10076])).

tff(c_16,plain,(
    ! [F_16,D_14,E_15,B_12,A_11,C_13] :
      ( E_15 = B_12
      | k1_xboole_0 = C_13
      | k1_xboole_0 = B_12
      | k1_xboole_0 = A_11
      | k3_zfmisc_1(D_14,E_15,F_16) != k3_zfmisc_1(A_11,B_12,C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10017,plain,(
    ! [E_15,C_1389,D_14,F_16] :
      ( E_15 = '#skF_6'
      | k1_xboole_0 = C_1389
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_14,E_15,F_16) != k3_zfmisc_1('#skF_1','#skF_2',C_1389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9942,c_16])).

tff(c_10070,plain,(
    ! [E_15,C_1389,D_14,F_16] :
      ( E_15 = '#skF_6'
      | k1_xboole_0 = C_1389
      | k1_xboole_0 = '#skF_6'
      | k3_zfmisc_1(D_14,E_15,F_16) != k3_zfmisc_1('#skF_1','#skF_2',C_1389) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_10017])).

tff(c_10758,plain,(
    ! [E_15,C_1389,D_14,F_16] :
      ( E_15 = '#skF_6'
      | k1_xboole_0 = C_1389
      | k3_zfmisc_1(D_14,E_15,F_16) != k3_zfmisc_1('#skF_1','#skF_2',C_1389) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10460,c_10070])).

tff(c_10761,plain,(
    ! [C_1389] :
      ( '#skF_6' = '#skF_2'
      | k1_xboole_0 = C_1389 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10758])).

tff(c_10841,plain,(
    ! [C_1456] : k1_xboole_0 = C_1456 ),
    inference(negUnitSimplification,[status(thm)],[c_7375,c_10761])).

tff(c_10962,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_10841,c_9941])).

tff(c_10963,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7506])).

tff(c_10965,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_10963])).

tff(c_10979,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10965,c_44])).

tff(c_10976,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10965,c_42])).

tff(c_10978,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10965,c_40])).

tff(c_10977,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10965,c_38])).

tff(c_10964,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7506])).

tff(c_11080,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10965,c_10964])).

tff(c_11452,plain,(
    ! [A_1786,B_1787,C_1788,D_1789] :
      ( k4_zfmisc_1(A_1786,B_1787,C_1788,D_1789) != '#skF_7'
      | D_1789 = '#skF_7'
      | C_1788 = '#skF_7'
      | B_1787 = '#skF_7'
      | A_1786 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10965,c_10965,c_10965,c_10965,c_10965,c_26])).

tff(c_11467,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11080,c_11452])).

tff(c_11479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10979,c_10976,c_10978,c_10977,c_11467])).

tff(c_11480,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10963])).

tff(c_11495,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11480,c_44])).

tff(c_11494,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11480,c_40])).

tff(c_11493,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11480,c_38])).

tff(c_11597,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11480,c_10964])).

tff(c_11969,plain,(
    ! [A_1849,B_1850,C_1851,D_1852] :
      ( k4_zfmisc_1(A_1849,B_1850,C_1851,D_1852) != '#skF_6'
      | D_1852 = '#skF_6'
      | C_1851 = '#skF_6'
      | B_1850 = '#skF_6'
      | A_1849 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11480,c_11480,c_11480,c_11480,c_11480,c_26])).

tff(c_11984,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11597,c_11969])).

tff(c_11996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11495,c_7375,c_11494,c_11493,c_11984])).

tff(c_11997,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7369])).

tff(c_12063,plain,(
    ! [A_1859,B_1860,C_1861] : k2_zfmisc_1(k2_zfmisc_1(A_1859,B_1860),C_1861) = k3_zfmisc_1(A_1859,B_1860,C_1861) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12066,plain,(
    ! [A_1859,B_1860,C_1861,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_1859,B_1860),C_1861,C_3) = k2_zfmisc_1(k3_zfmisc_1(A_1859,B_1860,C_1861),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_12063,c_2])).

tff(c_12161,plain,(
    ! [A_1859,B_1860,C_1861,C_3] : k3_zfmisc_1(k2_zfmisc_1(A_1859,B_1860),C_1861,C_3) = k4_zfmisc_1(A_1859,B_1860,C_1861,C_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12066])).

tff(c_11998,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7369])).

tff(c_11999,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4907,c_7370,c_46])).

tff(c_12004,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11998,c_11999])).

tff(c_12134,plain,(
    ! [A_1870,B_1871,C_1872,D_1873] :
      ( k4_zfmisc_1(A_1870,B_1871,C_1872,D_1873) != k1_xboole_0
      | k1_xboole_0 = D_1873
      | k1_xboole_0 = C_1872
      | k1_xboole_0 = B_1871
      | k1_xboole_0 = A_1870 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12137,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12004,c_12134])).

tff(c_12150,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_38,c_12137])).

tff(c_12160,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12150])).

tff(c_12511,plain,(
    ! [E_1914,D_1913,C_1909,F_1912,B_1911,A_1910] :
      ( E_1914 = B_1911
      | k3_zfmisc_1(A_1910,B_1911,C_1909) = k1_xboole_0
      | k3_zfmisc_1(D_1913,E_1914,F_1912) != k3_zfmisc_1(A_1910,B_1911,C_1909) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12523,plain,(
    ! [E_1914,C_1861,B_1860,C_3,D_1913,F_1912,A_1859] :
      ( E_1914 = C_1861
      | k3_zfmisc_1(k2_zfmisc_1(A_1859,B_1860),C_1861,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1859,B_1860,C_1861,C_3) != k3_zfmisc_1(D_1913,E_1914,F_1912) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12161,c_12511])).

tff(c_13443,plain,(
    ! [B_2004,C_2005,F_2007,A_2002,C_2008,E_2003,D_2006] :
      ( E_2003 = C_2005
      | k4_zfmisc_1(A_2002,B_2004,C_2005,C_2008) = k1_xboole_0
      | k4_zfmisc_1(A_2002,B_2004,C_2005,C_2008) != k3_zfmisc_1(D_2006,E_2003,F_2007) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12161,c_12523])).

tff(c_13458,plain,(
    ! [E_2003,D_2006,F_2007] :
      ( E_2003 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2006,E_2003,F_2007) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12004,c_13443])).

tff(c_13482,plain,(
    ! [E_2003,D_2006,F_2007] :
      ( E_2003 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2006,E_2003,F_2007) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12004,c_13458])).

tff(c_13495,plain,(
    ! [E_2010,D_2011,F_2012] :
      ( E_2010 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2011,E_2010,F_2012) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12160,c_13482])).

tff(c_13501,plain,(
    ! [C_1861,A_1859,B_1860,C_3] :
      ( C_1861 = '#skF_7'
      | k4_zfmisc_1(A_1859,B_1860,C_1861,C_3) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12161,c_13495])).

tff(c_13513,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13501])).

tff(c_13515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11997,c_13513])).

tff(c_13516,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_12150])).

tff(c_13531,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13516,c_44])).

tff(c_13528,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13516,c_42])).

tff(c_13529,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13516,c_38])).

tff(c_13517,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12150])).

tff(c_13632,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13516,c_13517])).

tff(c_13856,plain,(
    ! [A_2057,B_2058,C_2059,D_2060] :
      ( k4_zfmisc_1(A_2057,B_2058,C_2059,D_2060) != '#skF_7'
      | D_2060 = '#skF_7'
      | C_2059 = '#skF_7'
      | B_2058 = '#skF_7'
      | A_2057 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13516,c_13516,c_13516,c_13516,c_13516,c_26])).

tff(c_13871,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13632,c_13856])).

tff(c_13883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13531,c_13528,c_11997,c_13529,c_13871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.95/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/2.88  
% 7.95/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/2.88  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 7.95/2.88  
% 7.95/2.88  %Foreground sorts:
% 7.95/2.88  
% 7.95/2.88  
% 7.95/2.88  %Background operators:
% 7.95/2.88  
% 7.95/2.88  
% 7.95/2.88  %Foreground operators:
% 7.95/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.95/2.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.95/2.88  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 7.95/2.88  tff('#skF_7', type, '#skF_7': $i).
% 7.95/2.88  tff('#skF_5', type, '#skF_5': $i).
% 7.95/2.88  tff('#skF_6', type, '#skF_6': $i).
% 7.95/2.88  tff('#skF_2', type, '#skF_2': $i).
% 7.95/2.88  tff('#skF_3', type, '#skF_3': $i).
% 7.95/2.88  tff('#skF_1', type, '#skF_1': $i).
% 7.95/2.88  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.95/2.88  tff('#skF_8', type, '#skF_8': $i).
% 7.95/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.95/2.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.95/2.88  tff('#skF_4', type, '#skF_4': $i).
% 7.95/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.95/2.88  
% 8.29/2.91  tff(f_99, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_mcart_1)).
% 8.29/2.91  tff(f_27, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.29/2.91  tff(f_29, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 8.29/2.91  tff(f_80, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 8.29/2.91  tff(f_65, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 8.29/2.91  tff(f_41, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 8.29/2.91  tff(f_55, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 8.29/2.91  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.29/2.91  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.29/2.91  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.29/2.91  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.29/2.91  tff(c_36, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.29/2.91  tff(c_114, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_36])).
% 8.29/2.91  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3)=k3_zfmisc_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/2.91  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_zfmisc_1(k3_zfmisc_1(A_4, B_5, C_6), D_7)=k4_zfmisc_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.29/2.91  tff(c_169, plain, (![A_45, B_46, C_47]: (k2_zfmisc_1(k2_zfmisc_1(A_45, B_46), C_47)=k3_zfmisc_1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/2.91  tff(c_172, plain, (![A_45, B_46, C_47, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_45, B_46), C_47, C_3)=k2_zfmisc_1(k3_zfmisc_1(A_45, B_46, C_47), C_3))), inference(superposition, [status(thm), theory('equality')], [c_169, c_2])).
% 8.29/2.91  tff(c_241, plain, (![A_45, B_46, C_47, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_45, B_46), C_47, C_3)=k4_zfmisc_1(A_45, B_46, C_47, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_172])).
% 8.29/2.91  tff(c_46, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.29/2.91  tff(c_288, plain, (![A_60, B_61, C_62, D_63]: (k4_zfmisc_1(A_60, B_61, C_62, D_63)!=k1_xboole_0 | k1_xboole_0=D_63 | k1_xboole_0=C_62 | k1_xboole_0=B_61 | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.29/2.91  tff(c_291, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_46, c_288])).
% 8.29/2.91  tff(c_440, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_291])).
% 8.29/2.91  tff(c_445, plain, (![E_84, C_79, B_81, F_82, D_83, A_80]: (F_82=C_79 | k3_zfmisc_1(A_80, B_81, C_79)=k1_xboole_0 | k3_zfmisc_1(D_83, E_84, F_82)!=k3_zfmisc_1(A_80, B_81, C_79))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.29/2.91  tff(c_861, plain, (![C_137, A_134, B_133, C_136, B_132, A_131, C_135]: (C_137=C_136 | k3_zfmisc_1(A_131, B_132, C_137)=k1_xboole_0 | k4_zfmisc_1(A_134, B_133, C_135, C_136)!=k3_zfmisc_1(A_131, B_132, C_137))), inference(superposition, [status(thm), theory('equality')], [c_241, c_445])).
% 8.29/2.91  tff(c_995, plain, (![C_147, A_148, B_149]: (C_147='#skF_8' | k3_zfmisc_1(A_148, B_149, C_147)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_148, B_149, C_147))), inference(superposition, [status(thm), theory('equality')], [c_46, c_861])).
% 8.29/2.91  tff(c_1001, plain, (![C_3, A_45, B_46, C_47]: (C_3='#skF_8' | k3_zfmisc_1(k2_zfmisc_1(A_45, B_46), C_47, C_3)=k1_xboole_0 | k4_zfmisc_1(A_45, B_46, C_47, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_995])).
% 8.29/2.91  tff(c_1012, plain, (![C_3, A_45, B_46, C_47]: (C_3='#skF_8' | k4_zfmisc_1(A_45, B_46, C_47, C_3)=k1_xboole_0 | k4_zfmisc_1(A_45, B_46, C_47, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_1001])).
% 8.29/2.91  tff(c_1243, plain, ('#skF_8'='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_1012])).
% 8.29/2.91  tff(c_1244, plain, ('#skF_8'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_440, c_1243])).
% 8.29/2.91  tff(c_671, plain, (![D_104, E_105, A_101, B_102, C_100, F_103]: (E_105=B_102 | k3_zfmisc_1(A_101, B_102, C_100)=k1_xboole_0 | k3_zfmisc_1(D_104, E_105, F_103)!=k3_zfmisc_1(A_101, B_102, C_100))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.29/2.91  tff(c_683, plain, (![D_104, C_3, C_47, A_45, E_105, B_46, F_103]: (E_105=C_47 | k3_zfmisc_1(k2_zfmisc_1(A_45, B_46), C_47, C_3)=k1_xboole_0 | k4_zfmisc_1(A_45, B_46, C_47, C_3)!=k3_zfmisc_1(D_104, E_105, F_103))), inference(superposition, [status(thm), theory('equality')], [c_241, c_671])).
% 8.29/2.91  tff(c_1017, plain, (![A_152, B_150, F_153, C_154, E_151, D_155, C_156]: (E_151=C_154 | k4_zfmisc_1(A_152, B_150, C_154, C_156)=k1_xboole_0 | k4_zfmisc_1(A_152, B_150, C_154, C_156)!=k3_zfmisc_1(D_155, E_151, F_153))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_683])).
% 8.29/2.91  tff(c_1032, plain, (![E_151, D_155, F_153]: (E_151='#skF_7' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_155, E_151, F_153))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1017])).
% 8.29/2.91  tff(c_1056, plain, (![E_151, D_155, F_153]: (E_151='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_155, E_151, F_153))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1032])).
% 8.29/2.91  tff(c_1062, plain, (![E_157, D_158, F_159]: (E_157='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_158, E_157, F_159))), inference(negUnitSimplification, [status(thm)], [c_440, c_1056])).
% 8.29/2.91  tff(c_1068, plain, (![C_47, A_45, B_46, C_3]: (C_47='#skF_7' | k4_zfmisc_1(A_45, B_46, C_47, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_1062])).
% 8.29/2.91  tff(c_1080, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_1068])).
% 8.29/2.91  tff(c_1107, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_46])).
% 8.29/2.91  tff(c_1279, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1107])).
% 8.29/2.91  tff(c_403, plain, (![A_74, D_77, B_75, C_73, F_76, E_78]: (D_77=A_74 | k3_zfmisc_1(A_74, B_75, C_73)=k1_xboole_0 | k3_zfmisc_1(D_77, E_78, F_76)!=k3_zfmisc_1(A_74, B_75, C_73))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.29/2.91  tff(c_415, plain, (![D_77, C_3, C_47, A_45, F_76, B_46, E_78]: (k2_zfmisc_1(A_45, B_46)=D_77 | k3_zfmisc_1(k2_zfmisc_1(A_45, B_46), C_47, C_3)=k1_xboole_0 | k4_zfmisc_1(A_45, B_46, C_47, C_3)!=k3_zfmisc_1(D_77, E_78, F_76))), inference(superposition, [status(thm), theory('equality')], [c_241, c_403])).
% 8.29/2.91  tff(c_3092, plain, (![C_379, C_381, A_377, E_380, D_378, B_376, F_375]: (k2_zfmisc_1(A_377, B_376)=D_378 | k4_zfmisc_1(A_377, B_376, C_379, C_381)=k1_xboole_0 | k4_zfmisc_1(A_377, B_376, C_379, C_381)!=k3_zfmisc_1(D_378, E_380, F_375))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_415])).
% 8.29/2.91  tff(c_3095, plain, (![D_378, E_380, F_375]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_378 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_378, E_380, F_375))), inference(superposition, [status(thm), theory('equality')], [c_1279, c_3092])).
% 8.29/2.91  tff(c_3129, plain, (![D_378, E_380, F_375]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_378 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_378, E_380, F_375))), inference(demodulation, [status(thm), theory('equality')], [c_1279, c_3095])).
% 8.29/2.91  tff(c_3137, plain, (![D_382, E_383, F_384]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_382 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_382, E_383, F_384))), inference(negUnitSimplification, [status(thm)], [c_440, c_3129])).
% 8.29/2.91  tff(c_3143, plain, (![A_45, B_46, C_47, C_3]: (k2_zfmisc_1(A_45, B_46)=k2_zfmisc_1('#skF_5', '#skF_6') | k4_zfmisc_1(A_45, B_46, C_47, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_3137])).
% 8.29/2.91  tff(c_3155, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_3143])).
% 8.29/2.91  tff(c_3196, plain, (![C_3]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_3)=k3_zfmisc_1('#skF_5', '#skF_6', C_3))), inference(superposition, [status(thm), theory('equality')], [c_3155, c_2])).
% 8.29/2.91  tff(c_3204, plain, (![C_389]: (k3_zfmisc_1('#skF_5', '#skF_6', C_389)=k3_zfmisc_1('#skF_1', '#skF_2', C_389))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3196])).
% 8.29/2.91  tff(c_6, plain, (![A_8, B_9, C_10]: (k3_zfmisc_1(A_8, B_9, C_10)!=k1_xboole_0 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/2.91  tff(c_3303, plain, (![C_389]: (k3_zfmisc_1('#skF_1', '#skF_2', C_389)!=k1_xboole_0 | k1_xboole_0=C_389 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3204, c_6])).
% 8.29/2.91  tff(c_3457, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3303])).
% 8.29/2.91  tff(c_12, plain, (![B_9, C_10]: (k3_zfmisc_1(k1_xboole_0, B_9, C_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/2.91  tff(c_3545, plain, (![B_9, C_10]: (k3_zfmisc_1('#skF_5', B_9, C_10)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3457, c_3457, c_12])).
% 8.29/2.91  tff(c_3201, plain, (![C_3]: (k3_zfmisc_1('#skF_5', '#skF_6', C_3)=k3_zfmisc_1('#skF_1', '#skF_2', C_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3196])).
% 8.29/2.91  tff(c_3635, plain, (![C_3]: (k3_zfmisc_1('#skF_1', '#skF_2', C_3)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3545, c_3201])).
% 8.29/2.91  tff(c_188, plain, (![A_48, B_49, C_50, D_51]: (k2_zfmisc_1(k3_zfmisc_1(A_48, B_49, C_50), D_51)=k4_zfmisc_1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.29/2.91  tff(c_312, plain, (![C_67, A_66, C_68, D_64, B_65]: (k3_zfmisc_1(k3_zfmisc_1(A_66, B_65, C_67), D_64, C_68)=k2_zfmisc_1(k4_zfmisc_1(A_66, B_65, C_67, D_64), C_68))), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 8.29/2.91  tff(c_1362, plain, (![C_196, B_192, A_193, D_195, C_194]: (k2_zfmisc_1(k4_zfmisc_1(A_193, B_192, C_194, D_195), C_196)!=k1_xboole_0 | k1_xboole_0=C_196 | k1_xboole_0=D_195 | k3_zfmisc_1(A_193, B_192, C_194)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_312, c_6])).
% 8.29/2.91  tff(c_1365, plain, (![C_196]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_196)!=k1_xboole_0 | k1_xboole_0=C_196 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1279, c_1362])).
% 8.29/2.91  tff(c_1388, plain, (![C_196]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_196)!=k1_xboole_0 | k1_xboole_0=C_196 | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_38, c_1365])).
% 8.29/2.91  tff(c_1436, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1388])).
% 8.29/2.91  tff(c_1482, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1436, c_6])).
% 8.29/2.91  tff(c_1498, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_40, c_1482])).
% 8.29/2.91  tff(c_1501, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1498])).
% 8.29/2.91  tff(c_1515, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_440])).
% 8.29/2.91  tff(c_30, plain, (![A_23, B_24, D_26]: (k4_zfmisc_1(A_23, B_24, k1_xboole_0, D_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.29/2.91  tff(c_8, plain, (![A_8, B_9]: (k3_zfmisc_1(A_8, B_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/2.91  tff(c_200, plain, (![A_8, B_9, D_51]: (k4_zfmisc_1(A_8, B_9, k1_xboole_0, D_51)=k2_zfmisc_1(k1_xboole_0, D_51))), inference(superposition, [status(thm), theory('equality')], [c_8, c_188])).
% 8.29/2.91  tff(c_209, plain, (![D_51]: (k2_zfmisc_1(k1_xboole_0, D_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_200])).
% 8.29/2.91  tff(c_1485, plain, (![D_7]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_7)=k2_zfmisc_1(k1_xboole_0, D_7))), inference(superposition, [status(thm), theory('equality')], [c_1436, c_4])).
% 8.29/2.91  tff(c_1499, plain, (![D_7]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_209, c_1485])).
% 8.29/2.91  tff(c_1793, plain, (![D_7]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_1499])).
% 8.29/2.91  tff(c_1794, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1793, c_1279])).
% 8.29/2.91  tff(c_2073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1515, c_1794])).
% 8.29/2.91  tff(c_2074, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1498])).
% 8.29/2.91  tff(c_2089, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_440])).
% 8.29/2.91  tff(c_2366, plain, (![D_7]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_7)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_1499])).
% 8.29/2.91  tff(c_2367, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2366, c_1279])).
% 8.29/2.91  tff(c_2434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2089, c_2367])).
% 8.29/2.91  tff(c_2436, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1388])).
% 8.29/2.91  tff(c_3203, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_2436])).
% 8.29/2.91  tff(c_3506, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3457, c_3203])).
% 8.29/2.91  tff(c_3808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3506])).
% 8.29/2.91  tff(c_3810, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_3303])).
% 8.29/2.91  tff(c_22, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (E_21=B_18 | k3_zfmisc_1(A_17, B_18, C_19)=k1_xboole_0 | k3_zfmisc_1(D_20, E_21, F_22)!=k3_zfmisc_1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.29/2.91  tff(c_3285, plain, (![E_21, C_389, D_20, F_22]: (E_21='#skF_6' | k3_zfmisc_1('#skF_5', '#skF_6', C_389)=k1_xboole_0 | k3_zfmisc_1(D_20, E_21, F_22)!=k3_zfmisc_1('#skF_1', '#skF_2', C_389))), inference(superposition, [status(thm), theory('equality')], [c_3204, c_22])).
% 8.29/2.91  tff(c_3325, plain, (![E_21, C_389, D_20, F_22]: (E_21='#skF_6' | k3_zfmisc_1('#skF_1', '#skF_2', C_389)=k1_xboole_0 | k3_zfmisc_1(D_20, E_21, F_22)!=k3_zfmisc_1('#skF_1', '#skF_2', C_389))), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_3285])).
% 8.29/2.91  tff(c_4261, plain, (![C_389]: ('#skF_6'='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_2', C_389)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_3325])).
% 8.29/2.91  tff(c_4288, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_4261])).
% 8.29/2.91  tff(c_4344, plain, (![C_463]: (k3_zfmisc_1('#skF_5', '#skF_2', C_463)=k3_zfmisc_1('#skF_1', '#skF_2', C_463))), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_3201])).
% 8.29/2.91  tff(c_18, plain, (![F_16, D_14, E_15, B_12, A_11, C_13]: (D_14=A_11 | k1_xboole_0=C_13 | k1_xboole_0=B_12 | k1_xboole_0=A_11 | k3_zfmisc_1(D_14, E_15, F_16)!=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.29/2.91  tff(c_4425, plain, (![D_14, C_463, E_15, F_16]: (D_14='#skF_5' | k1_xboole_0=C_463 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_5' | k3_zfmisc_1(D_14, E_15, F_16)!=k3_zfmisc_1('#skF_1', '#skF_2', C_463))), inference(superposition, [status(thm), theory('equality')], [c_4344, c_18])).
% 8.29/2.91  tff(c_4478, plain, (![D_14, C_463, E_15, F_16]: (D_14='#skF_5' | k1_xboole_0=C_463 | k3_zfmisc_1(D_14, E_15, F_16)!=k3_zfmisc_1('#skF_1', '#skF_2', C_463))), inference(negUnitSimplification, [status(thm)], [c_3810, c_42, c_4425])).
% 8.29/2.91  tff(c_4702, plain, (![C_463]: ('#skF_5'='#skF_1' | k1_xboole_0=C_463)), inference(reflexivity, [status(thm), theory('equality')], [c_4478])).
% 8.29/2.91  tff(c_4758, plain, (![C_486]: (k1_xboole_0=C_486)), inference(negUnitSimplification, [status(thm)], [c_114, c_4702])).
% 8.29/2.91  tff(c_4879, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4758, c_3203])).
% 8.29/2.91  tff(c_4880, plain, (![C_389]: (k3_zfmisc_1('#skF_1', '#skF_2', C_389)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_4261])).
% 8.29/2.91  tff(c_4889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4880, c_3203])).
% 8.29/2.91  tff(c_4891, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_291])).
% 8.29/2.91  tff(c_26, plain, (![A_23, B_24, C_25, D_26]: (k4_zfmisc_1(A_23, B_24, C_25, D_26)!=k1_xboole_0 | k1_xboole_0=D_26 | k1_xboole_0=C_25 | k1_xboole_0=B_24 | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.29/2.91  tff(c_4898, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4891, c_26])).
% 8.29/2.91  tff(c_4905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_4898])).
% 8.29/2.91  tff(c_4906, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 8.29/2.91  tff(c_4912, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_4906])).
% 8.29/2.91  tff(c_4972, plain, (![A_781, B_782, C_783]: (k2_zfmisc_1(k2_zfmisc_1(A_781, B_782), C_783)=k3_zfmisc_1(A_781, B_782, C_783))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/2.91  tff(c_4975, plain, (![A_781, B_782, C_783, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_781, B_782), C_783, C_3)=k2_zfmisc_1(k3_zfmisc_1(A_781, B_782, C_783), C_3))), inference(superposition, [status(thm), theory('equality')], [c_4972, c_2])).
% 8.29/2.91  tff(c_5092, plain, (![A_781, B_782, C_783, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_781, B_782), C_783, C_3)=k4_zfmisc_1(A_781, B_782, C_783, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4975])).
% 8.29/2.91  tff(c_4907, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 8.29/2.91  tff(c_4967, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4907, c_46])).
% 8.29/2.91  tff(c_5039, plain, (![A_792, B_793, C_794, D_795]: (k4_zfmisc_1(A_792, B_793, C_794, D_795)!=k1_xboole_0 | k1_xboole_0=D_795 | k1_xboole_0=C_794 | k1_xboole_0=B_793 | k1_xboole_0=A_792)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.29/2.91  tff(c_5042, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4967, c_5039])).
% 8.29/2.91  tff(c_5055, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_44, c_5042])).
% 8.29/2.91  tff(c_5065, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5055])).
% 8.29/2.91  tff(c_5353, plain, (![A_827, B_828, F_829, D_830, C_826, E_831]: (F_829=C_826 | k3_zfmisc_1(A_827, B_828, C_826)=k1_xboole_0 | k3_zfmisc_1(D_830, E_831, F_829)!=k3_zfmisc_1(A_827, B_828, C_826))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.29/2.91  tff(c_5365, plain, (![C_3, F_829, B_782, C_783, D_830, A_781, E_831]: (F_829=C_3 | k3_zfmisc_1(k2_zfmisc_1(A_781, B_782), C_783, C_3)=k1_xboole_0 | k4_zfmisc_1(A_781, B_782, C_783, C_3)!=k3_zfmisc_1(D_830, E_831, F_829))), inference(superposition, [status(thm), theory('equality')], [c_5092, c_5353])).
% 8.29/2.91  tff(c_5760, plain, (![B_884, F_882, D_887, C_885, E_881, A_886, C_883]: (F_882=C_885 | k4_zfmisc_1(A_886, B_884, C_883, C_885)=k1_xboole_0 | k4_zfmisc_1(A_886, B_884, C_883, C_885)!=k3_zfmisc_1(D_887, E_881, F_882))), inference(demodulation, [status(thm), theory('equality')], [c_5092, c_5365])).
% 8.29/2.91  tff(c_5775, plain, (![F_882, D_887, E_881]: (F_882='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_887, E_881, F_882))), inference(superposition, [status(thm), theory('equality')], [c_4967, c_5760])).
% 8.29/2.91  tff(c_5799, plain, (![F_882, D_887, E_881]: (F_882='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_887, E_881, F_882))), inference(demodulation, [status(thm), theory('equality')], [c_4967, c_5775])).
% 8.29/2.91  tff(c_5805, plain, (![F_888, D_889, E_890]: (F_888='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_889, E_890, F_888))), inference(negUnitSimplification, [status(thm)], [c_5065, c_5799])).
% 8.29/2.91  tff(c_5811, plain, (![C_3, A_781, B_782, C_783]: (C_3='#skF_8' | k4_zfmisc_1(A_781, B_782, C_783, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5092, c_5805])).
% 8.29/2.91  tff(c_5823, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_5811])).
% 8.29/2.91  tff(c_5825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4912, c_5823])).
% 8.29/2.91  tff(c_5826, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_5055])).
% 8.29/2.91  tff(c_5854, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_5826])).
% 8.29/2.91  tff(c_5869, plain, ('#skF_1'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5854, c_44])).
% 8.29/2.91  tff(c_5866, plain, ('#skF_2'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5854, c_42])).
% 8.29/2.91  tff(c_5868, plain, ('#skF_3'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5854, c_40])).
% 8.29/2.91  tff(c_5827, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5055])).
% 8.29/2.91  tff(c_5993, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5854, c_5827])).
% 8.29/2.91  tff(c_6301, plain, (![A_950, B_951, C_952, D_953]: (k4_zfmisc_1(A_950, B_951, C_952, D_953)!='#skF_8' | D_953='#skF_8' | C_952='#skF_8' | B_951='#skF_8' | A_950='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5854, c_5854, c_5854, c_5854, c_5854, c_26])).
% 8.29/2.91  tff(c_6310, plain, ('#skF_8'='#skF_4' | '#skF_3'='#skF_8' | '#skF_2'='#skF_8' | '#skF_1'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_5993, c_6301])).
% 8.29/2.91  tff(c_6324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5869, c_5866, c_5868, c_4912, c_6310])).
% 8.29/2.91  tff(c_6325, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_5826])).
% 8.29/2.91  tff(c_6353, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_6325])).
% 8.29/2.91  tff(c_6370, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6353, c_44])).
% 8.29/2.91  tff(c_6367, plain, ('#skF_6'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6353, c_42])).
% 8.29/2.91  tff(c_6369, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6353, c_40])).
% 8.29/2.91  tff(c_6368, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6353, c_38])).
% 8.29/2.91  tff(c_6470, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6353, c_5827])).
% 8.29/2.91  tff(c_6839, plain, (![A_1019, B_1020, C_1021, D_1022]: (k4_zfmisc_1(A_1019, B_1020, C_1021, D_1022)!='#skF_6' | D_1022='#skF_6' | C_1021='#skF_6' | B_1020='#skF_6' | A_1019='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6353, c_6353, c_6353, c_6353, c_6353, c_26])).
% 8.29/2.91  tff(c_6854, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6470, c_6839])).
% 8.29/2.91  tff(c_6866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6370, c_6367, c_6369, c_6368, c_6854])).
% 8.29/2.91  tff(c_6867, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6325])).
% 8.29/2.91  tff(c_6912, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_44])).
% 8.29/2.91  tff(c_6909, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_42])).
% 8.29/2.91  tff(c_6911, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_40])).
% 8.29/2.91  tff(c_6910, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_38])).
% 8.29/2.91  tff(c_7014, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_5827])).
% 8.29/2.91  tff(c_7341, plain, (![A_1082, B_1083, C_1084, D_1085]: (k4_zfmisc_1(A_1082, B_1083, C_1084, D_1085)!='#skF_7' | D_1085='#skF_7' | C_1084='#skF_7' | B_1083='#skF_7' | A_1082='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_6867, c_6867, c_6867, c_6867, c_26])).
% 8.29/2.91  tff(c_7356, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7014, c_7341])).
% 8.29/2.91  tff(c_7368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6912, c_6909, c_6911, c_6910, c_7356])).
% 8.29/2.91  tff(c_7369, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_4906])).
% 8.29/2.91  tff(c_7375, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_7369])).
% 8.29/2.91  tff(c_7430, plain, (![A_1092, B_1093, C_1094]: (k2_zfmisc_1(k2_zfmisc_1(A_1092, B_1093), C_1094)=k3_zfmisc_1(A_1092, B_1093, C_1094))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/2.91  tff(c_7433, plain, (![A_1092, B_1093, C_1094, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_1092, B_1093), C_1094, C_3)=k2_zfmisc_1(k3_zfmisc_1(A_1092, B_1093, C_1094), C_3))), inference(superposition, [status(thm), theory('equality')], [c_7430, c_2])).
% 8.29/2.91  tff(c_7555, plain, (![A_1092, B_1093, C_1094, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_1092, B_1093), C_1094, C_3)=k4_zfmisc_1(A_1092, B_1093, C_1094, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7433])).
% 8.29/2.91  tff(c_7370, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_4906])).
% 8.29/2.91  tff(c_7445, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7370, c_4907, c_46])).
% 8.29/2.91  tff(c_7490, plain, (![A_1102, B_1103, C_1104, D_1105]: (k4_zfmisc_1(A_1102, B_1103, C_1104, D_1105)!=k1_xboole_0 | k1_xboole_0=D_1105 | k1_xboole_0=C_1104 | k1_xboole_0=B_1103 | k1_xboole_0=A_1102)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.29/2.91  tff(c_7493, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7445, c_7490])).
% 8.29/2.91  tff(c_7506, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_7493])).
% 8.29/2.91  tff(c_7528, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7506])).
% 8.29/2.91  tff(c_7556, plain, (![A_1113, B_1114, C_1115, C_1116]: (k3_zfmisc_1(k2_zfmisc_1(A_1113, B_1114), C_1115, C_1116)=k4_zfmisc_1(A_1113, B_1114, C_1115, C_1116))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7433])).
% 8.29/2.91  tff(c_8125, plain, (![C_1178, A_1179, A_1180, B_1181, C_1184, B_1182, C_1183]: (C_1184=B_1181 | k3_zfmisc_1(A_1180, B_1181, C_1178)=k1_xboole_0 | k4_zfmisc_1(A_1179, B_1182, C_1184, C_1183)!=k3_zfmisc_1(A_1180, B_1181, C_1178))), inference(superposition, [status(thm), theory('equality')], [c_7556, c_22])).
% 8.29/2.91  tff(c_8238, plain, (![B_1191, A_1192, C_1193]: (B_1191='#skF_7' | k3_zfmisc_1(A_1192, B_1191, C_1193)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_1192, B_1191, C_1193))), inference(superposition, [status(thm), theory('equality')], [c_7445, c_8125])).
% 8.29/2.91  tff(c_8244, plain, (![C_1094, A_1092, B_1093, C_3]: (C_1094='#skF_7' | k3_zfmisc_1(k2_zfmisc_1(A_1092, B_1093), C_1094, C_3)=k1_xboole_0 | k4_zfmisc_1(A_1092, B_1093, C_1094, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7555, c_8238])).
% 8.29/2.91  tff(c_8255, plain, (![C_1094, A_1092, B_1093, C_3]: (C_1094='#skF_7' | k4_zfmisc_1(A_1092, B_1093, C_1094, C_3)=k1_xboole_0 | k4_zfmisc_1(A_1092, B_1093, C_1094, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7555, c_8244])).
% 8.29/2.91  tff(c_8301, plain, ('#skF_7'='#skF_3' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_8255])).
% 8.29/2.91  tff(c_8302, plain, ('#skF_7'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_7528, c_8301])).
% 8.29/2.91  tff(c_8337, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8302, c_7445])).
% 8.29/2.91  tff(c_7677, plain, (![D_1126, F_1125, B_1124, C_1122, E_1127, A_1123]: (D_1126=A_1123 | k3_zfmisc_1(A_1123, B_1124, C_1122)=k1_xboole_0 | k3_zfmisc_1(D_1126, E_1127, F_1125)!=k3_zfmisc_1(A_1123, B_1124, C_1122))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.29/2.91  tff(c_7689, plain, (![B_1093, C_1094, D_1126, F_1125, A_1092, C_3, E_1127]: (k2_zfmisc_1(A_1092, B_1093)=D_1126 | k3_zfmisc_1(k2_zfmisc_1(A_1092, B_1093), C_1094, C_3)=k1_xboole_0 | k4_zfmisc_1(A_1092, B_1093, C_1094, C_3)!=k3_zfmisc_1(D_1126, E_1127, F_1125))), inference(superposition, [status(thm), theory('equality')], [c_7555, c_7677])).
% 8.29/2.91  tff(c_9830, plain, (![D_1377, C_1381, F_1379, B_1378, E_1376, C_1375, A_1380]: (k2_zfmisc_1(A_1380, B_1378)=D_1377 | k4_zfmisc_1(A_1380, B_1378, C_1375, C_1381)=k1_xboole_0 | k4_zfmisc_1(A_1380, B_1378, C_1375, C_1381)!=k3_zfmisc_1(D_1377, E_1376, F_1379))), inference(demodulation, [status(thm), theory('equality')], [c_7555, c_7689])).
% 8.29/2.91  tff(c_9833, plain, (![D_1377, E_1376, F_1379]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1377 | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1377, E_1376, F_1379))), inference(superposition, [status(thm), theory('equality')], [c_8337, c_9830])).
% 8.29/2.91  tff(c_9867, plain, (![D_1377, E_1376, F_1379]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1377 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1377, E_1376, F_1379))), inference(demodulation, [status(thm), theory('equality')], [c_8337, c_9833])).
% 8.29/2.91  tff(c_9875, plain, (![D_1382, E_1383, F_1384]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1382 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1382, E_1383, F_1384))), inference(negUnitSimplification, [status(thm)], [c_7528, c_9867])).
% 8.29/2.91  tff(c_9881, plain, (![A_1092, B_1093, C_1094, C_3]: (k2_zfmisc_1(A_1092, B_1093)=k2_zfmisc_1('#skF_1', '#skF_6') | k4_zfmisc_1(A_1092, B_1093, C_1094, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7555, c_9875])).
% 8.29/2.91  tff(c_9893, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_9881])).
% 8.29/2.91  tff(c_9933, plain, (![C_3]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_3)=k3_zfmisc_1('#skF_1', '#skF_6', C_3))), inference(superposition, [status(thm), theory('equality')], [c_9893, c_2])).
% 8.29/2.91  tff(c_9942, plain, (![C_1389]: (k3_zfmisc_1('#skF_1', '#skF_6', C_1389)=k3_zfmisc_1('#skF_1', '#skF_2', C_1389))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9933])).
% 8.29/2.91  tff(c_10044, plain, (![C_1389]: (k3_zfmisc_1('#skF_1', '#skF_2', C_1389)!=k1_xboole_0 | k1_xboole_0=C_1389 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9942, c_6])).
% 8.29/2.91  tff(c_10076, plain, (![C_1389]: (k3_zfmisc_1('#skF_1', '#skF_2', C_1389)!=k1_xboole_0 | k1_xboole_0=C_1389 | k1_xboole_0='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_10044])).
% 8.29/2.91  tff(c_10080, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_10076])).
% 8.29/2.91  tff(c_10, plain, (![A_8, C_10]: (k3_zfmisc_1(A_8, k1_xboole_0, C_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/2.91  tff(c_10119, plain, (![A_8, C_10]: (k3_zfmisc_1(A_8, '#skF_6', C_10)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10080, c_10080, c_10])).
% 8.29/2.91  tff(c_9938, plain, (![C_3]: (k3_zfmisc_1('#skF_1', '#skF_6', C_3)=k3_zfmisc_1('#skF_1', '#skF_2', C_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9933])).
% 8.29/2.91  tff(c_10290, plain, (![C_3]: (k3_zfmisc_1('#skF_1', '#skF_2', C_3)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10119, c_9938])).
% 8.29/2.91  tff(c_7466, plain, (![A_1098, B_1099, C_1100, D_1101]: (k2_zfmisc_1(k3_zfmisc_1(A_1098, B_1099, C_1100), D_1101)=k4_zfmisc_1(A_1098, B_1099, C_1100, D_1101))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.29/2.91  tff(c_7609, plain, (![A_1117, D_1120, C_1119, C_1118, B_1121]: (k3_zfmisc_1(k3_zfmisc_1(A_1117, B_1121, C_1119), D_1120, C_1118)=k2_zfmisc_1(k4_zfmisc_1(A_1117, B_1121, C_1119, D_1120), C_1118))), inference(superposition, [status(thm), theory('equality')], [c_7466, c_2])).
% 8.29/2.91  tff(c_8642, plain, (![C_1251, D_1252, B_1254, A_1250, C_1253]: (k2_zfmisc_1(k4_zfmisc_1(A_1250, B_1254, C_1253, D_1252), C_1251)!=k1_xboole_0 | k1_xboole_0=C_1251 | k1_xboole_0=D_1252 | k3_zfmisc_1(A_1250, B_1254, C_1253)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7609, c_6])).
% 8.29/2.91  tff(c_8645, plain, (![C_1251]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_1251)!=k1_xboole_0 | k1_xboole_0=C_1251 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8337, c_8642])).
% 8.29/2.91  tff(c_8668, plain, (![C_1251]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_1251)!=k1_xboole_0 | k1_xboole_0=C_1251 | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_38, c_8645])).
% 8.29/2.91  tff(c_8727, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8668])).
% 8.29/2.91  tff(c_8776, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8727, c_6])).
% 8.29/2.91  tff(c_8790, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_8776])).
% 8.29/2.91  tff(c_8809, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8790, c_7528])).
% 8.29/2.91  tff(c_32, plain, (![A_23, C_25, D_26]: (k4_zfmisc_1(A_23, k1_xboole_0, C_25, D_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.29/2.91  tff(c_8813, plain, (![A_23, C_25, D_26]: (k4_zfmisc_1(A_23, '#skF_6', C_25, D_26)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8790, c_8790, c_32])).
% 8.29/2.91  tff(c_9205, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8813, c_8337])).
% 8.29/2.91  tff(c_9324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8809, c_9205])).
% 8.29/2.91  tff(c_9326, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8668])).
% 8.29/2.91  tff(c_9941, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9938, c_9326])).
% 8.29/2.91  tff(c_10081, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10080, c_9941])).
% 8.29/2.91  tff(c_10458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10290, c_10081])).
% 8.29/2.91  tff(c_10460, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_10076])).
% 8.29/2.91  tff(c_16, plain, (![F_16, D_14, E_15, B_12, A_11, C_13]: (E_15=B_12 | k1_xboole_0=C_13 | k1_xboole_0=B_12 | k1_xboole_0=A_11 | k3_zfmisc_1(D_14, E_15, F_16)!=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.29/2.91  tff(c_10017, plain, (![E_15, C_1389, D_14, F_16]: (E_15='#skF_6' | k1_xboole_0=C_1389 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k3_zfmisc_1(D_14, E_15, F_16)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1389))), inference(superposition, [status(thm), theory('equality')], [c_9942, c_16])).
% 8.29/2.91  tff(c_10070, plain, (![E_15, C_1389, D_14, F_16]: (E_15='#skF_6' | k1_xboole_0=C_1389 | k1_xboole_0='#skF_6' | k3_zfmisc_1(D_14, E_15, F_16)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1389))), inference(negUnitSimplification, [status(thm)], [c_44, c_10017])).
% 8.29/2.91  tff(c_10758, plain, (![E_15, C_1389, D_14, F_16]: (E_15='#skF_6' | k1_xboole_0=C_1389 | k3_zfmisc_1(D_14, E_15, F_16)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1389))), inference(negUnitSimplification, [status(thm)], [c_10460, c_10070])).
% 8.29/2.91  tff(c_10761, plain, (![C_1389]: ('#skF_6'='#skF_2' | k1_xboole_0=C_1389)), inference(reflexivity, [status(thm), theory('equality')], [c_10758])).
% 8.29/2.91  tff(c_10841, plain, (![C_1456]: (k1_xboole_0=C_1456)), inference(negUnitSimplification, [status(thm)], [c_7375, c_10761])).
% 8.29/2.91  tff(c_10962, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_10841, c_9941])).
% 8.29/2.91  tff(c_10963, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7506])).
% 8.29/2.91  tff(c_10965, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_10963])).
% 8.29/2.91  tff(c_10979, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10965, c_44])).
% 8.29/2.91  tff(c_10976, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10965, c_42])).
% 8.29/2.91  tff(c_10978, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10965, c_40])).
% 8.29/2.91  tff(c_10977, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10965, c_38])).
% 8.29/2.91  tff(c_10964, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7506])).
% 8.29/2.91  tff(c_11080, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10965, c_10964])).
% 8.29/2.91  tff(c_11452, plain, (![A_1786, B_1787, C_1788, D_1789]: (k4_zfmisc_1(A_1786, B_1787, C_1788, D_1789)!='#skF_7' | D_1789='#skF_7' | C_1788='#skF_7' | B_1787='#skF_7' | A_1786='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10965, c_10965, c_10965, c_10965, c_10965, c_26])).
% 8.29/2.91  tff(c_11467, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11080, c_11452])).
% 8.29/2.91  tff(c_11479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10979, c_10976, c_10978, c_10977, c_11467])).
% 8.29/2.91  tff(c_11480, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_10963])).
% 8.29/2.91  tff(c_11495, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11480, c_44])).
% 8.29/2.91  tff(c_11494, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11480, c_40])).
% 8.29/2.91  tff(c_11493, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11480, c_38])).
% 8.29/2.91  tff(c_11597, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11480, c_10964])).
% 8.29/2.91  tff(c_11969, plain, (![A_1849, B_1850, C_1851, D_1852]: (k4_zfmisc_1(A_1849, B_1850, C_1851, D_1852)!='#skF_6' | D_1852='#skF_6' | C_1851='#skF_6' | B_1850='#skF_6' | A_1849='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11480, c_11480, c_11480, c_11480, c_11480, c_26])).
% 8.29/2.91  tff(c_11984, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11597, c_11969])).
% 8.29/2.91  tff(c_11996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11495, c_7375, c_11494, c_11493, c_11984])).
% 8.29/2.91  tff(c_11997, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_7369])).
% 8.29/2.91  tff(c_12063, plain, (![A_1859, B_1860, C_1861]: (k2_zfmisc_1(k2_zfmisc_1(A_1859, B_1860), C_1861)=k3_zfmisc_1(A_1859, B_1860, C_1861))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/2.91  tff(c_12066, plain, (![A_1859, B_1860, C_1861, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_1859, B_1860), C_1861, C_3)=k2_zfmisc_1(k3_zfmisc_1(A_1859, B_1860, C_1861), C_3))), inference(superposition, [status(thm), theory('equality')], [c_12063, c_2])).
% 8.29/2.91  tff(c_12161, plain, (![A_1859, B_1860, C_1861, C_3]: (k3_zfmisc_1(k2_zfmisc_1(A_1859, B_1860), C_1861, C_3)=k4_zfmisc_1(A_1859, B_1860, C_1861, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12066])).
% 8.29/2.91  tff(c_11998, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_7369])).
% 8.29/2.91  tff(c_11999, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4907, c_7370, c_46])).
% 8.29/2.91  tff(c_12004, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11998, c_11999])).
% 8.29/2.91  tff(c_12134, plain, (![A_1870, B_1871, C_1872, D_1873]: (k4_zfmisc_1(A_1870, B_1871, C_1872, D_1873)!=k1_xboole_0 | k1_xboole_0=D_1873 | k1_xboole_0=C_1872 | k1_xboole_0=B_1871 | k1_xboole_0=A_1870)), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.29/2.91  tff(c_12137, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12004, c_12134])).
% 8.29/2.91  tff(c_12150, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_38, c_12137])).
% 8.29/2.91  tff(c_12160, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12150])).
% 8.29/2.91  tff(c_12511, plain, (![E_1914, D_1913, C_1909, F_1912, B_1911, A_1910]: (E_1914=B_1911 | k3_zfmisc_1(A_1910, B_1911, C_1909)=k1_xboole_0 | k3_zfmisc_1(D_1913, E_1914, F_1912)!=k3_zfmisc_1(A_1910, B_1911, C_1909))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.29/2.91  tff(c_12523, plain, (![E_1914, C_1861, B_1860, C_3, D_1913, F_1912, A_1859]: (E_1914=C_1861 | k3_zfmisc_1(k2_zfmisc_1(A_1859, B_1860), C_1861, C_3)=k1_xboole_0 | k4_zfmisc_1(A_1859, B_1860, C_1861, C_3)!=k3_zfmisc_1(D_1913, E_1914, F_1912))), inference(superposition, [status(thm), theory('equality')], [c_12161, c_12511])).
% 8.29/2.91  tff(c_13443, plain, (![B_2004, C_2005, F_2007, A_2002, C_2008, E_2003, D_2006]: (E_2003=C_2005 | k4_zfmisc_1(A_2002, B_2004, C_2005, C_2008)=k1_xboole_0 | k4_zfmisc_1(A_2002, B_2004, C_2005, C_2008)!=k3_zfmisc_1(D_2006, E_2003, F_2007))), inference(demodulation, [status(thm), theory('equality')], [c_12161, c_12523])).
% 8.29/2.91  tff(c_13458, plain, (![E_2003, D_2006, F_2007]: (E_2003='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2006, E_2003, F_2007))), inference(superposition, [status(thm), theory('equality')], [c_12004, c_13443])).
% 8.29/2.91  tff(c_13482, plain, (![E_2003, D_2006, F_2007]: (E_2003='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2006, E_2003, F_2007))), inference(demodulation, [status(thm), theory('equality')], [c_12004, c_13458])).
% 8.29/2.91  tff(c_13495, plain, (![E_2010, D_2011, F_2012]: (E_2010='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2011, E_2010, F_2012))), inference(negUnitSimplification, [status(thm)], [c_12160, c_13482])).
% 8.29/2.91  tff(c_13501, plain, (![C_1861, A_1859, B_1860, C_3]: (C_1861='#skF_7' | k4_zfmisc_1(A_1859, B_1860, C_1861, C_3)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12161, c_13495])).
% 8.29/2.91  tff(c_13513, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_13501])).
% 8.29/2.91  tff(c_13515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11997, c_13513])).
% 8.29/2.91  tff(c_13516, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_12150])).
% 8.29/2.91  tff(c_13531, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13516, c_44])).
% 8.29/2.91  tff(c_13528, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13516, c_42])).
% 8.29/2.91  tff(c_13529, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13516, c_38])).
% 8.29/2.91  tff(c_13517, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12150])).
% 8.29/2.91  tff(c_13632, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13516, c_13517])).
% 8.29/2.91  tff(c_13856, plain, (![A_2057, B_2058, C_2059, D_2060]: (k4_zfmisc_1(A_2057, B_2058, C_2059, D_2060)!='#skF_7' | D_2060='#skF_7' | C_2059='#skF_7' | B_2058='#skF_7' | A_2057='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13516, c_13516, c_13516, c_13516, c_13516, c_26])).
% 8.29/2.91  tff(c_13871, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13632, c_13856])).
% 8.29/2.91  tff(c_13883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13531, c_13528, c_11997, c_13529, c_13871])).
% 8.29/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.29/2.91  
% 8.29/2.91  Inference rules
% 8.29/2.91  ----------------------
% 8.29/2.91  #Ref     : 70
% 8.29/2.91  #Sup     : 3484
% 8.29/2.91  #Fact    : 0
% 8.29/2.91  #Define  : 0
% 8.29/2.91  #Split   : 24
% 8.29/2.91  #Chain   : 0
% 8.29/2.91  #Close   : 0
% 8.29/2.91  
% 8.29/2.92  Ordering : KBO
% 8.29/2.92  
% 8.29/2.92  Simplification rules
% 8.29/2.92  ----------------------
% 8.29/2.92  #Subsume      : 717
% 8.29/2.92  #Demod        : 2540
% 8.29/2.92  #Tautology    : 1957
% 8.29/2.92  #SimpNegUnit  : 131
% 8.29/2.92  #BackRed      : 392
% 8.29/2.92  
% 8.29/2.92  #Partial instantiations: 480
% 8.29/2.92  #Strategies tried      : 1
% 8.29/2.92  
% 8.29/2.92  Timing (in seconds)
% 8.29/2.92  ----------------------
% 8.29/2.92  Preprocessing        : 0.29
% 8.29/2.92  Parsing              : 0.15
% 8.29/2.92  CNF conversion       : 0.02
% 8.29/2.92  Main loop            : 1.81
% 8.29/2.92  Inferencing          : 0.57
% 8.29/2.92  Reduction            : 0.56
% 8.29/2.92  Demodulation         : 0.39
% 8.29/2.92  BG Simplification    : 0.07
% 8.29/2.92  Subsumption          : 0.49
% 8.29/2.92  Abstraction          : 0.11
% 8.29/2.92  MUC search           : 0.00
% 8.29/2.92  Cooper               : 0.00
% 8.29/2.92  Total                : 2.19
% 8.29/2.92  Index Insertion      : 0.00
% 8.29/2.92  Index Deletion       : 0.00
% 8.29/2.92  Index Matching       : 0.00
% 8.29/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
