%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:46 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 9.01s
% Verified   : 
% Statistics : Number of formulae       :  312 (9535 expanded)
%              Number of leaves         :   22 (2833 expanded)
%              Depth                    :   34
%              Number of atoms          :  560 (25867 expanded)
%              Number of equality atoms :  539 (25846 expanded)
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

tff(f_89,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_110,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),D_13) = k4_zfmisc_1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [A_40,B_41,C_42] : k2_zfmisc_1(k2_zfmisc_1(A_40,B_41),C_42) = k3_zfmisc_1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    ! [A_7,B_8,C_9,C_42] : k3_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9,C_42) = k2_zfmisc_1(k3_zfmisc_1(A_7,B_8,C_9),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_153])).

tff(c_352,plain,(
    ! [A_7,B_8,C_9,C_42] : k3_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9,C_42) = k4_zfmisc_1(A_7,B_8,C_9,C_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_169])).

tff(c_42,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_237,plain,(
    ! [A_49,B_50,C_51,D_52] : k2_zfmisc_1(k3_zfmisc_1(A_49,B_50,C_51),D_52) = k4_zfmisc_1(A_49,B_50,C_51,D_52) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_428,plain,(
    ! [D_72,A_73,B_74,C_75] :
      ( k1_xboole_0 = D_72
      | k3_zfmisc_1(A_73,B_74,C_75) = k1_xboole_0
      | k4_zfmisc_1(A_73,B_74,C_75,D_72) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_2])).

tff(c_431,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_428])).

tff(c_479,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_294,plain,(
    ! [D_56,B_57,A_58,C_59] :
      ( D_56 = B_57
      | k1_xboole_0 = B_57
      | k1_xboole_0 = A_58
      | k2_zfmisc_1(C_59,D_56) != k2_zfmisc_1(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1169,plain,(
    ! [C_177,D_176,A_175,C_178,D_174,B_173] :
      ( D_176 = D_174
      | k1_xboole_0 = D_176
      | k3_zfmisc_1(A_175,B_173,C_177) = k1_xboole_0
      | k4_zfmisc_1(A_175,B_173,C_177,D_176) != k2_zfmisc_1(C_178,D_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_294])).

tff(c_1181,plain,(
    ! [D_174,C_178] :
      ( D_174 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_178,D_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1169])).

tff(c_1265,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1181])).

tff(c_162,plain,(
    ! [C_42,A_40,B_41] :
      ( k1_xboole_0 = C_42
      | k2_zfmisc_1(A_40,B_41) = k1_xboole_0
      | k3_zfmisc_1(A_40,B_41,C_42) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_2])).

tff(c_1323,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_162])).

tff(c_1326,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1323])).

tff(c_1357,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_2])).

tff(c_1359,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1357])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1315,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_14])).

tff(c_1324,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1315])).

tff(c_1679,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_1324])).

tff(c_1680,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_42])).

tff(c_1421,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_479])).

tff(c_1904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_1421])).

tff(c_1905,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1357])).

tff(c_2187,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_1324])).

tff(c_2188,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2187,c_42])).

tff(c_1927,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_479])).

tff(c_2260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2188,c_1927])).

tff(c_2261,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1323])).

tff(c_2295,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2261,c_479])).

tff(c_2579,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2261,c_1324])).

tff(c_2580,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_42])).

tff(c_2770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2295,c_2580])).

tff(c_2771,plain,(
    ! [D_174,C_178] :
      ( k1_xboole_0 = '#skF_8'
      | D_174 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_178,D_174) ) ),
    inference(splitRight,[status(thm)],[c_1181])).

tff(c_2773,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2771])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] : k4_zfmisc_1(A_20,B_21,C_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2805,plain,(
    ! [A_20,B_21,C_22] : k4_zfmisc_1(A_20,B_21,C_22,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2773,c_2773,c_24])).

tff(c_3077,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2805,c_42])).

tff(c_2793,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2773,c_479])).

tff(c_3190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_2793])).

tff(c_3193,plain,(
    ! [D_326,C_327] :
      ( D_326 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_327,D_326) ) ),
    inference(splitRight,[status(thm)],[c_2771])).

tff(c_3196,plain,(
    ! [D_13,A_10,B_11,C_12] :
      ( D_13 = '#skF_8'
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3193])).

tff(c_3267,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3196])).

tff(c_3297,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3267,c_42])).

tff(c_715,plain,(
    ! [E_108,A_113,F_109,C_111,D_110,B_112] :
      ( E_108 = B_112
      | k3_zfmisc_1(A_113,B_112,C_111) = k1_xboole_0
      | k3_zfmisc_1(D_110,E_108,F_109) != k3_zfmisc_1(A_113,B_112,C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_727,plain,(
    ! [E_108,C_42,A_7,F_109,D_110,B_8,C_9] :
      ( E_108 = C_9
      | k3_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9,C_42) = k1_xboole_0
      | k4_zfmisc_1(A_7,B_8,C_9,C_42) != k3_zfmisc_1(D_110,E_108,F_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_715])).

tff(c_3479,plain,(
    ! [B_363,C_365,A_367,F_368,C_366,D_364,E_362] :
      ( E_362 = C_365
      | k4_zfmisc_1(A_367,B_363,C_365,C_366) = k1_xboole_0
      | k4_zfmisc_1(A_367,B_363,C_365,C_366) != k3_zfmisc_1(D_364,E_362,F_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_727])).

tff(c_3482,plain,(
    ! [E_362,D_364,F_368] :
      ( E_362 = '#skF_7'
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_364,E_362,F_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3297,c_3479])).

tff(c_3516,plain,(
    ! [E_362,D_364,F_368] :
      ( E_362 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_364,E_362,F_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3297,c_3482])).

tff(c_3524,plain,(
    ! [E_369,D_370,F_371] :
      ( E_369 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_370,E_369,F_371) ) ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_3516])).

tff(c_3530,plain,(
    ! [C_9,A_7,B_8,C_42] :
      ( C_9 = '#skF_7'
      | k4_zfmisc_1(A_7,B_8,C_9,C_42) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_3524])).

tff(c_3542,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3530])).

tff(c_2772,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1181])).

tff(c_3572,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3542,c_2772])).

tff(c_3571,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3542,c_3297])).

tff(c_325,plain,(
    ! [C_60,A_61,B_62,D_63] :
      ( C_60 = A_61
      | k1_xboole_0 = B_62
      | k1_xboole_0 = A_61
      | k2_zfmisc_1(C_60,D_63) != k2_zfmisc_1(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_331,plain,(
    ! [D_63,B_11,A_10,C_12,D_13,C_60] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = C_60
      | k1_xboole_0 = D_13
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k2_zfmisc_1(C_60,D_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_325])).

tff(c_3589,plain,(
    ! [C_60,D_63] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = C_60
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_60,D_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3571,c_331])).

tff(c_3626,plain,(
    ! [C_376,D_377] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = C_376
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_376,D_377) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3572,c_34,c_3589])).

tff(c_3629,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_5','#skF_6','#skF_3')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3626])).

tff(c_3984,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3629])).

tff(c_306,plain,(
    ! [D_56,A_7,B_8,C_9,C_59] :
      ( D_56 = C_9
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_59,D_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_294])).

tff(c_4039,plain,(
    ! [D_56,C_59] :
      ( D_56 = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_59,D_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3984,c_306])).

tff(c_4075,plain,(
    ! [D_56,C_59] :
      ( D_56 = '#skF_3'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_59,D_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_4039])).

tff(c_4215,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4075])).

tff(c_4246,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4215,c_2])).

tff(c_4248,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4246])).

tff(c_4020,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3984,c_3572])).

tff(c_4252,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4248,c_4020])).

tff(c_182,plain,(
    ! [B_2,C_42] : k3_zfmisc_1(k1_xboole_0,B_2,C_42) = k2_zfmisc_1(k1_xboole_0,C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_153])).

tff(c_186,plain,(
    ! [B_2,C_42] : k3_zfmisc_1(k1_xboole_0,B_2,C_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_182])).

tff(c_4282,plain,(
    ! [B_2,C_42] : k3_zfmisc_1('#skF_5',B_2,C_42) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4248,c_4248,c_186])).

tff(c_4395,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4282,c_3984])).

tff(c_4539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4252,c_4395])).

tff(c_4540,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4246])).

tff(c_4547,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4540,c_4020])).

tff(c_4237,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = k2_zfmisc_1(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_4215,c_12])).

tff(c_4245,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4237])).

tff(c_4696,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4540,c_4245])).

tff(c_4697,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4696,c_3984])).

tff(c_4862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4547,c_4697])).

tff(c_4864,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4075])).

tff(c_337,plain,(
    ! [D_63,A_7,C_60,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = C_60
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_60,D_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_325])).

tff(c_4024,plain,(
    ! [C_60,D_63] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = C_60
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_60,D_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3984,c_337])).

tff(c_4072,plain,(
    ! [C_60,D_63] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = C_60
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_60,D_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_4024])).

tff(c_5026,plain,(
    ! [C_499,D_500] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = C_499
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_499,D_500) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4864,c_4072])).

tff(c_5032,plain,(
    ! [A_7,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = k2_zfmisc_1('#skF_5','#skF_6')
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5026])).

tff(c_5042,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5032])).

tff(c_8,plain,(
    ! [D_6,B_4,A_3,C_5] :
      ( D_6 = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5088,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_6'
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5042,c_8])).

tff(c_5417,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5088])).

tff(c_5418,plain,(
    '#skF_6' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_5417])).

tff(c_5494,plain,(
    k2_zfmisc_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5418,c_5042])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4,D_6] :
      ( C_5 = A_3
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5511,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_5'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5494,c_10])).

tff(c_5528,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_5511])).

tff(c_5669,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5528])).

tff(c_5072,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5042,c_4864])).

tff(c_5674,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5669,c_5072])).

tff(c_5718,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5669,c_5669,c_6])).

tff(c_5796,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5718,c_5494])).

tff(c_5834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5674,c_5796])).

tff(c_5835,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_5528])).

tff(c_5843,plain,(
    '#skF_5' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5835])).

tff(c_5845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_5843])).

tff(c_5847,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k4_zfmisc_1(A_20,B_21,C_22,D_23) != k1_xboole_0
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5888,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5847,c_22])).

tff(c_5897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_5888])).

tff(c_5898,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_5940,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5898])).

tff(c_5899,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_5935,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_42])).

tff(c_6073,plain,(
    ! [D_562,B_563,A_564,C_565] :
      ( D_562 = B_563
      | k1_xboole_0 = B_563
      | k1_xboole_0 = A_564
      | k2_zfmisc_1(C_565,D_562) != k2_zfmisc_1(A_564,B_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6966,plain,(
    ! [A_685,C_684,B_683,D_682,D_686,C_687] :
      ( D_686 = D_682
      | k1_xboole_0 = D_686
      | k3_zfmisc_1(A_685,B_683,C_687) = k1_xboole_0
      | k4_zfmisc_1(A_685,B_683,C_687,D_686) != k2_zfmisc_1(C_684,D_682) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6073])).

tff(c_6981,plain,(
    ! [D_682,C_684] :
      ( D_682 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_684,D_682) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5935,c_6966])).

tff(c_7088,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6981])).

tff(c_5952,plain,(
    ! [A_549,B_550,C_551] : k2_zfmisc_1(k2_zfmisc_1(A_549,B_550),C_551) = k3_zfmisc_1(A_549,B_550,C_551) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5961,plain,(
    ! [C_551,A_549,B_550] :
      ( k1_xboole_0 = C_551
      | k2_zfmisc_1(A_549,B_550) = k1_xboole_0
      | k3_zfmisc_1(A_549,B_550,C_551) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5952,c_2])).

tff(c_7145,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7088,c_5961])).

tff(c_7162,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7145])).

tff(c_7187,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7162,c_2])).

tff(c_7197,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_7187])).

tff(c_7137,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_7088,c_14])).

tff(c_7146,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7137])).

tff(c_7448,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7197,c_7146])).

tff(c_7449,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7448,c_5935])).

tff(c_6223,plain,(
    ! [A_581,B_582,C_583,D_584] :
      ( k4_zfmisc_1(A_581,B_582,C_583,D_584) != k1_xboole_0
      | k1_xboole_0 = D_584
      | k1_xboole_0 = C_583
      | k1_xboole_0 = B_582
      | k1_xboole_0 = A_581 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6226,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5935,c_6223])).

tff(c_6239,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_6226])).

tff(c_6248,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6239])).

tff(c_7221,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7197,c_6248])).

tff(c_7663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7449,c_7221])).

tff(c_7664,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7145])).

tff(c_7979,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7664,c_7146])).

tff(c_7980,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7979,c_5935])).

tff(c_7687,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7664,c_6248])).

tff(c_8244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7980,c_7687])).

tff(c_8245,plain,(
    ! [D_682,C_684] :
      ( k1_xboole_0 = '#skF_8'
      | D_682 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_684,D_682) ) ),
    inference(splitRight,[status(thm)],[c_6981])).

tff(c_8247,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_8245])).

tff(c_8279,plain,(
    ! [A_20,B_21,C_22] : k4_zfmisc_1(A_20,B_21,C_22,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8247,c_8247,c_24])).

tff(c_8477,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8279,c_5935])).

tff(c_8268,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8247,c_6248])).

tff(c_8623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8477,c_8268])).

tff(c_8626,plain,(
    ! [D_802,C_803] :
      ( D_802 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_803,D_802) ) ),
    inference(splitRight,[status(thm)],[c_8245])).

tff(c_8629,plain,(
    ! [D_13,A_10,B_11,C_12] :
      ( D_13 = '#skF_8'
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_8626])).

tff(c_8659,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8629])).

tff(c_8661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5940,c_8659])).

tff(c_8663,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6239])).

tff(c_8669,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8663,c_22])).

tff(c_8678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_8669])).

tff(c_8679,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5898])).

tff(c_8686,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8679])).

tff(c_8698,plain,(
    ! [A_809,B_810,C_811] : k2_zfmisc_1(k2_zfmisc_1(A_809,B_810),C_811) = k3_zfmisc_1(A_809,B_810,C_811) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8701,plain,(
    ! [A_809,B_810,C_811,C_9] : k3_zfmisc_1(k2_zfmisc_1(A_809,B_810),C_811,C_9) = k2_zfmisc_1(k3_zfmisc_1(A_809,B_810,C_811),C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_8698,c_12])).

tff(c_8897,plain,(
    ! [A_809,B_810,C_811,C_9] : k3_zfmisc_1(k2_zfmisc_1(A_809,B_810),C_811,C_9) = k4_zfmisc_1(A_809,B_810,C_811,C_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8701])).

tff(c_8680,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5898])).

tff(c_8681,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8680,c_5935])).

tff(c_8948,plain,(
    ! [A_837,B_838,C_839,D_840] :
      ( k4_zfmisc_1(A_837,B_838,C_839,D_840) != k1_xboole_0
      | k1_xboole_0 = D_840
      | k1_xboole_0 = C_839
      | k1_xboole_0 = B_838
      | k1_xboole_0 = A_837 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8951,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8681,c_8948])).

tff(c_8964,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_8951])).

tff(c_8973,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8964])).

tff(c_9164,plain,(
    ! [D_869,C_870,A_872,E_867,B_871,F_868] :
      ( E_867 = B_871
      | k3_zfmisc_1(A_872,B_871,C_870) = k1_xboole_0
      | k3_zfmisc_1(D_869,E_867,F_868) != k3_zfmisc_1(A_872,B_871,C_870) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_9176,plain,(
    ! [D_869,A_809,C_811,B_810,E_867,F_868,C_9] :
      ( E_867 = C_811
      | k3_zfmisc_1(k2_zfmisc_1(A_809,B_810),C_811,C_9) = k1_xboole_0
      | k4_zfmisc_1(A_809,B_810,C_811,C_9) != k3_zfmisc_1(D_869,E_867,F_868) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8897,c_9164])).

tff(c_10770,plain,(
    ! [F_1025,D_1029,B_1026,C_1024,C_1027,E_1028,A_1030] :
      ( E_1028 = C_1024
      | k4_zfmisc_1(A_1030,B_1026,C_1024,C_1027) = k1_xboole_0
      | k4_zfmisc_1(A_1030,B_1026,C_1024,C_1027) != k3_zfmisc_1(D_1029,E_1028,F_1025) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8897,c_9176])).

tff(c_10794,plain,(
    ! [E_1028,D_1029,F_1025] :
      ( E_1028 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1029,E_1028,F_1025) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8681,c_10770])).

tff(c_10809,plain,(
    ! [E_1028,D_1029,F_1025] :
      ( E_1028 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1029,E_1028,F_1025) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8681,c_10794])).

tff(c_10860,plain,(
    ! [E_1038,D_1039,F_1040] :
      ( E_1038 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1039,E_1038,F_1040) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8973,c_10809])).

tff(c_10866,plain,(
    ! [C_811,A_809,B_810,C_9] :
      ( C_811 = '#skF_7'
      | k4_zfmisc_1(A_809,B_810,C_811,C_9) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8897,c_10860])).

tff(c_10878,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10866])).

tff(c_8870,plain,(
    ! [D_829,B_830,A_831,C_832] :
      ( D_829 = B_830
      | k1_xboole_0 = B_830
      | k1_xboole_0 = A_831
      | k2_zfmisc_1(C_832,D_829) != k2_zfmisc_1(A_831,B_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9663,plain,(
    ! [D_936,C_934,A_937,B_935,D_938,C_939] :
      ( D_938 = D_936
      | k1_xboole_0 = D_938
      | k3_zfmisc_1(A_937,B_935,C_939) = k1_xboole_0
      | k4_zfmisc_1(A_937,B_935,C_939,D_938) != k2_zfmisc_1(C_934,D_936) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_8870])).

tff(c_9675,plain,(
    ! [D_936,C_934] :
      ( D_936 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_934,D_936) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8681,c_9663])).

tff(c_9699,plain,(
    ! [D_936,C_934] :
      ( D_936 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_934,D_936) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_9675])).

tff(c_9704,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9699])).

tff(c_8707,plain,(
    ! [C_811,A_809,B_810] :
      ( k1_xboole_0 = C_811
      | k2_zfmisc_1(A_809,B_810) = k1_xboole_0
      | k3_zfmisc_1(A_809,B_810,C_811) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8698,c_2])).

tff(c_9761,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9704,c_8707])).

tff(c_9806,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9761])).

tff(c_9831,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9806,c_2])).

tff(c_9841,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_9831])).

tff(c_9861,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9841,c_8973])).

tff(c_9753,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_9704,c_14])).

tff(c_9762,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9753])).

tff(c_10137,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9841,c_9762])).

tff(c_10138,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10137,c_8681])).

tff(c_10385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9861,c_10138])).

tff(c_10386,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_9761])).

tff(c_10405,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10386,c_8973])).

tff(c_10627,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10386,c_9762])).

tff(c_10628,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10627,c_8681])).

tff(c_10630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10405,c_10628])).

tff(c_10632,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9699])).

tff(c_8839,plain,(
    ! [C_825,A_826,B_827,D_828] :
      ( C_825 = A_826
      | k1_xboole_0 = B_827
      | k1_xboole_0 = A_826
      | k2_zfmisc_1(C_825,D_828) != k2_zfmisc_1(A_826,B_827) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10633,plain,(
    ! [D_1008,B_1005,A_1007,C_1009,C_1004,D_1006] :
      ( k3_zfmisc_1(A_1007,B_1005,C_1009) = C_1004
      | k1_xboole_0 = D_1008
      | k3_zfmisc_1(A_1007,B_1005,C_1009) = k1_xboole_0
      | k4_zfmisc_1(A_1007,B_1005,C_1009,D_1008) != k2_zfmisc_1(C_1004,D_1006) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_8839])).

tff(c_10645,plain,(
    ! [C_1004,D_1006] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_1004
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1004,D_1006) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8681,c_10633])).

tff(c_10669,plain,(
    ! [C_1004,D_1006] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_1004
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1004,D_1006) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_10645])).

tff(c_10706,plain,(
    ! [C_1015,D_1016] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_1015
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1015,D_1016) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10632,c_10669])).

tff(c_10709,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_10706])).

tff(c_11118,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_1','#skF_6','#skF_3')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10878,c_10709])).

tff(c_11121,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11118])).

tff(c_10907,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10878,c_10632])).

tff(c_11157,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11121,c_10907])).

tff(c_18,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] :
      ( E_18 = B_15
      | k3_zfmisc_1(A_14,B_15,C_16) = k1_xboole_0
      | k3_zfmisc_1(D_17,E_18,F_19) != k3_zfmisc_1(A_14,B_15,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_11188,plain,(
    ! [E_18,D_17,F_19] :
      ( E_18 = '#skF_6'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k1_xboole_0
      | k3_zfmisc_1(D_17,E_18,F_19) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11121,c_18])).

tff(c_11214,plain,(
    ! [E_18,D_17,F_19] :
      ( E_18 = '#skF_6'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0
      | k3_zfmisc_1(D_17,E_18,F_19) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11121,c_11188])).

tff(c_11950,plain,(
    ! [E_18,D_17,F_19] :
      ( E_18 = '#skF_6'
      | k3_zfmisc_1(D_17,E_18,F_19) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_11157,c_11214])).

tff(c_11953,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11950])).

tff(c_11955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8686,c_11953])).

tff(c_11956,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8964])).

tff(c_11958,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11956])).

tff(c_11976,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11958,c_40])).

tff(c_11973,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11958,c_38])).

tff(c_11975,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11958,c_36])).

tff(c_11974,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11958,c_34])).

tff(c_11957,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8964])).

tff(c_12072,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11958,c_11957])).

tff(c_8759,plain,(
    ! [A_816,B_817,C_818,D_819] : k2_zfmisc_1(k3_zfmisc_1(A_816,B_817,C_818),D_819) = k4_zfmisc_1(A_816,B_817,C_818,D_819) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8768,plain,(
    ! [D_819,A_816,B_817,C_818] :
      ( k1_xboole_0 = D_819
      | k3_zfmisc_1(A_816,B_817,C_818) = k1_xboole_0
      | k4_zfmisc_1(A_816,B_817,C_818,D_819) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8759,c_2])).

tff(c_12435,plain,(
    ! [D_1193,A_1194,B_1195,C_1196] :
      ( D_1193 = '#skF_7'
      | k3_zfmisc_1(A_1194,B_1195,C_1196) = '#skF_7'
      | k4_zfmisc_1(A_1194,B_1195,C_1196,D_1193) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11958,c_11958,c_11958,c_8768])).

tff(c_12450,plain,
    ( '#skF_7' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_12072,c_12435])).

tff(c_12461,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_11974,c_12450])).

tff(c_11962,plain,(
    ! [C_811,A_809,B_810] :
      ( C_811 = '#skF_7'
      | k2_zfmisc_1(A_809,B_810) = '#skF_7'
      | k3_zfmisc_1(A_809,B_810,C_811) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11958,c_11958,c_11958,c_8707])).

tff(c_12468,plain,
    ( '#skF_7' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_12461,c_11962])).

tff(c_12494,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_11975,c_12468])).

tff(c_11966,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_7'
      | A_1 = '#skF_7'
      | k2_zfmisc_1(A_1,B_2) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11958,c_11958,c_11958,c_2])).

tff(c_12515,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12494,c_11966])).

tff(c_12529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11976,c_11973,c_12515])).

tff(c_12530,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11956])).

tff(c_12549,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12530,c_40])).

tff(c_12548,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12530,c_36])).

tff(c_12547,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12530,c_34])).

tff(c_12751,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12530,c_11957])).

tff(c_13009,plain,(
    ! [D_1253,A_1254,B_1255,C_1256] :
      ( D_1253 = '#skF_6'
      | k3_zfmisc_1(A_1254,B_1255,C_1256) = '#skF_6'
      | k4_zfmisc_1(A_1254,B_1255,C_1256,D_1253) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12530,c_12530,c_12530,c_8768])).

tff(c_13024,plain,
    ( '#skF_6' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_12751,c_13009])).

tff(c_13035,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_12547,c_13024])).

tff(c_12877,plain,(
    ! [B_1235,A_1236] :
      ( B_1235 = '#skF_6'
      | A_1236 = '#skF_6'
      | k2_zfmisc_1(A_1236,B_1235) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12530,c_12530,c_12530,c_2])).

tff(c_12889,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_6'
      | k2_zfmisc_1(A_7,B_8) = '#skF_6'
      | k3_zfmisc_1(A_7,B_8,C_9) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12877])).

tff(c_13042,plain,
    ( '#skF_6' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_13035,c_12889])).

tff(c_13068,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_12548,c_13042])).

tff(c_12539,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_6'
      | A_1 = '#skF_6'
      | k2_zfmisc_1(A_1,B_2) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12530,c_12530,c_12530,c_2])).

tff(c_13089,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13068,c_12539])).

tff(c_13103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12549,c_8686,c_13089])).

tff(c_13104,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8679])).

tff(c_13126,plain,(
    ! [A_1259,B_1260,C_1261] : k2_zfmisc_1(k2_zfmisc_1(A_1259,B_1260),C_1261) = k3_zfmisc_1(A_1259,B_1260,C_1261) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13142,plain,(
    ! [A_7,B_8,C_9,C_1261] : k3_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9,C_1261) = k2_zfmisc_1(k3_zfmisc_1(A_7,B_8,C_9),C_1261) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_13126])).

tff(c_13325,plain,(
    ! [A_7,B_8,C_9,C_1261] : k3_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9,C_1261) = k4_zfmisc_1(A_7,B_8,C_9,C_1261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_13142])).

tff(c_13105,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8679])).

tff(c_13110,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13105,c_8681])).

tff(c_13402,plain,(
    ! [A_1291,B_1292,C_1293,D_1294] :
      ( k4_zfmisc_1(A_1291,B_1292,C_1293,D_1294) != k1_xboole_0
      | k1_xboole_0 = D_1294
      | k1_xboole_0 = C_1293
      | k1_xboole_0 = B_1292
      | k1_xboole_0 = A_1291 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_13405,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13110,c_13402])).

tff(c_13418,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_34,c_13405])).

tff(c_13427,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13418])).

tff(c_13657,plain,(
    ! [F_1323,D_1324,C_1325,E_1322,B_1326,A_1327] :
      ( E_1322 = B_1326
      | k3_zfmisc_1(A_1327,B_1326,C_1325) = k1_xboole_0
      | k3_zfmisc_1(D_1324,E_1322,F_1323) != k3_zfmisc_1(A_1327,B_1326,C_1325) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13669,plain,(
    ! [F_1323,D_1324,A_7,E_1322,C_1261,B_8,C_9] :
      ( E_1322 = C_9
      | k3_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9,C_1261) = k1_xboole_0
      | k4_zfmisc_1(A_7,B_8,C_9,C_1261) != k3_zfmisc_1(D_1324,E_1322,F_1323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13325,c_13657])).

tff(c_14957,plain,(
    ! [F_1465,A_1468,D_1463,C_1469,C_1467,E_1464,B_1466] :
      ( E_1464 = C_1467
      | k4_zfmisc_1(A_1468,B_1466,C_1467,C_1469) = k1_xboole_0
      | k4_zfmisc_1(A_1468,B_1466,C_1467,C_1469) != k3_zfmisc_1(D_1463,E_1464,F_1465) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13325,c_13669])).

tff(c_14975,plain,(
    ! [E_1464,D_1463,F_1465] :
      ( E_1464 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1463,E_1464,F_1465) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13110,c_14957])).

tff(c_14996,plain,(
    ! [E_1464,D_1463,F_1465] :
      ( E_1464 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1463,E_1464,F_1465) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13110,c_14975])).

tff(c_15002,plain,(
    ! [E_1470,D_1471,F_1472] :
      ( E_1470 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1471,E_1470,F_1472) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13427,c_14996])).

tff(c_15008,plain,(
    ! [C_9,A_7,B_8,C_1261] :
      ( C_9 = '#skF_7'
      | k4_zfmisc_1(A_7,B_8,C_9,C_1261) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13325,c_15002])).

tff(c_15020,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15008])).

tff(c_15022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13104,c_15020])).

tff(c_15023,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13418])).

tff(c_15301,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_40])).

tff(c_15298,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_38])).

tff(c_15299,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_34])).

tff(c_26,plain,(
    ! [A_20,B_21,D_23] : k4_zfmisc_1(A_20,B_21,k1_xboole_0,D_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_15292,plain,(
    ! [A_20,B_21,D_23] : k4_zfmisc_1(A_20,B_21,'#skF_7',D_23) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_15023,c_26])).

tff(c_15468,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15292,c_13110])).

tff(c_13210,plain,(
    ! [A_1268,B_1269,C_1270,D_1271] : k2_zfmisc_1(k3_zfmisc_1(A_1268,B_1269,C_1270),D_1271) = k4_zfmisc_1(A_1268,B_1269,C_1270,D_1271) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13219,plain,(
    ! [D_1271,A_1268,B_1269,C_1270] :
      ( k1_xboole_0 = D_1271
      | k3_zfmisc_1(A_1268,B_1269,C_1270) = k1_xboole_0
      | k4_zfmisc_1(A_1268,B_1269,C_1270,D_1271) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13210,c_2])).

tff(c_15758,plain,(
    ! [D_1555,A_1556,B_1557,C_1558] :
      ( D_1555 = '#skF_7'
      | k3_zfmisc_1(A_1556,B_1557,C_1558) = '#skF_7'
      | k4_zfmisc_1(A_1556,B_1557,C_1558,D_1555) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_15023,c_15023,c_13219])).

tff(c_15767,plain,
    ( '#skF_7' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_15468,c_15758])).

tff(c_15780,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_15299,c_15767])).

tff(c_13135,plain,(
    ! [C_1261,A_1259,B_1260] :
      ( k1_xboole_0 = C_1261
      | k2_zfmisc_1(A_1259,B_1260) = k1_xboole_0
      | k3_zfmisc_1(A_1259,B_1260,C_1261) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13126,c_2])).

tff(c_15286,plain,(
    ! [C_1261,A_1259,B_1260] :
      ( C_1261 = '#skF_7'
      | k2_zfmisc_1(A_1259,B_1260) = '#skF_7'
      | k3_zfmisc_1(A_1259,B_1260,C_1261) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_15023,c_15023,c_13135])).

tff(c_15791,plain,
    ( '#skF_7' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_15780,c_15286])).

tff(c_15817,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_13104,c_15791])).

tff(c_15291,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_7'
      | A_1 = '#skF_7'
      | k2_zfmisc_1(A_1,B_2) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15023,c_15023,c_15023,c_2])).

tff(c_15838,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15817,c_15291])).

tff(c_15852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15301,c_15298,c_15838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:42:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/2.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/2.98  
% 8.77/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/2.98  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 8.77/2.98  
% 8.77/2.98  %Foreground sorts:
% 8.77/2.98  
% 8.77/2.98  
% 8.77/2.98  %Background operators:
% 8.77/2.98  
% 8.77/2.98  
% 8.77/2.98  %Foreground operators:
% 8.77/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.77/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.77/2.98  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 8.77/2.98  tff('#skF_7', type, '#skF_7': $i).
% 8.77/2.98  tff('#skF_5', type, '#skF_5': $i).
% 8.77/2.98  tff('#skF_6', type, '#skF_6': $i).
% 8.77/2.98  tff('#skF_2', type, '#skF_2': $i).
% 8.77/2.98  tff('#skF_3', type, '#skF_3': $i).
% 8.77/2.98  tff('#skF_1', type, '#skF_1': $i).
% 8.77/2.98  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.77/2.98  tff('#skF_8', type, '#skF_8': $i).
% 8.77/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.77/2.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.77/2.98  tff('#skF_4', type, '#skF_4': $i).
% 8.77/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.77/2.98  
% 9.01/3.02  tff(f_89, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 9.01/3.02  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.01/3.02  tff(f_45, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 9.01/3.02  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.01/3.02  tff(f_41, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 9.01/3.02  tff(f_70, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 9.01/3.02  tff(f_55, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 9.01/3.02  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.01/3.02  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.01/3.02  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.01/3.02  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.01/3.02  tff(c_32, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.01/3.02  tff(c_110, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_32])).
% 9.01/3.02  tff(c_12, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.01/3.02  tff(c_14, plain, (![A_10, B_11, C_12, D_13]: (k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), D_13)=k4_zfmisc_1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.01/3.02  tff(c_153, plain, (![A_40, B_41, C_42]: (k2_zfmisc_1(k2_zfmisc_1(A_40, B_41), C_42)=k3_zfmisc_1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.01/3.02  tff(c_169, plain, (![A_7, B_8, C_9, C_42]: (k3_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9, C_42)=k2_zfmisc_1(k3_zfmisc_1(A_7, B_8, C_9), C_42))), inference(superposition, [status(thm), theory('equality')], [c_12, c_153])).
% 9.01/3.02  tff(c_352, plain, (![A_7, B_8, C_9, C_42]: (k3_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9, C_42)=k4_zfmisc_1(A_7, B_8, C_9, C_42))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_169])).
% 9.01/3.02  tff(c_42, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.01/3.02  tff(c_237, plain, (![A_49, B_50, C_51, D_52]: (k2_zfmisc_1(k3_zfmisc_1(A_49, B_50, C_51), D_52)=k4_zfmisc_1(A_49, B_50, C_51, D_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.01/3.02  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.01/3.02  tff(c_428, plain, (![D_72, A_73, B_74, C_75]: (k1_xboole_0=D_72 | k3_zfmisc_1(A_73, B_74, C_75)=k1_xboole_0 | k4_zfmisc_1(A_73, B_74, C_75, D_72)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_237, c_2])).
% 9.01/3.02  tff(c_431, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_428])).
% 9.01/3.02  tff(c_479, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_431])).
% 9.01/3.02  tff(c_294, plain, (![D_56, B_57, A_58, C_59]: (D_56=B_57 | k1_xboole_0=B_57 | k1_xboole_0=A_58 | k2_zfmisc_1(C_59, D_56)!=k2_zfmisc_1(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.01/3.02  tff(c_1169, plain, (![C_177, D_176, A_175, C_178, D_174, B_173]: (D_176=D_174 | k1_xboole_0=D_176 | k3_zfmisc_1(A_175, B_173, C_177)=k1_xboole_0 | k4_zfmisc_1(A_175, B_173, C_177, D_176)!=k2_zfmisc_1(C_178, D_174))), inference(superposition, [status(thm), theory('equality')], [c_14, c_294])).
% 9.01/3.02  tff(c_1181, plain, (![D_174, C_178]: (D_174='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_178, D_174))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1169])).
% 9.01/3.02  tff(c_1265, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1181])).
% 9.01/3.02  tff(c_162, plain, (![C_42, A_40, B_41]: (k1_xboole_0=C_42 | k2_zfmisc_1(A_40, B_41)=k1_xboole_0 | k3_zfmisc_1(A_40, B_41, C_42)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_2])).
% 9.01/3.02  tff(c_1323, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1265, c_162])).
% 9.01/3.02  tff(c_1326, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1323])).
% 9.01/3.02  tff(c_1357, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1326, c_2])).
% 9.01/3.02  tff(c_1359, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1357])).
% 9.01/3.02  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.01/3.02  tff(c_1315, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_1265, c_14])).
% 9.01/3.02  tff(c_1324, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1315])).
% 9.01/3.02  tff(c_1679, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_1324])).
% 9.01/3.02  tff(c_1680, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1679, c_42])).
% 9.01/3.02  tff(c_1421, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_479])).
% 9.01/3.02  tff(c_1904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1680, c_1421])).
% 9.01/3.02  tff(c_1905, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1357])).
% 9.01/3.02  tff(c_2187, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1905, c_1324])).
% 9.01/3.02  tff(c_2188, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2187, c_42])).
% 9.01/3.02  tff(c_1927, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1905, c_479])).
% 9.01/3.02  tff(c_2260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2188, c_1927])).
% 9.01/3.02  tff(c_2261, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1323])).
% 9.01/3.02  tff(c_2295, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2261, c_479])).
% 9.01/3.02  tff(c_2579, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2261, c_1324])).
% 9.01/3.02  tff(c_2580, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_42])).
% 9.01/3.02  tff(c_2770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2295, c_2580])).
% 9.01/3.02  tff(c_2771, plain, (![D_174, C_178]: (k1_xboole_0='#skF_8' | D_174='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_178, D_174))), inference(splitRight, [status(thm)], [c_1181])).
% 9.01/3.02  tff(c_2773, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_2771])).
% 9.01/3.02  tff(c_24, plain, (![A_20, B_21, C_22]: (k4_zfmisc_1(A_20, B_21, C_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.01/3.02  tff(c_2805, plain, (![A_20, B_21, C_22]: (k4_zfmisc_1(A_20, B_21, C_22, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2773, c_2773, c_24])).
% 9.01/3.02  tff(c_3077, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2805, c_42])).
% 9.01/3.02  tff(c_2793, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2773, c_479])).
% 9.01/3.02  tff(c_3190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3077, c_2793])).
% 9.01/3.02  tff(c_3193, plain, (![D_326, C_327]: (D_326='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_327, D_326))), inference(splitRight, [status(thm)], [c_2771])).
% 9.01/3.02  tff(c_3196, plain, (![D_13, A_10, B_11, C_12]: (D_13='#skF_8' | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3193])).
% 9.01/3.02  tff(c_3267, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_3196])).
% 9.01/3.02  tff(c_3297, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3267, c_42])).
% 9.01/3.02  tff(c_715, plain, (![E_108, A_113, F_109, C_111, D_110, B_112]: (E_108=B_112 | k3_zfmisc_1(A_113, B_112, C_111)=k1_xboole_0 | k3_zfmisc_1(D_110, E_108, F_109)!=k3_zfmisc_1(A_113, B_112, C_111))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.01/3.02  tff(c_727, plain, (![E_108, C_42, A_7, F_109, D_110, B_8, C_9]: (E_108=C_9 | k3_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9, C_42)=k1_xboole_0 | k4_zfmisc_1(A_7, B_8, C_9, C_42)!=k3_zfmisc_1(D_110, E_108, F_109))), inference(superposition, [status(thm), theory('equality')], [c_352, c_715])).
% 9.01/3.02  tff(c_3479, plain, (![B_363, C_365, A_367, F_368, C_366, D_364, E_362]: (E_362=C_365 | k4_zfmisc_1(A_367, B_363, C_365, C_366)=k1_xboole_0 | k4_zfmisc_1(A_367, B_363, C_365, C_366)!=k3_zfmisc_1(D_364, E_362, F_368))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_727])).
% 9.01/3.02  tff(c_3482, plain, (![E_362, D_364, F_368]: (E_362='#skF_7' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_364, E_362, F_368))), inference(superposition, [status(thm), theory('equality')], [c_3297, c_3479])).
% 9.01/3.02  tff(c_3516, plain, (![E_362, D_364, F_368]: (E_362='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_364, E_362, F_368))), inference(demodulation, [status(thm), theory('equality')], [c_3297, c_3482])).
% 9.01/3.02  tff(c_3524, plain, (![E_369, D_370, F_371]: (E_369='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_370, E_369, F_371))), inference(negUnitSimplification, [status(thm)], [c_479, c_3516])).
% 9.01/3.02  tff(c_3530, plain, (![C_9, A_7, B_8, C_42]: (C_9='#skF_7' | k4_zfmisc_1(A_7, B_8, C_9, C_42)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_352, c_3524])).
% 9.01/3.02  tff(c_3542, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_3530])).
% 9.01/3.02  tff(c_2772, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1181])).
% 9.01/3.02  tff(c_3572, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3542, c_2772])).
% 9.01/3.02  tff(c_3571, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3542, c_3297])).
% 9.01/3.02  tff(c_325, plain, (![C_60, A_61, B_62, D_63]: (C_60=A_61 | k1_xboole_0=B_62 | k1_xboole_0=A_61 | k2_zfmisc_1(C_60, D_63)!=k2_zfmisc_1(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.01/3.02  tff(c_331, plain, (![D_63, B_11, A_10, C_12, D_13, C_60]: (k3_zfmisc_1(A_10, B_11, C_12)=C_60 | k1_xboole_0=D_13 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k2_zfmisc_1(C_60, D_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_325])).
% 9.01/3.02  tff(c_3589, plain, (![C_60, D_63]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=C_60 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_60, D_63))), inference(superposition, [status(thm), theory('equality')], [c_3571, c_331])).
% 9.01/3.02  tff(c_3626, plain, (![C_376, D_377]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=C_376 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_376, D_377))), inference(negUnitSimplification, [status(thm)], [c_3572, c_34, c_3589])).
% 9.01/3.02  tff(c_3629, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3626])).
% 9.01/3.02  tff(c_3984, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_3629])).
% 9.01/3.02  tff(c_306, plain, (![D_56, A_7, B_8, C_9, C_59]: (D_56=C_9 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_59, D_56))), inference(superposition, [status(thm), theory('equality')], [c_12, c_294])).
% 9.01/3.02  tff(c_4039, plain, (![D_56, C_59]: (D_56='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_59, D_56))), inference(superposition, [status(thm), theory('equality')], [c_3984, c_306])).
% 9.01/3.02  tff(c_4075, plain, (![D_56, C_59]: (D_56='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_59, D_56))), inference(negUnitSimplification, [status(thm)], [c_36, c_4039])).
% 9.01/3.02  tff(c_4215, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4075])).
% 9.01/3.02  tff(c_4246, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4215, c_2])).
% 9.01/3.02  tff(c_4248, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4246])).
% 9.01/3.02  tff(c_4020, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3984, c_3572])).
% 9.01/3.02  tff(c_4252, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4248, c_4020])).
% 9.01/3.02  tff(c_182, plain, (![B_2, C_42]: (k3_zfmisc_1(k1_xboole_0, B_2, C_42)=k2_zfmisc_1(k1_xboole_0, C_42))), inference(superposition, [status(thm), theory('equality')], [c_6, c_153])).
% 9.01/3.02  tff(c_186, plain, (![B_2, C_42]: (k3_zfmisc_1(k1_xboole_0, B_2, C_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_182])).
% 9.01/3.02  tff(c_4282, plain, (![B_2, C_42]: (k3_zfmisc_1('#skF_5', B_2, C_42)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4248, c_4248, c_186])).
% 9.01/3.02  tff(c_4395, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4282, c_3984])).
% 9.01/3.02  tff(c_4539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4252, c_4395])).
% 9.01/3.02  tff(c_4540, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_4246])).
% 9.01/3.02  tff(c_4547, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4540, c_4020])).
% 9.01/3.02  tff(c_4237, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)=k2_zfmisc_1(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_4215, c_12])).
% 9.01/3.02  tff(c_4245, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4237])).
% 9.01/3.02  tff(c_4696, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4540, c_4245])).
% 9.01/3.02  tff(c_4697, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4696, c_3984])).
% 9.01/3.02  tff(c_4862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4547, c_4697])).
% 9.01/3.02  tff(c_4864, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_4075])).
% 9.01/3.02  tff(c_337, plain, (![D_63, A_7, C_60, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=C_60 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_60, D_63))), inference(superposition, [status(thm), theory('equality')], [c_12, c_325])).
% 9.01/3.02  tff(c_4024, plain, (![C_60, D_63]: (k2_zfmisc_1('#skF_5', '#skF_6')=C_60 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_60, D_63))), inference(superposition, [status(thm), theory('equality')], [c_3984, c_337])).
% 9.01/3.02  tff(c_4072, plain, (![C_60, D_63]: (k2_zfmisc_1('#skF_5', '#skF_6')=C_60 | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_60, D_63))), inference(negUnitSimplification, [status(thm)], [c_36, c_4024])).
% 9.01/3.02  tff(c_5026, plain, (![C_499, D_500]: (k2_zfmisc_1('#skF_5', '#skF_6')=C_499 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_499, D_500))), inference(negUnitSimplification, [status(thm)], [c_4864, c_4072])).
% 9.01/3.02  tff(c_5032, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=k2_zfmisc_1('#skF_5', '#skF_6') | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5026])).
% 9.01/3.02  tff(c_5042, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_5032])).
% 9.01/3.02  tff(c_8, plain, (![D_6, B_4, A_3, C_5]: (D_6=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.01/3.02  tff(c_5088, plain, (![B_4, A_3]: (B_4='#skF_6' | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5042, c_8])).
% 9.01/3.02  tff(c_5417, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_5088])).
% 9.01/3.02  tff(c_5418, plain, ('#skF_6'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_5417])).
% 9.01/3.02  tff(c_5494, plain, (k2_zfmisc_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5418, c_5042])).
% 9.01/3.02  tff(c_10, plain, (![C_5, A_3, B_4, D_6]: (C_5=A_3 | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.01/3.02  tff(c_5511, plain, (![C_5, D_6]: (C_5='#skF_5' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5494, c_10])).
% 9.01/3.02  tff(c_5528, plain, (![C_5, D_6]: (C_5='#skF_5' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_5511])).
% 9.01/3.02  tff(c_5669, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_5528])).
% 9.01/3.02  tff(c_5072, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5042, c_4864])).
% 9.01/3.02  tff(c_5674, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5669, c_5072])).
% 9.01/3.02  tff(c_5718, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5669, c_5669, c_6])).
% 9.01/3.02  tff(c_5796, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5718, c_5494])).
% 9.01/3.02  tff(c_5834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5674, c_5796])).
% 9.01/3.02  tff(c_5835, plain, (![C_5, D_6]: (C_5='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_5528])).
% 9.01/3.02  tff(c_5843, plain, ('#skF_5'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_5835])).
% 9.01/3.02  tff(c_5845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_5843])).
% 9.01/3.02  tff(c_5847, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_431])).
% 9.01/3.02  tff(c_22, plain, (![A_20, B_21, C_22, D_23]: (k4_zfmisc_1(A_20, B_21, C_22, D_23)!=k1_xboole_0 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.01/3.02  tff(c_5888, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5847, c_22])).
% 9.01/3.02  tff(c_5897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_5888])).
% 9.01/3.02  tff(c_5898, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 9.01/3.02  tff(c_5940, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_5898])).
% 9.01/3.02  tff(c_5899, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 9.01/3.02  tff(c_5935, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5899, c_42])).
% 9.01/3.02  tff(c_6073, plain, (![D_562, B_563, A_564, C_565]: (D_562=B_563 | k1_xboole_0=B_563 | k1_xboole_0=A_564 | k2_zfmisc_1(C_565, D_562)!=k2_zfmisc_1(A_564, B_563))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.01/3.02  tff(c_6966, plain, (![A_685, C_684, B_683, D_682, D_686, C_687]: (D_686=D_682 | k1_xboole_0=D_686 | k3_zfmisc_1(A_685, B_683, C_687)=k1_xboole_0 | k4_zfmisc_1(A_685, B_683, C_687, D_686)!=k2_zfmisc_1(C_684, D_682))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6073])).
% 9.01/3.02  tff(c_6981, plain, (![D_682, C_684]: (D_682='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_684, D_682))), inference(superposition, [status(thm), theory('equality')], [c_5935, c_6966])).
% 9.01/3.02  tff(c_7088, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6981])).
% 9.01/3.02  tff(c_5952, plain, (![A_549, B_550, C_551]: (k2_zfmisc_1(k2_zfmisc_1(A_549, B_550), C_551)=k3_zfmisc_1(A_549, B_550, C_551))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.01/3.02  tff(c_5961, plain, (![C_551, A_549, B_550]: (k1_xboole_0=C_551 | k2_zfmisc_1(A_549, B_550)=k1_xboole_0 | k3_zfmisc_1(A_549, B_550, C_551)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5952, c_2])).
% 9.01/3.02  tff(c_7145, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7088, c_5961])).
% 9.01/3.02  tff(c_7162, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7145])).
% 9.01/3.02  tff(c_7187, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7162, c_2])).
% 9.01/3.02  tff(c_7197, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_40, c_7187])).
% 9.01/3.02  tff(c_7137, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_7088, c_14])).
% 9.01/3.02  tff(c_7146, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7137])).
% 9.01/3.02  tff(c_7448, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7197, c_7146])).
% 9.01/3.02  tff(c_7449, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7448, c_5935])).
% 9.01/3.02  tff(c_6223, plain, (![A_581, B_582, C_583, D_584]: (k4_zfmisc_1(A_581, B_582, C_583, D_584)!=k1_xboole_0 | k1_xboole_0=D_584 | k1_xboole_0=C_583 | k1_xboole_0=B_582 | k1_xboole_0=A_581)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.01/3.02  tff(c_6226, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5935, c_6223])).
% 9.01/3.02  tff(c_6239, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_40, c_6226])).
% 9.01/3.02  tff(c_6248, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6239])).
% 9.01/3.02  tff(c_7221, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7197, c_6248])).
% 9.01/3.02  tff(c_7663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7449, c_7221])).
% 9.01/3.02  tff(c_7664, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7145])).
% 9.01/3.02  tff(c_7979, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7664, c_7146])).
% 9.01/3.02  tff(c_7980, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7979, c_5935])).
% 9.01/3.02  tff(c_7687, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7664, c_6248])).
% 9.01/3.02  tff(c_8244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7980, c_7687])).
% 9.01/3.02  tff(c_8245, plain, (![D_682, C_684]: (k1_xboole_0='#skF_8' | D_682='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_684, D_682))), inference(splitRight, [status(thm)], [c_6981])).
% 9.01/3.02  tff(c_8247, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_8245])).
% 9.01/3.02  tff(c_8279, plain, (![A_20, B_21, C_22]: (k4_zfmisc_1(A_20, B_21, C_22, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8247, c_8247, c_24])).
% 9.01/3.02  tff(c_8477, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8279, c_5935])).
% 9.01/3.02  tff(c_8268, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8247, c_6248])).
% 9.01/3.02  tff(c_8623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8477, c_8268])).
% 9.01/3.02  tff(c_8626, plain, (![D_802, C_803]: (D_802='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_803, D_802))), inference(splitRight, [status(thm)], [c_8245])).
% 9.01/3.02  tff(c_8629, plain, (![D_13, A_10, B_11, C_12]: (D_13='#skF_8' | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_8626])).
% 9.01/3.02  tff(c_8659, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_8629])).
% 9.01/3.02  tff(c_8661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5940, c_8659])).
% 9.01/3.02  tff(c_8663, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6239])).
% 9.01/3.02  tff(c_8669, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8663, c_22])).
% 9.01/3.02  tff(c_8678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_8669])).
% 9.01/3.02  tff(c_8679, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_5898])).
% 9.01/3.02  tff(c_8686, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_8679])).
% 9.01/3.02  tff(c_8698, plain, (![A_809, B_810, C_811]: (k2_zfmisc_1(k2_zfmisc_1(A_809, B_810), C_811)=k3_zfmisc_1(A_809, B_810, C_811))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.01/3.02  tff(c_8701, plain, (![A_809, B_810, C_811, C_9]: (k3_zfmisc_1(k2_zfmisc_1(A_809, B_810), C_811, C_9)=k2_zfmisc_1(k3_zfmisc_1(A_809, B_810, C_811), C_9))), inference(superposition, [status(thm), theory('equality')], [c_8698, c_12])).
% 9.01/3.02  tff(c_8897, plain, (![A_809, B_810, C_811, C_9]: (k3_zfmisc_1(k2_zfmisc_1(A_809, B_810), C_811, C_9)=k4_zfmisc_1(A_809, B_810, C_811, C_9))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_8701])).
% 9.01/3.02  tff(c_8680, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_5898])).
% 9.01/3.02  tff(c_8681, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8680, c_5935])).
% 9.01/3.02  tff(c_8948, plain, (![A_837, B_838, C_839, D_840]: (k4_zfmisc_1(A_837, B_838, C_839, D_840)!=k1_xboole_0 | k1_xboole_0=D_840 | k1_xboole_0=C_839 | k1_xboole_0=B_838 | k1_xboole_0=A_837)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.01/3.02  tff(c_8951, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8681, c_8948])).
% 9.01/3.02  tff(c_8964, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_8951])).
% 9.01/3.02  tff(c_8973, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8964])).
% 9.01/3.02  tff(c_9164, plain, (![D_869, C_870, A_872, E_867, B_871, F_868]: (E_867=B_871 | k3_zfmisc_1(A_872, B_871, C_870)=k1_xboole_0 | k3_zfmisc_1(D_869, E_867, F_868)!=k3_zfmisc_1(A_872, B_871, C_870))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.01/3.02  tff(c_9176, plain, (![D_869, A_809, C_811, B_810, E_867, F_868, C_9]: (E_867=C_811 | k3_zfmisc_1(k2_zfmisc_1(A_809, B_810), C_811, C_9)=k1_xboole_0 | k4_zfmisc_1(A_809, B_810, C_811, C_9)!=k3_zfmisc_1(D_869, E_867, F_868))), inference(superposition, [status(thm), theory('equality')], [c_8897, c_9164])).
% 9.01/3.02  tff(c_10770, plain, (![F_1025, D_1029, B_1026, C_1024, C_1027, E_1028, A_1030]: (E_1028=C_1024 | k4_zfmisc_1(A_1030, B_1026, C_1024, C_1027)=k1_xboole_0 | k4_zfmisc_1(A_1030, B_1026, C_1024, C_1027)!=k3_zfmisc_1(D_1029, E_1028, F_1025))), inference(demodulation, [status(thm), theory('equality')], [c_8897, c_9176])).
% 9.01/3.02  tff(c_10794, plain, (![E_1028, D_1029, F_1025]: (E_1028='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1029, E_1028, F_1025))), inference(superposition, [status(thm), theory('equality')], [c_8681, c_10770])).
% 9.01/3.02  tff(c_10809, plain, (![E_1028, D_1029, F_1025]: (E_1028='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1029, E_1028, F_1025))), inference(demodulation, [status(thm), theory('equality')], [c_8681, c_10794])).
% 9.01/3.02  tff(c_10860, plain, (![E_1038, D_1039, F_1040]: (E_1038='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1039, E_1038, F_1040))), inference(negUnitSimplification, [status(thm)], [c_8973, c_10809])).
% 9.01/3.02  tff(c_10866, plain, (![C_811, A_809, B_810, C_9]: (C_811='#skF_7' | k4_zfmisc_1(A_809, B_810, C_811, C_9)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8897, c_10860])).
% 9.01/3.02  tff(c_10878, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_10866])).
% 9.01/3.02  tff(c_8870, plain, (![D_829, B_830, A_831, C_832]: (D_829=B_830 | k1_xboole_0=B_830 | k1_xboole_0=A_831 | k2_zfmisc_1(C_832, D_829)!=k2_zfmisc_1(A_831, B_830))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.01/3.02  tff(c_9663, plain, (![D_936, C_934, A_937, B_935, D_938, C_939]: (D_938=D_936 | k1_xboole_0=D_938 | k3_zfmisc_1(A_937, B_935, C_939)=k1_xboole_0 | k4_zfmisc_1(A_937, B_935, C_939, D_938)!=k2_zfmisc_1(C_934, D_936))), inference(superposition, [status(thm), theory('equality')], [c_14, c_8870])).
% 9.01/3.02  tff(c_9675, plain, (![D_936, C_934]: (D_936='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_934, D_936))), inference(superposition, [status(thm), theory('equality')], [c_8681, c_9663])).
% 9.01/3.02  tff(c_9699, plain, (![D_936, C_934]: (D_936='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_934, D_936))), inference(negUnitSimplification, [status(thm)], [c_34, c_9675])).
% 9.01/3.02  tff(c_9704, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9699])).
% 9.01/3.02  tff(c_8707, plain, (![C_811, A_809, B_810]: (k1_xboole_0=C_811 | k2_zfmisc_1(A_809, B_810)=k1_xboole_0 | k3_zfmisc_1(A_809, B_810, C_811)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8698, c_2])).
% 9.01/3.02  tff(c_9761, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9704, c_8707])).
% 9.01/3.02  tff(c_9806, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9761])).
% 9.01/3.02  tff(c_9831, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9806, c_2])).
% 9.01/3.02  tff(c_9841, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_40, c_9831])).
% 9.01/3.02  tff(c_9861, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9841, c_8973])).
% 9.01/3.02  tff(c_9753, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_9704, c_14])).
% 9.01/3.02  tff(c_9762, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9753])).
% 9.01/3.02  tff(c_10137, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9841, c_9762])).
% 9.01/3.02  tff(c_10138, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10137, c_8681])).
% 9.01/3.02  tff(c_10385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9861, c_10138])).
% 9.01/3.02  tff(c_10386, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_9761])).
% 9.01/3.02  tff(c_10405, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10386, c_8973])).
% 9.01/3.02  tff(c_10627, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10386, c_9762])).
% 9.01/3.02  tff(c_10628, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10627, c_8681])).
% 9.01/3.02  tff(c_10630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10405, c_10628])).
% 9.01/3.02  tff(c_10632, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_9699])).
% 9.01/3.02  tff(c_8839, plain, (![C_825, A_826, B_827, D_828]: (C_825=A_826 | k1_xboole_0=B_827 | k1_xboole_0=A_826 | k2_zfmisc_1(C_825, D_828)!=k2_zfmisc_1(A_826, B_827))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.01/3.02  tff(c_10633, plain, (![D_1008, B_1005, A_1007, C_1009, C_1004, D_1006]: (k3_zfmisc_1(A_1007, B_1005, C_1009)=C_1004 | k1_xboole_0=D_1008 | k3_zfmisc_1(A_1007, B_1005, C_1009)=k1_xboole_0 | k4_zfmisc_1(A_1007, B_1005, C_1009, D_1008)!=k2_zfmisc_1(C_1004, D_1006))), inference(superposition, [status(thm), theory('equality')], [c_14, c_8839])).
% 9.01/3.02  tff(c_10645, plain, (![C_1004, D_1006]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_1004 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1004, D_1006))), inference(superposition, [status(thm), theory('equality')], [c_8681, c_10633])).
% 9.01/3.02  tff(c_10669, plain, (![C_1004, D_1006]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_1004 | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1004, D_1006))), inference(negUnitSimplification, [status(thm)], [c_34, c_10645])).
% 9.01/3.02  tff(c_10706, plain, (![C_1015, D_1016]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_1015 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1015, D_1016))), inference(negUnitSimplification, [status(thm)], [c_10632, c_10669])).
% 9.01/3.02  tff(c_10709, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_10706])).
% 9.01/3.02  tff(c_11118, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10878, c_10709])).
% 9.01/3.02  tff(c_11121, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_11118])).
% 9.01/3.02  tff(c_10907, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10878, c_10632])).
% 9.01/3.02  tff(c_11157, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11121, c_10907])).
% 9.01/3.02  tff(c_18, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (E_18=B_15 | k3_zfmisc_1(A_14, B_15, C_16)=k1_xboole_0 | k3_zfmisc_1(D_17, E_18, F_19)!=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.01/3.02  tff(c_11188, plain, (![E_18, D_17, F_19]: (E_18='#skF_6' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k1_xboole_0 | k3_zfmisc_1(D_17, E_18, F_19)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11121, c_18])).
% 9.01/3.02  tff(c_11214, plain, (![E_18, D_17, F_19]: (E_18='#skF_6' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0 | k3_zfmisc_1(D_17, E_18, F_19)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11121, c_11188])).
% 9.01/3.02  tff(c_11950, plain, (![E_18, D_17, F_19]: (E_18='#skF_6' | k3_zfmisc_1(D_17, E_18, F_19)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_11157, c_11214])).
% 9.01/3.02  tff(c_11953, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_11950])).
% 9.01/3.02  tff(c_11955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8686, c_11953])).
% 9.01/3.02  tff(c_11956, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_8964])).
% 9.01/3.02  tff(c_11958, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_11956])).
% 9.01/3.02  tff(c_11976, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11958, c_40])).
% 9.01/3.02  tff(c_11973, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11958, c_38])).
% 9.01/3.02  tff(c_11975, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11958, c_36])).
% 9.01/3.02  tff(c_11974, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11958, c_34])).
% 9.01/3.02  tff(c_11957, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8964])).
% 9.01/3.02  tff(c_12072, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_11958, c_11957])).
% 9.01/3.02  tff(c_8759, plain, (![A_816, B_817, C_818, D_819]: (k2_zfmisc_1(k3_zfmisc_1(A_816, B_817, C_818), D_819)=k4_zfmisc_1(A_816, B_817, C_818, D_819))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.01/3.02  tff(c_8768, plain, (![D_819, A_816, B_817, C_818]: (k1_xboole_0=D_819 | k3_zfmisc_1(A_816, B_817, C_818)=k1_xboole_0 | k4_zfmisc_1(A_816, B_817, C_818, D_819)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8759, c_2])).
% 9.01/3.02  tff(c_12435, plain, (![D_1193, A_1194, B_1195, C_1196]: (D_1193='#skF_7' | k3_zfmisc_1(A_1194, B_1195, C_1196)='#skF_7' | k4_zfmisc_1(A_1194, B_1195, C_1196, D_1193)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11958, c_11958, c_11958, c_8768])).
% 9.01/3.02  tff(c_12450, plain, ('#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_12072, c_12435])).
% 9.01/3.02  tff(c_12461, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_11974, c_12450])).
% 9.01/3.02  tff(c_11962, plain, (![C_811, A_809, B_810]: (C_811='#skF_7' | k2_zfmisc_1(A_809, B_810)='#skF_7' | k3_zfmisc_1(A_809, B_810, C_811)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11958, c_11958, c_11958, c_8707])).
% 9.01/3.02  tff(c_12468, plain, ('#skF_7'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_12461, c_11962])).
% 9.01/3.02  tff(c_12494, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_11975, c_12468])).
% 9.01/3.02  tff(c_11966, plain, (![B_2, A_1]: (B_2='#skF_7' | A_1='#skF_7' | k2_zfmisc_1(A_1, B_2)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11958, c_11958, c_11958, c_2])).
% 9.01/3.02  tff(c_12515, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12494, c_11966])).
% 9.01/3.02  tff(c_12529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11976, c_11973, c_12515])).
% 9.01/3.02  tff(c_12530, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_11956])).
% 9.01/3.02  tff(c_12549, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12530, c_40])).
% 9.01/3.02  tff(c_12548, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12530, c_36])).
% 9.01/3.02  tff(c_12547, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12530, c_34])).
% 9.01/3.02  tff(c_12751, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12530, c_11957])).
% 9.01/3.02  tff(c_13009, plain, (![D_1253, A_1254, B_1255, C_1256]: (D_1253='#skF_6' | k3_zfmisc_1(A_1254, B_1255, C_1256)='#skF_6' | k4_zfmisc_1(A_1254, B_1255, C_1256, D_1253)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12530, c_12530, c_12530, c_8768])).
% 9.01/3.02  tff(c_13024, plain, ('#skF_6'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_12751, c_13009])).
% 9.01/3.02  tff(c_13035, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_12547, c_13024])).
% 9.01/3.02  tff(c_12877, plain, (![B_1235, A_1236]: (B_1235='#skF_6' | A_1236='#skF_6' | k2_zfmisc_1(A_1236, B_1235)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12530, c_12530, c_12530, c_2])).
% 9.01/3.02  tff(c_12889, plain, (![C_9, A_7, B_8]: (C_9='#skF_6' | k2_zfmisc_1(A_7, B_8)='#skF_6' | k3_zfmisc_1(A_7, B_8, C_9)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12, c_12877])).
% 9.01/3.02  tff(c_13042, plain, ('#skF_6'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_13035, c_12889])).
% 9.01/3.02  tff(c_13068, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_12548, c_13042])).
% 9.01/3.02  tff(c_12539, plain, (![B_2, A_1]: (B_2='#skF_6' | A_1='#skF_6' | k2_zfmisc_1(A_1, B_2)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12530, c_12530, c_12530, c_2])).
% 9.01/3.02  tff(c_13089, plain, ('#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13068, c_12539])).
% 9.01/3.02  tff(c_13103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12549, c_8686, c_13089])).
% 9.01/3.02  tff(c_13104, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_8679])).
% 9.01/3.02  tff(c_13126, plain, (![A_1259, B_1260, C_1261]: (k2_zfmisc_1(k2_zfmisc_1(A_1259, B_1260), C_1261)=k3_zfmisc_1(A_1259, B_1260, C_1261))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.01/3.02  tff(c_13142, plain, (![A_7, B_8, C_9, C_1261]: (k3_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9, C_1261)=k2_zfmisc_1(k3_zfmisc_1(A_7, B_8, C_9), C_1261))), inference(superposition, [status(thm), theory('equality')], [c_12, c_13126])).
% 9.01/3.02  tff(c_13325, plain, (![A_7, B_8, C_9, C_1261]: (k3_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9, C_1261)=k4_zfmisc_1(A_7, B_8, C_9, C_1261))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_13142])).
% 9.01/3.02  tff(c_13105, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_8679])).
% 9.01/3.02  tff(c_13110, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13105, c_8681])).
% 9.01/3.02  tff(c_13402, plain, (![A_1291, B_1292, C_1293, D_1294]: (k4_zfmisc_1(A_1291, B_1292, C_1293, D_1294)!=k1_xboole_0 | k1_xboole_0=D_1294 | k1_xboole_0=C_1293 | k1_xboole_0=B_1292 | k1_xboole_0=A_1291)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.01/3.02  tff(c_13405, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13110, c_13402])).
% 9.01/3.02  tff(c_13418, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_34, c_13405])).
% 9.01/3.02  tff(c_13427, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13418])).
% 9.01/3.02  tff(c_13657, plain, (![F_1323, D_1324, C_1325, E_1322, B_1326, A_1327]: (E_1322=B_1326 | k3_zfmisc_1(A_1327, B_1326, C_1325)=k1_xboole_0 | k3_zfmisc_1(D_1324, E_1322, F_1323)!=k3_zfmisc_1(A_1327, B_1326, C_1325))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.01/3.02  tff(c_13669, plain, (![F_1323, D_1324, A_7, E_1322, C_1261, B_8, C_9]: (E_1322=C_9 | k3_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9, C_1261)=k1_xboole_0 | k4_zfmisc_1(A_7, B_8, C_9, C_1261)!=k3_zfmisc_1(D_1324, E_1322, F_1323))), inference(superposition, [status(thm), theory('equality')], [c_13325, c_13657])).
% 9.01/3.02  tff(c_14957, plain, (![F_1465, A_1468, D_1463, C_1469, C_1467, E_1464, B_1466]: (E_1464=C_1467 | k4_zfmisc_1(A_1468, B_1466, C_1467, C_1469)=k1_xboole_0 | k4_zfmisc_1(A_1468, B_1466, C_1467, C_1469)!=k3_zfmisc_1(D_1463, E_1464, F_1465))), inference(demodulation, [status(thm), theory('equality')], [c_13325, c_13669])).
% 9.01/3.02  tff(c_14975, plain, (![E_1464, D_1463, F_1465]: (E_1464='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1463, E_1464, F_1465))), inference(superposition, [status(thm), theory('equality')], [c_13110, c_14957])).
% 9.01/3.02  tff(c_14996, plain, (![E_1464, D_1463, F_1465]: (E_1464='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1463, E_1464, F_1465))), inference(demodulation, [status(thm), theory('equality')], [c_13110, c_14975])).
% 9.01/3.02  tff(c_15002, plain, (![E_1470, D_1471, F_1472]: (E_1470='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1471, E_1470, F_1472))), inference(negUnitSimplification, [status(thm)], [c_13427, c_14996])).
% 9.01/3.02  tff(c_15008, plain, (![C_9, A_7, B_8, C_1261]: (C_9='#skF_7' | k4_zfmisc_1(A_7, B_8, C_9, C_1261)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13325, c_15002])).
% 9.01/3.02  tff(c_15020, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_15008])).
% 9.01/3.02  tff(c_15022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13104, c_15020])).
% 9.01/3.02  tff(c_15023, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_13418])).
% 9.01/3.02  tff(c_15301, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_40])).
% 9.01/3.02  tff(c_15298, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_38])).
% 9.01/3.02  tff(c_15299, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_34])).
% 9.01/3.02  tff(c_26, plain, (![A_20, B_21, D_23]: (k4_zfmisc_1(A_20, B_21, k1_xboole_0, D_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.01/3.02  tff(c_15292, plain, (![A_20, B_21, D_23]: (k4_zfmisc_1(A_20, B_21, '#skF_7', D_23)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_15023, c_26])).
% 9.01/3.02  tff(c_15468, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15292, c_13110])).
% 9.01/3.02  tff(c_13210, plain, (![A_1268, B_1269, C_1270, D_1271]: (k2_zfmisc_1(k3_zfmisc_1(A_1268, B_1269, C_1270), D_1271)=k4_zfmisc_1(A_1268, B_1269, C_1270, D_1271))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.01/3.02  tff(c_13219, plain, (![D_1271, A_1268, B_1269, C_1270]: (k1_xboole_0=D_1271 | k3_zfmisc_1(A_1268, B_1269, C_1270)=k1_xboole_0 | k4_zfmisc_1(A_1268, B_1269, C_1270, D_1271)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13210, c_2])).
% 9.01/3.02  tff(c_15758, plain, (![D_1555, A_1556, B_1557, C_1558]: (D_1555='#skF_7' | k3_zfmisc_1(A_1556, B_1557, C_1558)='#skF_7' | k4_zfmisc_1(A_1556, B_1557, C_1558, D_1555)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_15023, c_15023, c_13219])).
% 9.01/3.02  tff(c_15767, plain, ('#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_15468, c_15758])).
% 9.01/3.02  tff(c_15780, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_15299, c_15767])).
% 9.01/3.02  tff(c_13135, plain, (![C_1261, A_1259, B_1260]: (k1_xboole_0=C_1261 | k2_zfmisc_1(A_1259, B_1260)=k1_xboole_0 | k3_zfmisc_1(A_1259, B_1260, C_1261)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13126, c_2])).
% 9.01/3.02  tff(c_15286, plain, (![C_1261, A_1259, B_1260]: (C_1261='#skF_7' | k2_zfmisc_1(A_1259, B_1260)='#skF_7' | k3_zfmisc_1(A_1259, B_1260, C_1261)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_15023, c_15023, c_13135])).
% 9.01/3.02  tff(c_15791, plain, ('#skF_7'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_15780, c_15286])).
% 9.01/3.02  tff(c_15817, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_13104, c_15791])).
% 9.01/3.02  tff(c_15291, plain, (![B_2, A_1]: (B_2='#skF_7' | A_1='#skF_7' | k2_zfmisc_1(A_1, B_2)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15023, c_15023, c_15023, c_2])).
% 9.01/3.02  tff(c_15838, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15817, c_15291])).
% 9.01/3.02  tff(c_15852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15301, c_15298, c_15838])).
% 9.01/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.01/3.02  
% 9.01/3.02  Inference rules
% 9.01/3.02  ----------------------
% 9.01/3.02  #Ref     : 66
% 9.01/3.02  #Sup     : 3896
% 9.01/3.02  #Fact    : 0
% 9.01/3.02  #Define  : 0
% 9.01/3.02  #Split   : 31
% 9.01/3.02  #Chain   : 0
% 9.01/3.02  #Close   : 0
% 9.01/3.02  
% 9.01/3.02  Ordering : KBO
% 9.01/3.02  
% 9.01/3.02  Simplification rules
% 9.01/3.02  ----------------------
% 9.01/3.02  #Subsume      : 808
% 9.01/3.02  #Demod        : 3052
% 9.01/3.02  #Tautology    : 2039
% 9.01/3.02  #SimpNegUnit  : 190
% 9.01/3.02  #BackRed      : 716
% 9.01/3.02  
% 9.01/3.02  #Partial instantiations: 0
% 9.01/3.02  #Strategies tried      : 1
% 9.01/3.02  
% 9.01/3.02  Timing (in seconds)
% 9.01/3.02  ----------------------
% 9.01/3.02  Preprocessing        : 0.30
% 9.01/3.02  Parsing              : 0.15
% 9.01/3.02  CNF conversion       : 0.02
% 9.01/3.02  Main loop            : 1.90
% 9.01/3.02  Inferencing          : 0.62
% 9.01/3.02  Reduction            : 0.59
% 9.01/3.02  Demodulation         : 0.41
% 9.01/3.02  BG Simplification    : 0.07
% 9.01/3.02  Subsumption          : 0.48
% 9.01/3.02  Abstraction          : 0.11
% 9.01/3.02  MUC search           : 0.00
% 9.01/3.02  Cooper               : 0.00
% 9.01/3.02  Total                : 2.29
% 9.01/3.02  Index Insertion      : 0.00
% 9.01/3.02  Index Deletion       : 0.00
% 9.01/3.02  Index Matching       : 0.00
% 9.01/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
