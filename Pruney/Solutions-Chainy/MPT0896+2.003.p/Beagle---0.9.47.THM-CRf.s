%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:45 EST 2020

% Result     : Theorem 8.16s
% Output     : CNFRefutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :  369 (8203 expanded)
%              Number of leaves         :   21 (2411 expanded)
%              Depth                    :   32
%              Number of atoms          :  654 (26320 expanded)
%              Number of equality atoms :  622 (26288 expanded)
%              Maximal formula depth    :   18 (   3 average)
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

tff(f_76,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_102,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),D_13) = k4_zfmisc_1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_333,plain,(
    ! [D_56,B_57,A_58,C_59] :
      ( D_56 = B_57
      | k1_xboole_0 = B_57
      | k1_xboole_0 = A_58
      | k2_zfmisc_1(C_59,D_56) != k2_zfmisc_1(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_907,plain,(
    ! [B_126,D_127,C_130,A_128,D_129,C_131] :
      ( D_129 = D_127
      | k1_xboole_0 = D_129
      | k3_zfmisc_1(A_128,B_126,C_130) = k1_xboole_0
      | k4_zfmisc_1(A_128,B_126,C_130,D_129) != k2_zfmisc_1(C_131,D_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_333])).

tff(c_931,plain,(
    ! [D_127,C_131] :
      ( D_127 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_131,D_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_907])).

tff(c_993,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_931])).

tff(c_114,plain,(
    ! [A_27,B_28,C_29] : k2_zfmisc_1(k2_zfmisc_1(A_27,B_28),C_29) = k3_zfmisc_1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [C_29,A_27,B_28] :
      ( k1_xboole_0 = C_29
      | k2_zfmisc_1(A_27,B_28) = k1_xboole_0
      | k3_zfmisc_1(A_27,B_28,C_29) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_2])).

tff(c_1033,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_123])).

tff(c_1037,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1033])).

tff(c_1068,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1037,c_2])).

tff(c_1070,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1068])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1028,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_14])).

tff(c_1035,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1028])).

tff(c_1357,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_1035])).

tff(c_1358,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_34])).

tff(c_154,plain,(
    ! [A_30,B_31,C_32,D_33] : k2_zfmisc_1(k3_zfmisc_1(A_30,B_31,C_32),D_33) = k4_zfmisc_1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_415,plain,(
    ! [D_64,A_65,B_66,C_67] :
      ( k1_xboole_0 = D_64
      | k3_zfmisc_1(A_65,B_66,C_67) = k1_xboole_0
      | k4_zfmisc_1(A_65,B_66,C_67,D_64) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_2])).

tff(c_430,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_415])).

tff(c_466,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_1125,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_466])).

tff(c_1551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_1125])).

tff(c_1552,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1068])).

tff(c_1880,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1035])).

tff(c_1881,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1880,c_34])).

tff(c_1567,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_466])).

tff(c_1965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1567])).

tff(c_1966,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_2249,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1966,c_1035])).

tff(c_2250,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2249,c_34])).

tff(c_1979,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1966,c_466])).

tff(c_2491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_1979])).

tff(c_2493,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_931])).

tff(c_467,plain,(
    ! [A_74,A_76,C_78,B_73,D_77,B_75] :
      ( D_77 = B_73
      | k1_xboole_0 = B_73
      | k1_xboole_0 = A_74
      | k4_zfmisc_1(A_76,B_75,C_78,D_77) != k2_zfmisc_1(A_74,B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_333])).

tff(c_625,plain,(
    ! [B_89,A_90] :
      ( B_89 = '#skF_8'
      | k1_xboole_0 = B_89
      | k1_xboole_0 = A_90
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(A_90,B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_467])).

tff(c_628,plain,(
    ! [D_13,A_10,B_11,C_12] :
      ( D_13 = '#skF_8'
      | k1_xboole_0 = D_13
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_625])).

tff(c_2943,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_628])).

tff(c_2944,plain,
    ( '#skF_8' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_2943])).

tff(c_2977,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2944])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k3_zfmisc_1(A_14,B_15,C_16) != k1_xboole_0
      | k1_xboole_0 = C_16
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3008,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2977,c_16])).

tff(c_3025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_3008])).

tff(c_3026,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2944])).

tff(c_3032,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3026,c_34])).

tff(c_232,plain,(
    ! [C_43,A_44,B_45,D_46] :
      ( C_43 = A_44
      | k1_xboole_0 = B_45
      | k1_xboole_0 = A_44
      | k2_zfmisc_1(C_43,D_46) != k2_zfmisc_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3059,plain,(
    ! [D_285,C_284,C_289,B_286,D_288,A_287] :
      ( k3_zfmisc_1(A_287,B_286,C_289) = C_284
      | k1_xboole_0 = D_288
      | k3_zfmisc_1(A_287,B_286,C_289) = k1_xboole_0
      | k4_zfmisc_1(A_287,B_286,C_289,D_288) != k2_zfmisc_1(C_284,D_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_232])).

tff(c_3062,plain,(
    ! [C_284,D_285] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = C_284
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_284,D_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3032,c_3059])).

tff(c_3132,plain,(
    ! [C_295,D_296] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = C_295
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_295,D_296) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2493,c_26,c_3062])).

tff(c_3135,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3132])).

tff(c_3242,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3135])).

tff(c_345,plain,(
    ! [D_56,A_7,B_8,C_9,C_59] :
      ( D_56 = C_9
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_59,D_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_333])).

tff(c_3297,plain,(
    ! [D_56,C_59] :
      ( D_56 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_59,D_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3242,c_345])).

tff(c_3553,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3297])).

tff(c_3584,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3553,c_2])).

tff(c_3586,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3584])).

tff(c_3027,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2944])).

tff(c_3598,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3586,c_3027])).

tff(c_3575,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = k2_zfmisc_1(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_3553,c_12])).

tff(c_3583,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3575])).

tff(c_3723,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3586,c_3583])).

tff(c_3724,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3723,c_3242])).

tff(c_3726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3598,c_3724])).

tff(c_3727,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3584])).

tff(c_3740,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3727,c_3027])).

tff(c_3866,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3727,c_3583])).

tff(c_3867,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_3242])).

tff(c_3891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3740,c_3867])).

tff(c_3893,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3297])).

tff(c_3892,plain,(
    ! [D_56,C_59] :
      ( k1_xboole_0 = '#skF_7'
      | D_56 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_59,D_56) ) ),
    inference(splitRight,[status(thm)],[c_3297])).

tff(c_3894,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3892])).

tff(c_3906,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3894,c_3027])).

tff(c_18,plain,(
    ! [A_14,B_15] : k3_zfmisc_1(A_14,B_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3928,plain,(
    ! [A_14,B_15] : k3_zfmisc_1(A_14,B_15,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3894,c_3894,c_18])).

tff(c_4130,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3928,c_3242])).

tff(c_4132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3906,c_4130])).

tff(c_4173,plain,(
    ! [D_386,C_387] :
      ( D_386 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_387,D_386) ) ),
    inference(splitRight,[status(thm)],[c_3892])).

tff(c_4179,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_7'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4173])).

tff(c_4189,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4179])).

tff(c_4216,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4189,c_3242])).

tff(c_244,plain,(
    ! [C_43,A_7,D_46,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = C_43
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_43,D_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_232])).

tff(c_4224,plain,(
    ! [C_43,D_46] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = C_43
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_43,D_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4216,c_244])).

tff(c_4395,plain,(
    ! [C_401,D_402] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = C_401
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_401,D_402) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3893,c_28,c_4224])).

tff(c_4401,plain,(
    ! [A_7,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = k2_zfmisc_1('#skF_5','#skF_6')
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4395])).

tff(c_4457,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4401])).

tff(c_8,plain,(
    ! [D_6,B_4,A_3,C_5] :
      ( D_6 = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4497,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_6'
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4457,c_8])).

tff(c_4739,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4497])).

tff(c_4740,plain,(
    '#skF_6' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_4739])).

tff(c_4762,plain,(
    k2_zfmisc_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4740,c_4457])).

tff(c_4779,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4762,c_8])).

tff(c_4796,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4779])).

tff(c_4967,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4796])).

tff(c_5007,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_4967,c_6])).

tff(c_5017,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5007,c_4762])).

tff(c_4487,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4457,c_3893])).

tff(c_4971,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_4487])).

tff(c_5119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5017,c_4971])).

tff(c_5121,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4796])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4,D_6] :
      ( C_5 = A_3
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4785,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_5'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4762,c_10])).

tff(c_4797,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4785])).

tff(c_5122,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4797])).

tff(c_5123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5121,c_5122])).

tff(c_5124,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_4797])).

tff(c_5151,plain,(
    '#skF_5' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5124])).

tff(c_5153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_5151])).

tff(c_5155,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_163,plain,(
    ! [D_33,A_30,B_31,C_32] :
      ( k1_xboole_0 = D_33
      | k3_zfmisc_1(A_30,B_31,C_32) = k1_xboole_0
      | k4_zfmisc_1(A_30,B_31,C_32,D_33) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_2])).

tff(c_5160,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5155,c_163])).

tff(c_5165,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_5160])).

tff(c_5176,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5165,c_16])).

tff(c_5188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_5176])).

tff(c_5189,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_5200,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5189])).

tff(c_5190,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_5195,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5190,c_34])).

tff(c_5314,plain,(
    ! [D_448,B_449,A_450,C_451] :
      ( D_448 = B_449
      | k1_xboole_0 = B_449
      | k1_xboole_0 = A_450
      | k2_zfmisc_1(C_451,D_448) != k2_zfmisc_1(A_450,B_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5942,plain,(
    ! [D_529,B_526,D_525,A_527,C_528,C_530] :
      ( D_529 = D_525
      | k1_xboole_0 = D_529
      | k3_zfmisc_1(A_527,B_526,C_530) = k1_xboole_0
      | k4_zfmisc_1(A_527,B_526,C_530,D_529) != k2_zfmisc_1(C_528,D_525) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5314])).

tff(c_5966,plain,(
    ! [D_525,C_528] :
      ( D_525 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_528,D_525) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5195,c_5942])).

tff(c_6025,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5966])).

tff(c_6056,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_16])).

tff(c_6065,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6056])).

tff(c_6067,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6065])).

tff(c_6053,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_14])).

tff(c_6062,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6053])).

tff(c_6369,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6067,c_6062])).

tff(c_6370,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6369,c_5195])).

tff(c_5268,plain,(
    ! [A_441,B_442,C_443,D_444] : k2_zfmisc_1(k3_zfmisc_1(A_441,B_442,C_443),D_444) = k4_zfmisc_1(A_441,B_442,C_443,D_444) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5513,plain,(
    ! [D_472,A_473,B_474,C_475] :
      ( k1_xboole_0 = D_472
      | k3_zfmisc_1(A_473,B_474,C_475) = k1_xboole_0
      | k4_zfmisc_1(A_473,B_474,C_475,D_472) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5268,c_2])).

tff(c_5528,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5195,c_5513])).

tff(c_5537,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5528])).

tff(c_6078,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6067,c_5537])).

tff(c_6618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6370,c_6078])).

tff(c_6619,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6065])).

tff(c_6631,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6619,c_5537])).

tff(c_6942,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6619,c_6062])).

tff(c_6943,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6942,c_5195])).

tff(c_6995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6631,c_6943])).

tff(c_6996,plain,(
    ! [D_525,C_528] :
      ( k1_xboole_0 = '#skF_8'
      | D_525 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_528,D_525) ) ),
    inference(splitRight,[status(thm)],[c_5966])).

tff(c_7012,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_6996])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5281,plain,(
    ! [A_441,B_442,C_443] : k4_zfmisc_1(A_441,B_442,C_443,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5268,c_4])).

tff(c_7032,plain,(
    ! [A_441,B_442,C_443] : k4_zfmisc_1(A_441,B_442,C_443,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7012,c_7012,c_5281])).

tff(c_7296,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7032,c_5195])).

tff(c_7024,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7012,c_5537])).

tff(c_7457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7296,c_7024])).

tff(c_7493,plain,(
    ! [D_647,C_648] :
      ( D_647 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_648,D_647) ) ),
    inference(splitRight,[status(thm)],[c_6996])).

tff(c_7496,plain,(
    ! [D_13,A_10,B_11,C_12] :
      ( D_13 = '#skF_8'
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7493])).

tff(c_7526,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7496])).

tff(c_7528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5200,c_7526])).

tff(c_7530,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5528])).

tff(c_5277,plain,(
    ! [D_444,A_441,B_442,C_443] :
      ( k1_xboole_0 = D_444
      | k3_zfmisc_1(A_441,B_442,C_443) = k1_xboole_0
      | k4_zfmisc_1(A_441,B_442,C_443,D_444) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5268,c_2])).

tff(c_7535,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7530,c_5277])).

tff(c_7540,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_7535])).

tff(c_7551,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7540,c_16])).

tff(c_7561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_7551])).

tff(c_7562,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5189])).

tff(c_7568,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7562])).

tff(c_7563,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5189])).

tff(c_7616,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7563,c_5195])).

tff(c_7769,plain,(
    ! [D_679,B_680,A_681,C_682] :
      ( D_679 = B_680
      | k1_xboole_0 = B_680
      | k1_xboole_0 = A_681
      | k2_zfmisc_1(C_682,D_679) != k2_zfmisc_1(A_681,B_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8343,plain,(
    ! [C_749,B_750,C_753,A_751,D_752,D_748] :
      ( D_752 = D_748
      | k1_xboole_0 = D_752
      | k3_zfmisc_1(A_751,B_750,C_753) = k1_xboole_0
      | k4_zfmisc_1(A_751,B_750,C_753,D_752) != k2_zfmisc_1(C_749,D_748) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7769])).

tff(c_8367,plain,(
    ! [D_748,C_749] :
      ( D_748 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_749,D_748) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7616,c_8343])).

tff(c_8383,plain,(
    ! [D_748,C_749] :
      ( D_748 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_749,D_748) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_8367])).

tff(c_8384,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8383])).

tff(c_8412,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8384,c_16])).

tff(c_8423,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8412])).

tff(c_8426,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8423])).

tff(c_7621,plain,(
    ! [A_657,B_658,C_659,D_660] : k2_zfmisc_1(k3_zfmisc_1(A_657,B_658,C_659),D_660) = k4_zfmisc_1(A_657,B_658,C_659,D_660) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7909,plain,(
    ! [D_696,A_697,B_698,C_699] :
      ( k1_xboole_0 = D_696
      | k3_zfmisc_1(A_697,B_698,C_699) = k1_xboole_0
      | k4_zfmisc_1(A_697,B_698,C_699,D_696) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7621,c_2])).

tff(c_7924,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7616,c_7909])).

tff(c_7933,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_7924])).

tff(c_7934,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7933])).

tff(c_8435,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8426,c_7934])).

tff(c_8415,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_8384,c_14])).

tff(c_8424,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8415])).

tff(c_8715,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8426,c_8424])).

tff(c_8716,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8715,c_7616])).

tff(c_8718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8435,c_8716])).

tff(c_8719,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8423])).

tff(c_8729,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8719,c_7934])).

tff(c_9008,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8719,c_8424])).

tff(c_9009,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9008,c_7616])).

tff(c_9215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8729,c_9009])).

tff(c_9217,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8383])).

tff(c_7800,plain,(
    ! [C_683,A_684,B_685,D_686] :
      ( C_683 = A_684
      | k1_xboole_0 = B_685
      | k1_xboole_0 = A_684
      | k2_zfmisc_1(C_683,D_686) != k2_zfmisc_1(A_684,B_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9352,plain,(
    ! [D_835,A_834,C_831,B_832,D_833,C_836] :
      ( k3_zfmisc_1(A_834,B_832,C_836) = C_831
      | k1_xboole_0 = D_835
      | k3_zfmisc_1(A_834,B_832,C_836) = k1_xboole_0
      | k4_zfmisc_1(A_834,B_832,C_836,D_835) != k2_zfmisc_1(C_831,D_833) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7800])).

tff(c_9376,plain,(
    ! [C_831,D_833] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_831
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_831,D_833) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7616,c_9352])).

tff(c_9393,plain,(
    ! [C_837,D_838] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_837
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_837,D_838) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9217,c_26,c_9376])).

tff(c_9396,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_9393])).

tff(c_9431,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9396])).

tff(c_7781,plain,(
    ! [A_7,B_8,C_682,C_9,D_679] :
      ( D_679 = C_9
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_682,D_679) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7769])).

tff(c_9486,plain,(
    ! [D_679,C_682] :
      ( D_679 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_682,D_679) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9431,c_7781])).

tff(c_9701,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9486])).

tff(c_9727,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9701,c_2])).

tff(c_9737,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_9727])).

tff(c_9467,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9431,c_9217])).

tff(c_9745,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9737,c_9467])).

tff(c_9724,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_1','#skF_6',C_9) = k2_zfmisc_1(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_9701,c_12])).

tff(c_9734,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_1','#skF_6',C_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9724])).

tff(c_9867,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_1','#skF_6',C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9737,c_9734])).

tff(c_9868,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9867,c_9431])).

tff(c_10047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9745,c_9868])).

tff(c_10049,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9486])).

tff(c_10048,plain,(
    ! [D_679,C_682] :
      ( k1_xboole_0 = '#skF_7'
      | D_679 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_682,D_679) ) ),
    inference(splitRight,[status(thm)],[c_9486])).

tff(c_10050,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_10048])).

tff(c_10058,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10050,c_9467])).

tff(c_10082,plain,(
    ! [A_14,B_15] : k3_zfmisc_1(A_14,B_15,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10050,c_10050,c_18])).

tff(c_10240,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10082,c_9431])).

tff(c_10300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10058,c_10240])).

tff(c_10344,plain,(
    ! [D_896,C_897] :
      ( D_896 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_897,D_896) ) ),
    inference(splitRight,[status(thm)],[c_10048])).

tff(c_10350,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_7'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10344])).

tff(c_10360,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10350])).

tff(c_10387,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10360,c_9431])).

tff(c_7812,plain,(
    ! [A_7,C_683,D_686,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = C_683
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_683,D_686) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7800])).

tff(c_10395,plain,(
    ! [C_683,D_686] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = C_683
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_683,D_686) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10387,c_7812])).

tff(c_10561,plain,(
    ! [C_911,D_912] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = C_911
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_911,D_912) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10049,c_28,c_10395])).

tff(c_10567,plain,(
    ! [A_7,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = k2_zfmisc_1('#skF_1','#skF_6')
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10561])).

tff(c_10593,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10567])).

tff(c_10642,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10593,c_8])).

tff(c_10654,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_10642])).

tff(c_10871,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10654])).

tff(c_10623,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10593,c_10049])).

tff(c_10875,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10871,c_10623])).

tff(c_10909,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10871,c_10871,c_4])).

tff(c_10968,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10909,c_10593])).

tff(c_11021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10875,c_10968])).

tff(c_11022,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_6'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_10654])).

tff(c_11026,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11022])).

tff(c_11028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7568,c_11026])).

tff(c_11029,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7933])).

tff(c_11040,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11029,c_16])).

tff(c_11049,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_11040])).

tff(c_11052,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11049])).

tff(c_11141,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11052,c_26])).

tff(c_11139,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11052,c_11052,c_4])).

tff(c_11143,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11052,c_32])).

tff(c_11142,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11052,c_28])).

tff(c_11030,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7933])).

tff(c_11325,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11052,c_11030])).

tff(c_7775,plain,(
    ! [B_11,A_10,C_12,D_13,C_682,D_679] :
      ( D_679 = D_13
      | k1_xboole_0 = D_13
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k2_zfmisc_1(C_682,D_679) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7769])).

tff(c_11726,plain,(
    ! [C_1008,C_1012,A_1010,D_1011,B_1009,D_1007] :
      ( D_1011 = D_1007
      | D_1011 = '#skF_6'
      | k3_zfmisc_1(A_1010,B_1009,C_1012) = '#skF_6'
      | k4_zfmisc_1(A_1010,B_1009,C_1012,D_1011) != k2_zfmisc_1(C_1008,D_1007) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11052,c_11052,c_7775])).

tff(c_11741,plain,(
    ! [D_1007,C_1008] :
      ( D_1007 = '#skF_4'
      | '#skF_6' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_1008,D_1007) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11325,c_11726])).

tff(c_11758,plain,(
    ! [D_1007,C_1008] :
      ( D_1007 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_1008,D_1007) != '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_11141,c_11741])).

tff(c_11759,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11758])).

tff(c_11132,plain,(
    ! [A_14,B_15,C_16] :
      ( k3_zfmisc_1(A_14,B_15,C_16) != '#skF_6'
      | C_16 = '#skF_6'
      | B_15 = '#skF_6'
      | A_14 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11052,c_11052,c_11052,c_11052,c_16])).

tff(c_11766,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11759,c_11132])).

tff(c_11790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11143,c_7568,c_11142,c_11766])).

tff(c_11793,plain,(
    ! [D_1013,C_1014] :
      ( D_1013 = '#skF_4'
      | k2_zfmisc_1(C_1014,D_1013) != '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_11758])).

tff(c_11796,plain,(
    '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11139,c_11793])).

tff(c_11809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11141,c_11796])).

tff(c_11810,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_11049])).

tff(c_11830,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_26])).

tff(c_11828,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_11810,c_4])).

tff(c_11832,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_32])).

tff(c_11829,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_30])).

tff(c_11831,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_28])).

tff(c_11908,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_11030])).

tff(c_12338,plain,(
    ! [B_1071,A_1072,D_1069,C_1070,C_1074,D_1073] :
      ( D_1073 = D_1069
      | D_1073 = '#skF_7'
      | k3_zfmisc_1(A_1072,B_1071,C_1074) = '#skF_7'
      | k4_zfmisc_1(A_1072,B_1071,C_1074,D_1073) != k2_zfmisc_1(C_1070,D_1069) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_11810,c_7775])).

tff(c_12353,plain,(
    ! [D_1069,C_1070] :
      ( D_1069 = '#skF_4'
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_1070,D_1069) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11908,c_12338])).

tff(c_12370,plain,(
    ! [D_1069,C_1070] :
      ( D_1069 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_1070,D_1069) != '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_11830,c_12353])).

tff(c_12417,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_12370])).

tff(c_11821,plain,(
    ! [A_14,B_15,C_16] :
      ( k3_zfmisc_1(A_14,B_15,C_16) != '#skF_7'
      | C_16 = '#skF_7'
      | B_15 = '#skF_7'
      | A_14 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11810,c_11810,c_11810,c_11810,c_16])).

tff(c_12424,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12417,c_11821])).

tff(c_12445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11832,c_11829,c_11831,c_12424])).

tff(c_12448,plain,(
    ! [D_1081,C_1082] :
      ( D_1081 = '#skF_4'
      | k2_zfmisc_1(C_1082,D_1081) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_12370])).

tff(c_12454,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11828,c_12448])).

tff(c_12465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11830,c_12454])).

tff(c_12466,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7562])).

tff(c_12467,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7562])).

tff(c_12519,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12467,c_7563,c_5195])).

tff(c_12656,plain,(
    ! [D_1107,B_1108,A_1109,C_1110] :
      ( D_1107 = B_1108
      | k1_xboole_0 = B_1108
      | k1_xboole_0 = A_1109
      | k2_zfmisc_1(C_1110,D_1107) != k2_zfmisc_1(A_1109,B_1108) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13203,plain,(
    ! [C_1178,D_1176,B_1173,C_1177,D_1174,A_1175] :
      ( D_1176 = D_1174
      | k1_xboole_0 = D_1176
      | k3_zfmisc_1(A_1175,B_1173,C_1178) = k1_xboole_0
      | k4_zfmisc_1(A_1175,B_1173,C_1178,D_1176) != k2_zfmisc_1(C_1177,D_1174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_12656])).

tff(c_13227,plain,(
    ! [D_1174,C_1177] :
      ( D_1174 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1177,D_1174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12519,c_13203])).

tff(c_13243,plain,(
    ! [D_1174,C_1177] :
      ( D_1174 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1177,D_1174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_13227])).

tff(c_13244,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13243])).

tff(c_13272,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13244,c_16])).

tff(c_13283,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_13272])).

tff(c_13275,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_13244,c_14])).

tff(c_13284,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13275])).

tff(c_13519,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13283,c_13284])).

tff(c_13520,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13519,c_12519])).

tff(c_12524,plain,(
    ! [A_1088,B_1089,C_1090,D_1091] : k2_zfmisc_1(k3_zfmisc_1(A_1088,B_1089,C_1090),D_1091) = k4_zfmisc_1(A_1088,B_1089,C_1090,D_1091) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12785,plain,(
    ! [D_1122,A_1123,B_1124,C_1125] :
      ( k1_xboole_0 = D_1122
      | k3_zfmisc_1(A_1123,B_1124,C_1125) = k1_xboole_0
      | k4_zfmisc_1(A_1123,B_1124,C_1125,D_1122) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12524,c_2])).

tff(c_12800,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12519,c_12785])).

tff(c_12809,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_12800])).

tff(c_12810,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12809])).

tff(c_13294,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13283,c_12810])).

tff(c_13676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13520,c_13294])).

tff(c_13678,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13243])).

tff(c_12703,plain,(
    ! [C_1114,A_1115,B_1116,D_1117] :
      ( C_1114 = A_1115
      | k1_xboole_0 = B_1116
      | k1_xboole_0 = A_1115
      | k2_zfmisc_1(C_1114,D_1117) != k2_zfmisc_1(A_1115,B_1116) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13897,plain,(
    ! [C_1245,A_1243,D_1240,B_1241,D_1244,C_1242] :
      ( k3_zfmisc_1(A_1243,B_1241,C_1245) = C_1242
      | k1_xboole_0 = D_1244
      | k3_zfmisc_1(A_1243,B_1241,C_1245) = k1_xboole_0
      | k4_zfmisc_1(A_1243,B_1241,C_1245,D_1244) != k2_zfmisc_1(C_1242,D_1240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_12703])).

tff(c_13921,plain,(
    ! [C_1242,D_1240] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = C_1242
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1242,D_1240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12519,c_13897])).

tff(c_13945,plain,(
    ! [C_1247,D_1248] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = C_1247
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1247,D_1248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13678,c_26,c_13921])).

tff(c_13948,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_13945])).

tff(c_13983,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13948])).

tff(c_12668,plain,(
    ! [D_1107,C_1110,A_7,B_8,C_9] :
      ( D_1107 = C_9
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_1110,D_1107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12656])).

tff(c_14038,plain,(
    ! [D_1107,C_1110] :
      ( D_1107 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_1110,D_1107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13983,c_12668])).

tff(c_14237,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14038])).

tff(c_14262,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14237,c_2])).

tff(c_14273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_14262])).

tff(c_14274,plain,(
    ! [D_1107,C_1110] :
      ( k1_xboole_0 = '#skF_7'
      | D_1107 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_1110,D_1107) ) ),
    inference(splitRight,[status(thm)],[c_14038])).

tff(c_14298,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_14274])).

tff(c_14019,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13983,c_13678])).

tff(c_14306,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14298,c_14019])).

tff(c_14332,plain,(
    ! [A_14,B_15] : k3_zfmisc_1(A_14,B_15,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14298,c_14298,c_18])).

tff(c_14514,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14332,c_13983])).

tff(c_14578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14306,c_14514])).

tff(c_14581,plain,(
    ! [D_1294,C_1295] :
      ( D_1294 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_1295,D_1294) ) ),
    inference(splitRight,[status(thm)],[c_14274])).

tff(c_14587,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_7'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_14581])).

tff(c_14597,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_14587])).

tff(c_14599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12466,c_14597])).

tff(c_14600,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12809])).

tff(c_14608,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14600,c_16])).

tff(c_14617,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_14608])).

tff(c_14637,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_26])).

tff(c_14635,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_14617,c_4])).

tff(c_14639,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_32])).

tff(c_14636,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_30])).

tff(c_14601,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12809])).

tff(c_14715,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_14601])).

tff(c_12662,plain,(
    ! [D_1107,B_11,A_10,C_12,C_1110,D_13] :
      ( D_13 = D_1107
      | k1_xboole_0 = D_13
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k2_zfmisc_1(C_1110,D_1107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_12656])).

tff(c_15154,plain,(
    ! [D_1354,C_1355,B_1351,A_1353,D_1352,C_1356] :
      ( D_1354 = D_1352
      | D_1354 = '#skF_7'
      | k3_zfmisc_1(A_1353,B_1351,C_1356) = '#skF_7'
      | k4_zfmisc_1(A_1353,B_1351,C_1356,D_1354) != k2_zfmisc_1(C_1355,D_1352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_14617,c_12662])).

tff(c_15169,plain,(
    ! [D_1352,C_1355] :
      ( D_1352 = '#skF_4'
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_1355,D_1352) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14715,c_15154])).

tff(c_15186,plain,(
    ! [D_1352,C_1355] :
      ( D_1352 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_1355,D_1352) != '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_14637,c_15169])).

tff(c_15187,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_15186])).

tff(c_14620,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_14600])).

tff(c_12665,plain,(
    ! [A_1109,A_7,B_8,C_9,B_1108] :
      ( C_9 = B_1108
      | k1_xboole_0 = B_1108
      | k1_xboole_0 = A_1109
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(A_1109,B_1108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12656])).

tff(c_14644,plain,(
    ! [A_1109,A_7,B_8,C_9,B_1108] :
      ( C_9 = B_1108
      | B_1108 = '#skF_7'
      | A_1109 = '#skF_7'
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(A_1109,B_1108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_14617,c_12665])).

tff(c_15054,plain,(
    ! [B_1339,A_1340] :
      ( B_1339 = '#skF_7'
      | B_1339 = '#skF_7'
      | A_1340 = '#skF_7'
      | k2_zfmisc_1(A_1340,B_1339) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14620,c_14644])).

tff(c_15066,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_7'
      | C_9 = '#skF_7'
      | k2_zfmisc_1(A_7,B_8) = '#skF_7'
      | k3_zfmisc_1(A_7,B_8,C_9) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_15054])).

tff(c_15191,plain,
    ( '#skF_7' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_15187,c_15066])).

tff(c_15211,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_12466,c_12466,c_15191])).

tff(c_14630,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_7'
      | A_1 = '#skF_7'
      | k2_zfmisc_1(A_1,B_2) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_14617,c_14617,c_2])).

tff(c_15219,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15211,c_14630])).

tff(c_15231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14639,c_14636,c_15219])).

tff(c_15234,plain,(
    ! [D_1357,C_1358] :
      ( D_1357 = '#skF_4'
      | k2_zfmisc_1(C_1358,D_1357) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_15186])).

tff(c_15237,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14635,c_15234])).

tff(c_15250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14637,c_15237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.16/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.32/2.89  
% 8.32/2.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.32/2.89  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 8.32/2.89  
% 8.32/2.89  %Foreground sorts:
% 8.32/2.89  
% 8.32/2.89  
% 8.32/2.89  %Background operators:
% 8.32/2.89  
% 8.32/2.89  
% 8.32/2.89  %Foreground operators:
% 8.32/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.32/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.32/2.89  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 8.32/2.89  tff('#skF_7', type, '#skF_7': $i).
% 8.32/2.89  tff('#skF_5', type, '#skF_5': $i).
% 8.32/2.89  tff('#skF_6', type, '#skF_6': $i).
% 8.32/2.89  tff('#skF_2', type, '#skF_2': $i).
% 8.32/2.89  tff('#skF_3', type, '#skF_3': $i).
% 8.32/2.89  tff('#skF_1', type, '#skF_1': $i).
% 8.32/2.89  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.32/2.89  tff('#skF_8', type, '#skF_8': $i).
% 8.32/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.32/2.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.32/2.89  tff('#skF_4', type, '#skF_4': $i).
% 8.32/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.32/2.89  
% 8.51/2.93  tff(f_76, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 8.51/2.93  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.51/2.93  tff(f_45, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 8.51/2.93  tff(f_41, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 8.51/2.93  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.51/2.93  tff(f_57, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 8.51/2.93  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/2.93  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/2.93  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/2.93  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/2.93  tff(c_24, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/2.93  tff(c_102, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_24])).
% 8.51/2.93  tff(c_12, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.51/2.93  tff(c_14, plain, (![A_10, B_11, C_12, D_13]: (k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), D_13)=k4_zfmisc_1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/2.93  tff(c_34, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.51/2.93  tff(c_333, plain, (![D_56, B_57, A_58, C_59]: (D_56=B_57 | k1_xboole_0=B_57 | k1_xboole_0=A_58 | k2_zfmisc_1(C_59, D_56)!=k2_zfmisc_1(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_907, plain, (![B_126, D_127, C_130, A_128, D_129, C_131]: (D_129=D_127 | k1_xboole_0=D_129 | k3_zfmisc_1(A_128, B_126, C_130)=k1_xboole_0 | k4_zfmisc_1(A_128, B_126, C_130, D_129)!=k2_zfmisc_1(C_131, D_127))), inference(superposition, [status(thm), theory('equality')], [c_14, c_333])).
% 8.51/2.93  tff(c_931, plain, (![D_127, C_131]: (D_127='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_131, D_127))), inference(superposition, [status(thm), theory('equality')], [c_34, c_907])).
% 8.51/2.93  tff(c_993, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_931])).
% 8.51/2.93  tff(c_114, plain, (![A_27, B_28, C_29]: (k2_zfmisc_1(k2_zfmisc_1(A_27, B_28), C_29)=k3_zfmisc_1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.51/2.93  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.51/2.93  tff(c_123, plain, (![C_29, A_27, B_28]: (k1_xboole_0=C_29 | k2_zfmisc_1(A_27, B_28)=k1_xboole_0 | k3_zfmisc_1(A_27, B_28, C_29)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_114, c_2])).
% 8.51/2.93  tff(c_1033, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_993, c_123])).
% 8.51/2.93  tff(c_1037, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1033])).
% 8.51/2.93  tff(c_1068, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1037, c_2])).
% 8.51/2.93  tff(c_1070, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1068])).
% 8.51/2.93  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.51/2.93  tff(c_1028, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_993, c_14])).
% 8.51/2.93  tff(c_1035, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1028])).
% 8.51/2.93  tff(c_1357, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_1035])).
% 8.51/2.93  tff(c_1358, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_34])).
% 8.51/2.93  tff(c_154, plain, (![A_30, B_31, C_32, D_33]: (k2_zfmisc_1(k3_zfmisc_1(A_30, B_31, C_32), D_33)=k4_zfmisc_1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/2.93  tff(c_415, plain, (![D_64, A_65, B_66, C_67]: (k1_xboole_0=D_64 | k3_zfmisc_1(A_65, B_66, C_67)=k1_xboole_0 | k4_zfmisc_1(A_65, B_66, C_67, D_64)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154, c_2])).
% 8.51/2.93  tff(c_430, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_415])).
% 8.51/2.93  tff(c_466, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_430])).
% 8.51/2.93  tff(c_1125, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_466])).
% 8.51/2.93  tff(c_1551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1358, c_1125])).
% 8.51/2.93  tff(c_1552, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1068])).
% 8.51/2.93  tff(c_1880, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_1035])).
% 8.51/2.93  tff(c_1881, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1880, c_34])).
% 8.51/2.93  tff(c_1567, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_466])).
% 8.51/2.93  tff(c_1965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1567])).
% 8.51/2.93  tff(c_1966, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1033])).
% 8.51/2.93  tff(c_2249, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1966, c_1035])).
% 8.51/2.93  tff(c_2250, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2249, c_34])).
% 8.51/2.93  tff(c_1979, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1966, c_466])).
% 8.51/2.93  tff(c_2491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2250, c_1979])).
% 8.51/2.93  tff(c_2493, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_931])).
% 8.51/2.93  tff(c_467, plain, (![A_74, A_76, C_78, B_73, D_77, B_75]: (D_77=B_73 | k1_xboole_0=B_73 | k1_xboole_0=A_74 | k4_zfmisc_1(A_76, B_75, C_78, D_77)!=k2_zfmisc_1(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_14, c_333])).
% 8.51/2.93  tff(c_625, plain, (![B_89, A_90]: (B_89='#skF_8' | k1_xboole_0=B_89 | k1_xboole_0=A_90 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_34, c_467])).
% 8.51/2.93  tff(c_628, plain, (![D_13, A_10, B_11, C_12]: (D_13='#skF_8' | k1_xboole_0=D_13 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_625])).
% 8.51/2.93  tff(c_2943, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_628])).
% 8.51/2.93  tff(c_2944, plain, ('#skF_8'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_2943])).
% 8.51/2.93  tff(c_2977, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2944])).
% 8.51/2.93  tff(c_16, plain, (![A_14, B_15, C_16]: (k3_zfmisc_1(A_14, B_15, C_16)!=k1_xboole_0 | k1_xboole_0=C_16 | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.51/2.93  tff(c_3008, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2977, c_16])).
% 8.51/2.93  tff(c_3025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_3008])).
% 8.51/2.93  tff(c_3026, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_2944])).
% 8.51/2.93  tff(c_3032, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3026, c_34])).
% 8.51/2.93  tff(c_232, plain, (![C_43, A_44, B_45, D_46]: (C_43=A_44 | k1_xboole_0=B_45 | k1_xboole_0=A_44 | k2_zfmisc_1(C_43, D_46)!=k2_zfmisc_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_3059, plain, (![D_285, C_284, C_289, B_286, D_288, A_287]: (k3_zfmisc_1(A_287, B_286, C_289)=C_284 | k1_xboole_0=D_288 | k3_zfmisc_1(A_287, B_286, C_289)=k1_xboole_0 | k4_zfmisc_1(A_287, B_286, C_289, D_288)!=k2_zfmisc_1(C_284, D_285))), inference(superposition, [status(thm), theory('equality')], [c_14, c_232])).
% 8.51/2.93  tff(c_3062, plain, (![C_284, D_285]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=C_284 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_284, D_285))), inference(superposition, [status(thm), theory('equality')], [c_3032, c_3059])).
% 8.51/2.93  tff(c_3132, plain, (![C_295, D_296]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=C_295 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_295, D_296))), inference(negUnitSimplification, [status(thm)], [c_2493, c_26, c_3062])).
% 8.51/2.93  tff(c_3135, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3132])).
% 8.51/2.93  tff(c_3242, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_3135])).
% 8.51/2.93  tff(c_345, plain, (![D_56, A_7, B_8, C_9, C_59]: (D_56=C_9 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_59, D_56))), inference(superposition, [status(thm), theory('equality')], [c_12, c_333])).
% 8.51/2.93  tff(c_3297, plain, (![D_56, C_59]: (D_56='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_59, D_56))), inference(superposition, [status(thm), theory('equality')], [c_3242, c_345])).
% 8.51/2.93  tff(c_3553, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3297])).
% 8.51/2.93  tff(c_3584, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3553, c_2])).
% 8.51/2.93  tff(c_3586, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3584])).
% 8.51/2.93  tff(c_3027, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2944])).
% 8.51/2.93  tff(c_3598, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3586, c_3027])).
% 8.51/2.93  tff(c_3575, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)=k2_zfmisc_1(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_3553, c_12])).
% 8.51/2.93  tff(c_3583, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3575])).
% 8.51/2.93  tff(c_3723, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3586, c_3583])).
% 8.51/2.93  tff(c_3724, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3723, c_3242])).
% 8.51/2.93  tff(c_3726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3598, c_3724])).
% 8.51/2.93  tff(c_3727, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3584])).
% 8.51/2.93  tff(c_3740, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3727, c_3027])).
% 8.51/2.93  tff(c_3866, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3727, c_3583])).
% 8.51/2.93  tff(c_3867, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_3242])).
% 8.51/2.93  tff(c_3891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3740, c_3867])).
% 8.51/2.93  tff(c_3893, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3297])).
% 8.51/2.93  tff(c_3892, plain, (![D_56, C_59]: (k1_xboole_0='#skF_7' | D_56='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_59, D_56))), inference(splitRight, [status(thm)], [c_3297])).
% 8.51/2.93  tff(c_3894, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_3892])).
% 8.51/2.93  tff(c_3906, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3894, c_3027])).
% 8.51/2.93  tff(c_18, plain, (![A_14, B_15]: (k3_zfmisc_1(A_14, B_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.51/2.93  tff(c_3928, plain, (![A_14, B_15]: (k3_zfmisc_1(A_14, B_15, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3894, c_3894, c_18])).
% 8.51/2.93  tff(c_4130, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3928, c_3242])).
% 8.51/2.93  tff(c_4132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3906, c_4130])).
% 8.51/2.93  tff(c_4173, plain, (![D_386, C_387]: (D_386='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_387, D_386))), inference(splitRight, [status(thm)], [c_3892])).
% 8.51/2.93  tff(c_4179, plain, (![C_9, A_7, B_8]: (C_9='#skF_7' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4173])).
% 8.51/2.93  tff(c_4189, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_4179])).
% 8.51/2.93  tff(c_4216, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4189, c_3242])).
% 8.51/2.93  tff(c_244, plain, (![C_43, A_7, D_46, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=C_43 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_43, D_46))), inference(superposition, [status(thm), theory('equality')], [c_12, c_232])).
% 8.51/2.93  tff(c_4224, plain, (![C_43, D_46]: (k2_zfmisc_1('#skF_5', '#skF_6')=C_43 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_43, D_46))), inference(superposition, [status(thm), theory('equality')], [c_4216, c_244])).
% 8.51/2.93  tff(c_4395, plain, (![C_401, D_402]: (k2_zfmisc_1('#skF_5', '#skF_6')=C_401 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_401, D_402))), inference(negUnitSimplification, [status(thm)], [c_3893, c_28, c_4224])).
% 8.51/2.93  tff(c_4401, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=k2_zfmisc_1('#skF_5', '#skF_6') | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4395])).
% 8.51/2.93  tff(c_4457, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_4401])).
% 8.51/2.93  tff(c_8, plain, (![D_6, B_4, A_3, C_5]: (D_6=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_4497, plain, (![B_4, A_3]: (B_4='#skF_6' | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4457, c_8])).
% 8.51/2.93  tff(c_4739, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_4497])).
% 8.51/2.93  tff(c_4740, plain, ('#skF_6'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_4739])).
% 8.51/2.93  tff(c_4762, plain, (k2_zfmisc_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4740, c_4457])).
% 8.51/2.93  tff(c_4779, plain, (![D_6, C_5]: (D_6='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4762, c_8])).
% 8.51/2.93  tff(c_4796, plain, (![D_6, C_5]: (D_6='#skF_2' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_4779])).
% 8.51/2.93  tff(c_4967, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4796])).
% 8.51/2.93  tff(c_5007, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4967, c_4967, c_6])).
% 8.51/2.93  tff(c_5017, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5007, c_4762])).
% 8.51/2.93  tff(c_4487, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4457, c_3893])).
% 8.51/2.93  tff(c_4971, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4967, c_4487])).
% 8.51/2.93  tff(c_5119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5017, c_4971])).
% 8.51/2.93  tff(c_5121, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_4796])).
% 8.51/2.93  tff(c_10, plain, (![C_5, A_3, B_4, D_6]: (C_5=A_3 | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_4785, plain, (![C_5, D_6]: (C_5='#skF_5' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4762, c_10])).
% 8.51/2.93  tff(c_4797, plain, (![C_5, D_6]: (C_5='#skF_5' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_4785])).
% 8.51/2.93  tff(c_5122, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4797])).
% 8.51/2.93  tff(c_5123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5121, c_5122])).
% 8.51/2.93  tff(c_5124, plain, (![C_5, D_6]: (C_5='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_4797])).
% 8.51/2.93  tff(c_5151, plain, ('#skF_5'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_5124])).
% 8.51/2.93  tff(c_5153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_5151])).
% 8.51/2.93  tff(c_5155, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_430])).
% 8.51/2.93  tff(c_163, plain, (![D_33, A_30, B_31, C_32]: (k1_xboole_0=D_33 | k3_zfmisc_1(A_30, B_31, C_32)=k1_xboole_0 | k4_zfmisc_1(A_30, B_31, C_32, D_33)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154, c_2])).
% 8.51/2.93  tff(c_5160, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5155, c_163])).
% 8.51/2.93  tff(c_5165, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_5160])).
% 8.51/2.93  tff(c_5176, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5165, c_16])).
% 8.51/2.93  tff(c_5188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_5176])).
% 8.51/2.93  tff(c_5189, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 8.51/2.93  tff(c_5200, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_5189])).
% 8.51/2.93  tff(c_5190, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 8.51/2.93  tff(c_5195, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5190, c_34])).
% 8.51/2.93  tff(c_5314, plain, (![D_448, B_449, A_450, C_451]: (D_448=B_449 | k1_xboole_0=B_449 | k1_xboole_0=A_450 | k2_zfmisc_1(C_451, D_448)!=k2_zfmisc_1(A_450, B_449))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_5942, plain, (![D_529, B_526, D_525, A_527, C_528, C_530]: (D_529=D_525 | k1_xboole_0=D_529 | k3_zfmisc_1(A_527, B_526, C_530)=k1_xboole_0 | k4_zfmisc_1(A_527, B_526, C_530, D_529)!=k2_zfmisc_1(C_528, D_525))), inference(superposition, [status(thm), theory('equality')], [c_14, c_5314])).
% 8.51/2.93  tff(c_5966, plain, (![D_525, C_528]: (D_525='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_528, D_525))), inference(superposition, [status(thm), theory('equality')], [c_5195, c_5942])).
% 8.51/2.93  tff(c_6025, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5966])).
% 8.51/2.93  tff(c_6056, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6025, c_16])).
% 8.51/2.93  tff(c_6065, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_32, c_6056])).
% 8.51/2.93  tff(c_6067, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_6065])).
% 8.51/2.93  tff(c_6053, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_6025, c_14])).
% 8.51/2.93  tff(c_6062, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6053])).
% 8.51/2.93  tff(c_6369, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6067, c_6062])).
% 8.51/2.93  tff(c_6370, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6369, c_5195])).
% 8.51/2.93  tff(c_5268, plain, (![A_441, B_442, C_443, D_444]: (k2_zfmisc_1(k3_zfmisc_1(A_441, B_442, C_443), D_444)=k4_zfmisc_1(A_441, B_442, C_443, D_444))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/2.93  tff(c_5513, plain, (![D_472, A_473, B_474, C_475]: (k1_xboole_0=D_472 | k3_zfmisc_1(A_473, B_474, C_475)=k1_xboole_0 | k4_zfmisc_1(A_473, B_474, C_475, D_472)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5268, c_2])).
% 8.51/2.93  tff(c_5528, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5195, c_5513])).
% 8.51/2.93  tff(c_5537, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5528])).
% 8.51/2.93  tff(c_6078, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6067, c_5537])).
% 8.51/2.93  tff(c_6618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6370, c_6078])).
% 8.51/2.93  tff(c_6619, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6065])).
% 8.51/2.93  tff(c_6631, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6619, c_5537])).
% 8.51/2.93  tff(c_6942, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6619, c_6062])).
% 8.51/2.93  tff(c_6943, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6942, c_5195])).
% 8.51/2.93  tff(c_6995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6631, c_6943])).
% 8.51/2.93  tff(c_6996, plain, (![D_525, C_528]: (k1_xboole_0='#skF_8' | D_525='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_528, D_525))), inference(splitRight, [status(thm)], [c_5966])).
% 8.51/2.93  tff(c_7012, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_6996])).
% 8.51/2.93  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.51/2.93  tff(c_5281, plain, (![A_441, B_442, C_443]: (k4_zfmisc_1(A_441, B_442, C_443, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5268, c_4])).
% 8.51/2.93  tff(c_7032, plain, (![A_441, B_442, C_443]: (k4_zfmisc_1(A_441, B_442, C_443, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7012, c_7012, c_5281])).
% 8.51/2.93  tff(c_7296, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7032, c_5195])).
% 8.51/2.93  tff(c_7024, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7012, c_5537])).
% 8.51/2.93  tff(c_7457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7296, c_7024])).
% 8.51/2.93  tff(c_7493, plain, (![D_647, C_648]: (D_647='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_648, D_647))), inference(splitRight, [status(thm)], [c_6996])).
% 8.51/2.93  tff(c_7496, plain, (![D_13, A_10, B_11, C_12]: (D_13='#skF_8' | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7493])).
% 8.51/2.93  tff(c_7526, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_7496])).
% 8.51/2.93  tff(c_7528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5200, c_7526])).
% 8.51/2.93  tff(c_7530, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5528])).
% 8.51/2.93  tff(c_5277, plain, (![D_444, A_441, B_442, C_443]: (k1_xboole_0=D_444 | k3_zfmisc_1(A_441, B_442, C_443)=k1_xboole_0 | k4_zfmisc_1(A_441, B_442, C_443, D_444)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5268, c_2])).
% 8.51/2.93  tff(c_7535, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7530, c_5277])).
% 8.51/2.93  tff(c_7540, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_7535])).
% 8.51/2.93  tff(c_7551, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7540, c_16])).
% 8.51/2.93  tff(c_7561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_7551])).
% 8.51/2.93  tff(c_7562, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_5189])).
% 8.51/2.93  tff(c_7568, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_7562])).
% 8.51/2.93  tff(c_7563, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_5189])).
% 8.51/2.93  tff(c_7616, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7563, c_5195])).
% 8.51/2.93  tff(c_7769, plain, (![D_679, B_680, A_681, C_682]: (D_679=B_680 | k1_xboole_0=B_680 | k1_xboole_0=A_681 | k2_zfmisc_1(C_682, D_679)!=k2_zfmisc_1(A_681, B_680))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_8343, plain, (![C_749, B_750, C_753, A_751, D_752, D_748]: (D_752=D_748 | k1_xboole_0=D_752 | k3_zfmisc_1(A_751, B_750, C_753)=k1_xboole_0 | k4_zfmisc_1(A_751, B_750, C_753, D_752)!=k2_zfmisc_1(C_749, D_748))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7769])).
% 8.51/2.93  tff(c_8367, plain, (![D_748, C_749]: (D_748='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_749, D_748))), inference(superposition, [status(thm), theory('equality')], [c_7616, c_8343])).
% 8.51/2.93  tff(c_8383, plain, (![D_748, C_749]: (D_748='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_749, D_748))), inference(negUnitSimplification, [status(thm)], [c_26, c_8367])).
% 8.51/2.93  tff(c_8384, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8383])).
% 8.51/2.93  tff(c_8412, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8384, c_16])).
% 8.51/2.93  tff(c_8423, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_32, c_8412])).
% 8.51/2.93  tff(c_8426, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_8423])).
% 8.51/2.93  tff(c_7621, plain, (![A_657, B_658, C_659, D_660]: (k2_zfmisc_1(k3_zfmisc_1(A_657, B_658, C_659), D_660)=k4_zfmisc_1(A_657, B_658, C_659, D_660))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/2.93  tff(c_7909, plain, (![D_696, A_697, B_698, C_699]: (k1_xboole_0=D_696 | k3_zfmisc_1(A_697, B_698, C_699)=k1_xboole_0 | k4_zfmisc_1(A_697, B_698, C_699, D_696)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7621, c_2])).
% 8.51/2.93  tff(c_7924, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7616, c_7909])).
% 8.51/2.93  tff(c_7933, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_7924])).
% 8.51/2.93  tff(c_7934, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7933])).
% 8.51/2.93  tff(c_8435, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8426, c_7934])).
% 8.51/2.93  tff(c_8415, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_8384, c_14])).
% 8.51/2.93  tff(c_8424, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8415])).
% 8.51/2.93  tff(c_8715, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8426, c_8424])).
% 8.51/2.93  tff(c_8716, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8715, c_7616])).
% 8.51/2.93  tff(c_8718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8435, c_8716])).
% 8.51/2.93  tff(c_8719, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_8423])).
% 8.51/2.93  tff(c_8729, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8719, c_7934])).
% 8.51/2.93  tff(c_9008, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8719, c_8424])).
% 8.51/2.93  tff(c_9009, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_9008, c_7616])).
% 8.51/2.93  tff(c_9215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8729, c_9009])).
% 8.51/2.93  tff(c_9217, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8383])).
% 8.51/2.93  tff(c_7800, plain, (![C_683, A_684, B_685, D_686]: (C_683=A_684 | k1_xboole_0=B_685 | k1_xboole_0=A_684 | k2_zfmisc_1(C_683, D_686)!=k2_zfmisc_1(A_684, B_685))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_9352, plain, (![D_835, A_834, C_831, B_832, D_833, C_836]: (k3_zfmisc_1(A_834, B_832, C_836)=C_831 | k1_xboole_0=D_835 | k3_zfmisc_1(A_834, B_832, C_836)=k1_xboole_0 | k4_zfmisc_1(A_834, B_832, C_836, D_835)!=k2_zfmisc_1(C_831, D_833))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7800])).
% 8.51/2.93  tff(c_9376, plain, (![C_831, D_833]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_831 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_831, D_833))), inference(superposition, [status(thm), theory('equality')], [c_7616, c_9352])).
% 8.51/2.93  tff(c_9393, plain, (![C_837, D_838]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_837 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_837, D_838))), inference(negUnitSimplification, [status(thm)], [c_9217, c_26, c_9376])).
% 8.51/2.93  tff(c_9396, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_9393])).
% 8.51/2.93  tff(c_9431, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_9396])).
% 8.51/2.93  tff(c_7781, plain, (![A_7, B_8, C_682, C_9, D_679]: (D_679=C_9 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_682, D_679))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7769])).
% 8.51/2.93  tff(c_9486, plain, (![D_679, C_682]: (D_679='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_682, D_679))), inference(superposition, [status(thm), theory('equality')], [c_9431, c_7781])).
% 8.51/2.93  tff(c_9701, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9486])).
% 8.51/2.93  tff(c_9727, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9701, c_2])).
% 8.51/2.93  tff(c_9737, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_32, c_9727])).
% 8.51/2.93  tff(c_9467, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9431, c_9217])).
% 8.51/2.93  tff(c_9745, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9737, c_9467])).
% 8.51/2.93  tff(c_9724, plain, (![C_9]: (k3_zfmisc_1('#skF_1', '#skF_6', C_9)=k2_zfmisc_1(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_9701, c_12])).
% 8.51/2.93  tff(c_9734, plain, (![C_9]: (k3_zfmisc_1('#skF_1', '#skF_6', C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9724])).
% 8.51/2.93  tff(c_9867, plain, (![C_9]: (k3_zfmisc_1('#skF_1', '#skF_6', C_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9737, c_9734])).
% 8.51/2.93  tff(c_9868, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9867, c_9431])).
% 8.51/2.93  tff(c_10047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9745, c_9868])).
% 8.51/2.93  tff(c_10049, plain, (k2_zfmisc_1('#skF_1', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_9486])).
% 8.51/2.93  tff(c_10048, plain, (![D_679, C_682]: (k1_xboole_0='#skF_7' | D_679='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_682, D_679))), inference(splitRight, [status(thm)], [c_9486])).
% 8.51/2.93  tff(c_10050, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_10048])).
% 8.51/2.93  tff(c_10058, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10050, c_9467])).
% 8.51/2.93  tff(c_10082, plain, (![A_14, B_15]: (k3_zfmisc_1(A_14, B_15, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10050, c_10050, c_18])).
% 8.51/2.93  tff(c_10240, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10082, c_9431])).
% 8.51/2.93  tff(c_10300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10058, c_10240])).
% 8.51/2.93  tff(c_10344, plain, (![D_896, C_897]: (D_896='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_897, D_896))), inference(splitRight, [status(thm)], [c_10048])).
% 8.51/2.93  tff(c_10350, plain, (![C_9, A_7, B_8]: (C_9='#skF_7' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_10344])).
% 8.51/2.93  tff(c_10360, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_10350])).
% 8.51/2.93  tff(c_10387, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10360, c_9431])).
% 8.51/2.93  tff(c_7812, plain, (![A_7, C_683, D_686, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=C_683 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_683, D_686))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7800])).
% 8.51/2.93  tff(c_10395, plain, (![C_683, D_686]: (k2_zfmisc_1('#skF_1', '#skF_6')=C_683 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_683, D_686))), inference(superposition, [status(thm), theory('equality')], [c_10387, c_7812])).
% 8.51/2.93  tff(c_10561, plain, (![C_911, D_912]: (k2_zfmisc_1('#skF_1', '#skF_6')=C_911 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_911, D_912))), inference(negUnitSimplification, [status(thm)], [c_10049, c_28, c_10395])).
% 8.51/2.93  tff(c_10567, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=k2_zfmisc_1('#skF_1', '#skF_6') | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_10561])).
% 8.51/2.93  tff(c_10593, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_10567])).
% 8.51/2.93  tff(c_10642, plain, (![D_6, C_5]: (D_6='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10593, c_8])).
% 8.51/2.93  tff(c_10654, plain, (![D_6, C_5]: (D_6='#skF_6' | k1_xboole_0='#skF_6' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_10642])).
% 8.51/2.93  tff(c_10871, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_10654])).
% 8.51/2.93  tff(c_10623, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10593, c_10049])).
% 8.51/2.93  tff(c_10875, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10871, c_10623])).
% 8.51/2.93  tff(c_10909, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10871, c_10871, c_4])).
% 8.51/2.93  tff(c_10968, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10909, c_10593])).
% 8.51/2.93  tff(c_11021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10875, c_10968])).
% 8.51/2.93  tff(c_11022, plain, (![D_6, C_5]: (D_6='#skF_6' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_10654])).
% 8.51/2.93  tff(c_11026, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_11022])).
% 8.51/2.93  tff(c_11028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7568, c_11026])).
% 8.51/2.93  tff(c_11029, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7933])).
% 8.51/2.93  tff(c_11040, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11029, c_16])).
% 8.51/2.93  tff(c_11049, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_32, c_11040])).
% 8.51/2.93  tff(c_11052, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_11049])).
% 8.51/2.93  tff(c_11141, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11052, c_26])).
% 8.51/2.93  tff(c_11139, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11052, c_11052, c_4])).
% 8.51/2.93  tff(c_11143, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11052, c_32])).
% 8.51/2.93  tff(c_11142, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11052, c_28])).
% 8.51/2.93  tff(c_11030, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7933])).
% 8.51/2.93  tff(c_11325, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11052, c_11030])).
% 8.51/2.93  tff(c_7775, plain, (![B_11, A_10, C_12, D_13, C_682, D_679]: (D_679=D_13 | k1_xboole_0=D_13 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k2_zfmisc_1(C_682, D_679))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7769])).
% 8.51/2.93  tff(c_11726, plain, (![C_1008, C_1012, A_1010, D_1011, B_1009, D_1007]: (D_1011=D_1007 | D_1011='#skF_6' | k3_zfmisc_1(A_1010, B_1009, C_1012)='#skF_6' | k4_zfmisc_1(A_1010, B_1009, C_1012, D_1011)!=k2_zfmisc_1(C_1008, D_1007))), inference(demodulation, [status(thm), theory('equality')], [c_11052, c_11052, c_7775])).
% 8.51/2.93  tff(c_11741, plain, (![D_1007, C_1008]: (D_1007='#skF_4' | '#skF_6'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6' | k2_zfmisc_1(C_1008, D_1007)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11325, c_11726])).
% 8.51/2.93  tff(c_11758, plain, (![D_1007, C_1008]: (D_1007='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6' | k2_zfmisc_1(C_1008, D_1007)!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_11141, c_11741])).
% 8.51/2.93  tff(c_11759, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(splitLeft, [status(thm)], [c_11758])).
% 8.51/2.93  tff(c_11132, plain, (![A_14, B_15, C_16]: (k3_zfmisc_1(A_14, B_15, C_16)!='#skF_6' | C_16='#skF_6' | B_15='#skF_6' | A_14='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11052, c_11052, c_11052, c_11052, c_16])).
% 8.51/2.93  tff(c_11766, plain, ('#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11759, c_11132])).
% 8.51/2.93  tff(c_11790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11143, c_7568, c_11142, c_11766])).
% 8.51/2.93  tff(c_11793, plain, (![D_1013, C_1014]: (D_1013='#skF_4' | k2_zfmisc_1(C_1014, D_1013)!='#skF_6')), inference(splitRight, [status(thm)], [c_11758])).
% 8.51/2.93  tff(c_11796, plain, ('#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11139, c_11793])).
% 8.51/2.93  tff(c_11809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11141, c_11796])).
% 8.51/2.93  tff(c_11810, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_11049])).
% 8.51/2.93  tff(c_11830, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_26])).
% 8.51/2.93  tff(c_11828, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_11810, c_4])).
% 8.51/2.93  tff(c_11832, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_32])).
% 8.51/2.93  tff(c_11829, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_30])).
% 8.51/2.93  tff(c_11831, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_28])).
% 8.51/2.93  tff(c_11908, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_11030])).
% 8.51/2.93  tff(c_12338, plain, (![B_1071, A_1072, D_1069, C_1070, C_1074, D_1073]: (D_1073=D_1069 | D_1073='#skF_7' | k3_zfmisc_1(A_1072, B_1071, C_1074)='#skF_7' | k4_zfmisc_1(A_1072, B_1071, C_1074, D_1073)!=k2_zfmisc_1(C_1070, D_1069))), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_11810, c_7775])).
% 8.51/2.93  tff(c_12353, plain, (![D_1069, C_1070]: (D_1069='#skF_4' | '#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7' | k2_zfmisc_1(C_1070, D_1069)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_11908, c_12338])).
% 8.51/2.93  tff(c_12370, plain, (![D_1069, C_1070]: (D_1069='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7' | k2_zfmisc_1(C_1070, D_1069)!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_11830, c_12353])).
% 8.51/2.93  tff(c_12417, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(splitLeft, [status(thm)], [c_12370])).
% 8.51/2.93  tff(c_11821, plain, (![A_14, B_15, C_16]: (k3_zfmisc_1(A_14, B_15, C_16)!='#skF_7' | C_16='#skF_7' | B_15='#skF_7' | A_14='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11810, c_11810, c_11810, c_11810, c_16])).
% 8.51/2.93  tff(c_12424, plain, ('#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12417, c_11821])).
% 8.51/2.93  tff(c_12445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11832, c_11829, c_11831, c_12424])).
% 8.51/2.93  tff(c_12448, plain, (![D_1081, C_1082]: (D_1081='#skF_4' | k2_zfmisc_1(C_1082, D_1081)!='#skF_7')), inference(splitRight, [status(thm)], [c_12370])).
% 8.51/2.93  tff(c_12454, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11828, c_12448])).
% 8.51/2.93  tff(c_12465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11830, c_12454])).
% 8.51/2.93  tff(c_12466, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_7562])).
% 8.51/2.93  tff(c_12467, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_7562])).
% 8.51/2.93  tff(c_12519, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12467, c_7563, c_5195])).
% 8.51/2.93  tff(c_12656, plain, (![D_1107, B_1108, A_1109, C_1110]: (D_1107=B_1108 | k1_xboole_0=B_1108 | k1_xboole_0=A_1109 | k2_zfmisc_1(C_1110, D_1107)!=k2_zfmisc_1(A_1109, B_1108))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_13203, plain, (![C_1178, D_1176, B_1173, C_1177, D_1174, A_1175]: (D_1176=D_1174 | k1_xboole_0=D_1176 | k3_zfmisc_1(A_1175, B_1173, C_1178)=k1_xboole_0 | k4_zfmisc_1(A_1175, B_1173, C_1178, D_1176)!=k2_zfmisc_1(C_1177, D_1174))), inference(superposition, [status(thm), theory('equality')], [c_14, c_12656])).
% 8.51/2.93  tff(c_13227, plain, (![D_1174, C_1177]: (D_1174='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1177, D_1174))), inference(superposition, [status(thm), theory('equality')], [c_12519, c_13203])).
% 8.51/2.93  tff(c_13243, plain, (![D_1174, C_1177]: (D_1174='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1177, D_1174))), inference(negUnitSimplification, [status(thm)], [c_26, c_13227])).
% 8.51/2.93  tff(c_13244, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13243])).
% 8.51/2.93  tff(c_13272, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13244, c_16])).
% 8.51/2.93  tff(c_13283, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_13272])).
% 8.51/2.93  tff(c_13275, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_13244, c_14])).
% 8.51/2.93  tff(c_13284, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_13275])).
% 8.51/2.93  tff(c_13519, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13283, c_13284])).
% 8.51/2.93  tff(c_13520, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13519, c_12519])).
% 8.51/2.93  tff(c_12524, plain, (![A_1088, B_1089, C_1090, D_1091]: (k2_zfmisc_1(k3_zfmisc_1(A_1088, B_1089, C_1090), D_1091)=k4_zfmisc_1(A_1088, B_1089, C_1090, D_1091))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/2.93  tff(c_12785, plain, (![D_1122, A_1123, B_1124, C_1125]: (k1_xboole_0=D_1122 | k3_zfmisc_1(A_1123, B_1124, C_1125)=k1_xboole_0 | k4_zfmisc_1(A_1123, B_1124, C_1125, D_1122)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12524, c_2])).
% 8.51/2.93  tff(c_12800, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12519, c_12785])).
% 8.51/2.93  tff(c_12809, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_12800])).
% 8.51/2.93  tff(c_12810, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12809])).
% 8.51/2.93  tff(c_13294, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13283, c_12810])).
% 8.51/2.93  tff(c_13676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13520, c_13294])).
% 8.51/2.93  tff(c_13678, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_13243])).
% 8.51/2.93  tff(c_12703, plain, (![C_1114, A_1115, B_1116, D_1117]: (C_1114=A_1115 | k1_xboole_0=B_1116 | k1_xboole_0=A_1115 | k2_zfmisc_1(C_1114, D_1117)!=k2_zfmisc_1(A_1115, B_1116))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.51/2.93  tff(c_13897, plain, (![C_1245, A_1243, D_1240, B_1241, D_1244, C_1242]: (k3_zfmisc_1(A_1243, B_1241, C_1245)=C_1242 | k1_xboole_0=D_1244 | k3_zfmisc_1(A_1243, B_1241, C_1245)=k1_xboole_0 | k4_zfmisc_1(A_1243, B_1241, C_1245, D_1244)!=k2_zfmisc_1(C_1242, D_1240))), inference(superposition, [status(thm), theory('equality')], [c_14, c_12703])).
% 8.51/2.93  tff(c_13921, plain, (![C_1242, D_1240]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=C_1242 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1242, D_1240))), inference(superposition, [status(thm), theory('equality')], [c_12519, c_13897])).
% 8.51/2.93  tff(c_13945, plain, (![C_1247, D_1248]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=C_1247 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1247, D_1248))), inference(negUnitSimplification, [status(thm)], [c_13678, c_26, c_13921])).
% 8.51/2.93  tff(c_13948, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_13945])).
% 8.51/2.93  tff(c_13983, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_13948])).
% 8.51/2.93  tff(c_12668, plain, (![D_1107, C_1110, A_7, B_8, C_9]: (D_1107=C_9 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_1110, D_1107))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12656])).
% 8.51/2.93  tff(c_14038, plain, (![D_1107, C_1110]: (D_1107='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_1110, D_1107))), inference(superposition, [status(thm), theory('equality')], [c_13983, c_12668])).
% 8.51/2.93  tff(c_14237, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14038])).
% 8.51/2.93  tff(c_14262, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14237, c_2])).
% 8.51/2.93  tff(c_14273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_14262])).
% 8.51/2.93  tff(c_14274, plain, (![D_1107, C_1110]: (k1_xboole_0='#skF_7' | D_1107='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_1110, D_1107))), inference(splitRight, [status(thm)], [c_14038])).
% 8.51/2.93  tff(c_14298, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_14274])).
% 8.51/2.93  tff(c_14019, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13983, c_13678])).
% 8.51/2.93  tff(c_14306, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14298, c_14019])).
% 8.51/2.93  tff(c_14332, plain, (![A_14, B_15]: (k3_zfmisc_1(A_14, B_15, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14298, c_14298, c_18])).
% 8.51/2.93  tff(c_14514, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14332, c_13983])).
% 8.51/2.93  tff(c_14578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14306, c_14514])).
% 8.51/2.93  tff(c_14581, plain, (![D_1294, C_1295]: (D_1294='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_1295, D_1294))), inference(splitRight, [status(thm)], [c_14274])).
% 8.51/2.93  tff(c_14587, plain, (![C_9, A_7, B_8]: (C_9='#skF_7' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_14581])).
% 8.51/2.93  tff(c_14597, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_14587])).
% 8.51/2.93  tff(c_14599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12466, c_14597])).
% 8.51/2.93  tff(c_14600, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12809])).
% 8.51/2.93  tff(c_14608, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14600, c_16])).
% 8.51/2.93  tff(c_14617, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_14608])).
% 8.51/2.93  tff(c_14637, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_26])).
% 8.51/2.93  tff(c_14635, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_14617, c_4])).
% 8.51/2.93  tff(c_14639, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_32])).
% 8.51/2.93  tff(c_14636, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_30])).
% 8.51/2.93  tff(c_14601, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12809])).
% 8.51/2.93  tff(c_14715, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_14601])).
% 8.51/2.93  tff(c_12662, plain, (![D_1107, B_11, A_10, C_12, C_1110, D_13]: (D_13=D_1107 | k1_xboole_0=D_13 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k2_zfmisc_1(C_1110, D_1107))), inference(superposition, [status(thm), theory('equality')], [c_14, c_12656])).
% 8.51/2.93  tff(c_15154, plain, (![D_1354, C_1355, B_1351, A_1353, D_1352, C_1356]: (D_1354=D_1352 | D_1354='#skF_7' | k3_zfmisc_1(A_1353, B_1351, C_1356)='#skF_7' | k4_zfmisc_1(A_1353, B_1351, C_1356, D_1354)!=k2_zfmisc_1(C_1355, D_1352))), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_14617, c_12662])).
% 8.51/2.94  tff(c_15169, plain, (![D_1352, C_1355]: (D_1352='#skF_4' | '#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7' | k2_zfmisc_1(C_1355, D_1352)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14715, c_15154])).
% 8.51/2.94  tff(c_15186, plain, (![D_1352, C_1355]: (D_1352='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7' | k2_zfmisc_1(C_1355, D_1352)!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_14637, c_15169])).
% 8.51/2.94  tff(c_15187, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(splitLeft, [status(thm)], [c_15186])).
% 8.51/2.94  tff(c_14620, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_14600])).
% 8.51/2.94  tff(c_12665, plain, (![A_1109, A_7, B_8, C_9, B_1108]: (C_9=B_1108 | k1_xboole_0=B_1108 | k1_xboole_0=A_1109 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(A_1109, B_1108))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12656])).
% 8.51/2.94  tff(c_14644, plain, (![A_1109, A_7, B_8, C_9, B_1108]: (C_9=B_1108 | B_1108='#skF_7' | A_1109='#skF_7' | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(A_1109, B_1108))), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_14617, c_12665])).
% 8.51/2.94  tff(c_15054, plain, (![B_1339, A_1340]: (B_1339='#skF_7' | B_1339='#skF_7' | A_1340='#skF_7' | k2_zfmisc_1(A_1340, B_1339)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14620, c_14644])).
% 8.51/2.94  tff(c_15066, plain, (![C_9, A_7, B_8]: (C_9='#skF_7' | C_9='#skF_7' | k2_zfmisc_1(A_7, B_8)='#skF_7' | k3_zfmisc_1(A_7, B_8, C_9)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12, c_15054])).
% 8.51/2.94  tff(c_15191, plain, ('#skF_7'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_15187, c_15066])).
% 8.51/2.94  tff(c_15211, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_12466, c_12466, c_15191])).
% 8.51/2.94  tff(c_14630, plain, (![B_2, A_1]: (B_2='#skF_7' | A_1='#skF_7' | k2_zfmisc_1(A_1, B_2)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_14617, c_14617, c_2])).
% 8.51/2.94  tff(c_15219, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15211, c_14630])).
% 8.51/2.94  tff(c_15231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14639, c_14636, c_15219])).
% 8.51/2.94  tff(c_15234, plain, (![D_1357, C_1358]: (D_1357='#skF_4' | k2_zfmisc_1(C_1358, D_1357)!='#skF_7')), inference(splitRight, [status(thm)], [c_15186])).
% 8.51/2.94  tff(c_15237, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_14635, c_15234])).
% 8.51/2.94  tff(c_15250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14637, c_15237])).
% 8.51/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/2.94  
% 8.51/2.94  Inference rules
% 8.51/2.94  ----------------------
% 8.51/2.94  #Ref     : 37
% 8.51/2.94  #Sup     : 3681
% 8.51/2.94  #Fact    : 0
% 8.51/2.94  #Define  : 0
% 8.51/2.94  #Split   : 35
% 8.51/2.94  #Chain   : 0
% 8.51/2.94  #Close   : 0
% 8.51/2.94  
% 8.51/2.94  Ordering : KBO
% 8.51/2.94  
% 8.51/2.94  Simplification rules
% 8.51/2.94  ----------------------
% 8.51/2.94  #Subsume      : 777
% 8.51/2.94  #Demod        : 3244
% 8.51/2.94  #Tautology    : 1809
% 8.51/2.94  #SimpNegUnit  : 225
% 8.51/2.94  #BackRed      : 774
% 8.51/2.94  
% 8.51/2.94  #Partial instantiations: 0
% 8.51/2.94  #Strategies tried      : 1
% 8.51/2.94  
% 8.51/2.94  Timing (in seconds)
% 8.51/2.94  ----------------------
% 8.51/2.94  Preprocessing        : 0.30
% 8.51/2.94  Parsing              : 0.16
% 8.51/2.94  CNF conversion       : 0.02
% 8.51/2.94  Main loop            : 1.73
% 8.51/2.94  Inferencing          : 0.56
% 8.51/2.94  Reduction            : 0.57
% 8.51/2.94  Demodulation         : 0.40
% 8.51/2.94  BG Simplification    : 0.07
% 8.51/2.94  Subsumption          : 0.40
% 8.51/2.94  Abstraction          : 0.09
% 8.51/2.94  MUC search           : 0.00
% 8.51/2.94  Cooper               : 0.00
% 8.51/2.94  Total                : 2.14
% 8.51/2.94  Index Insertion      : 0.00
% 8.51/2.94  Index Deletion       : 0.00
% 8.51/2.94  Index Matching       : 0.00
% 8.51/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
