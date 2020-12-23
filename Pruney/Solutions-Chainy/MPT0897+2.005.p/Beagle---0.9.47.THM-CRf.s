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
% DateTime   : Thu Dec  3 10:09:48 EST 2020

% Result     : Theorem 8.36s
% Output     : CNFRefutation 8.90s
% Verified   : 
% Statistics : Number of formulae       :  373 (12267 expanded)
%              Number of leaves         :   20 (3398 expanded)
%              Depth                    :   27
%              Number of atoms          :  564 (33706 expanded)
%              Number of equality atoms :  529 (33671 expanded)
%              Maximal formula depth    :   15 (   3 average)
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

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_14,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),D_13) = k4_zfmisc_1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_286,plain,(
    ! [D_47,B_48,A_49,C_50] :
      ( D_47 = B_48
      | k1_xboole_0 = B_48
      | k1_xboole_0 = A_49
      | k2_zfmisc_1(C_50,D_47) != k2_zfmisc_1(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_707,plain,(
    ! [C_102,B_103,A_104,C_106,D_101,D_105] :
      ( D_105 = D_101
      | k1_xboole_0 = D_105
      | k3_zfmisc_1(A_104,B_103,C_106) = k1_xboole_0
      | k4_zfmisc_1(A_104,B_103,C_106,D_105) != k2_zfmisc_1(C_102,D_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_286])).

tff(c_728,plain,(
    ! [D_101,C_102] :
      ( D_101 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_102,D_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_707])).

tff(c_814,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_55,plain,(
    ! [A_18,B_19,C_20] : k2_zfmisc_1(k2_zfmisc_1(A_18,B_19),C_20) = k3_zfmisc_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_xboole_0 = C_20
      | k2_zfmisc_1(A_18,B_19) = k1_xboole_0
      | k3_zfmisc_1(A_18,B_19,C_20) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_847,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_64])).

tff(c_850,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_847])).

tff(c_881,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_2])).

tff(c_883,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_881])).

tff(c_18,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_905,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_18])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_842,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_14])).

tff(c_848,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_842])).

tff(c_1179,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_848])).

tff(c_1180,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_20])).

tff(c_1182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_905,c_1180])).

tff(c_1183,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_881])).

tff(c_1207,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_18])).

tff(c_1479,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_848])).

tff(c_1480,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_20])).

tff(c_1482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1207,c_1480])).

tff(c_1483,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_847])).

tff(c_1526,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_18])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_18,B_19] : k3_zfmisc_1(A_18,B_19,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_4])).

tff(c_139,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_zfmisc_1(k3_zfmisc_1(A_27,B_28,C_29),D_30) = k4_zfmisc_1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [A_18,B_19,D_30] : k4_zfmisc_1(A_18,B_19,k1_xboole_0,D_30) = k2_zfmisc_1(k1_xboole_0,D_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_139])).

tff(c_173,plain,(
    ! [A_18,B_19,D_30] : k4_zfmisc_1(A_18,B_19,k1_xboole_0,D_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_1519,plain,(
    ! [A_18,B_19,D_30] : k4_zfmisc_1(A_18,B_19,'#skF_7',D_30) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_1483,c_173])).

tff(c_1733,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_20])).

tff(c_1735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1526,c_1733])).

tff(c_1737,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_1736,plain,(
    ! [D_101,C_102] :
      ( k1_xboole_0 = '#skF_8'
      | D_101 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_102,D_101) ) ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_1779,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1736])).

tff(c_1801,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_18])).

tff(c_152,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_4])).

tff(c_1796,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_1779,c_152])).

tff(c_2028,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1796,c_20])).

tff(c_2030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1801,c_2028])).

tff(c_2033,plain,(
    ! [D_193,C_194] :
      ( D_193 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_194,D_193) ) ),
    inference(splitRight,[status(thm)],[c_1736])).

tff(c_2036,plain,(
    ! [D_13,A_10,B_11,C_12] :
      ( D_13 = '#skF_8'
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2033])).

tff(c_2066,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2036])).

tff(c_2032,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1736])).

tff(c_2128,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2066,c_2032])).

tff(c_2129,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2066,c_20])).

tff(c_186,plain,(
    ! [C_34,A_35,B_36,D_37] :
      ( C_34 = A_35
      | k1_xboole_0 = B_36
      | k1_xboole_0 = A_35
      | k2_zfmisc_1(C_34,D_37) != k2_zfmisc_1(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2226,plain,(
    ! [B_220,A_221,D_222,C_223,D_218,C_219] :
      ( k3_zfmisc_1(A_221,B_220,C_223) = C_219
      | k1_xboole_0 = D_222
      | k3_zfmisc_1(A_221,B_220,C_223) = k1_xboole_0
      | k4_zfmisc_1(A_221,B_220,C_223,D_222) != k2_zfmisc_1(C_219,D_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_186])).

tff(c_2229,plain,(
    ! [C_219,D_218] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = C_219
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_219,D_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2129,c_2226])).

tff(c_2268,plain,(
    ! [C_224,D_225] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = C_224
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_224,D_225) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1737,c_2128,c_2229])).

tff(c_2271,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2268])).

tff(c_2394,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2271])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_298,plain,(
    ! [A_7,C_50,B_8,C_9,D_47] :
      ( D_47 = C_9
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_50,D_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_286])).

tff(c_2449,plain,(
    ! [D_47,C_50] :
      ( D_47 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_50,D_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2394,c_298])).

tff(c_2719,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2449])).

tff(c_2751,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2719,c_2])).

tff(c_2753,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2751])).

tff(c_2430,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_1737])).

tff(c_2762,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2753,c_2430])).

tff(c_84,plain,(
    ! [B_2,C_20] : k3_zfmisc_1(k1_xboole_0,B_2,C_20) = k2_zfmisc_1(k1_xboole_0,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_88,plain,(
    ! [B_2,C_20] : k3_zfmisc_1(k1_xboole_0,B_2,C_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_2784,plain,(
    ! [B_2,C_20] : k3_zfmisc_1('#skF_5',B_2,C_20) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2753,c_2753,c_88])).

tff(c_2865,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_2394])).

tff(c_2934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2762,c_2865])).

tff(c_2935,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2751])).

tff(c_2985,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2935,c_2430])).

tff(c_2742,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = k2_zfmisc_1(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_2719,c_12])).

tff(c_2750,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2742])).

tff(c_3102,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_5','#skF_6',C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2935,c_2750])).

tff(c_3103,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3102,c_2394])).

tff(c_3124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2985,c_3103])).

tff(c_3126,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2449])).

tff(c_3125,plain,(
    ! [D_47,C_50] :
      ( k1_xboole_0 = '#skF_7'
      | D_47 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_50,D_47) ) ),
    inference(splitRight,[status(thm)],[c_2449])).

tff(c_3127,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3125])).

tff(c_3137,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3127,c_2430])).

tff(c_3160,plain,(
    ! [A_18,B_19] : k3_zfmisc_1(A_18,B_19,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3127,c_3127,c_68])).

tff(c_3306,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3160,c_2394])).

tff(c_3308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3137,c_3306])).

tff(c_3311,plain,(
    ! [D_297,C_298] :
      ( D_297 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_298,D_297) ) ),
    inference(splitRight,[status(thm)],[c_3125])).

tff(c_3317,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_7'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3311])).

tff(c_3327,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3317])).

tff(c_3310,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3125])).

tff(c_3390,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3327,c_3310])).

tff(c_3392,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3327,c_2394])).

tff(c_2092,plain,(
    ! [A_206,C_204,B_203,C_205,D_202] :
      ( k2_zfmisc_1(A_206,B_203) = C_204
      | k1_xboole_0 = C_205
      | k2_zfmisc_1(A_206,B_203) = k1_xboole_0
      | k3_zfmisc_1(A_206,B_203,C_205) != k2_zfmisc_1(C_204,D_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_186])).

tff(c_3595,plain,(
    ! [C_320,C_322,A_321,B_319,B_324,A_323] :
      ( k2_zfmisc_1(A_323,B_319) = k2_zfmisc_1(A_321,B_324)
      | k1_xboole_0 = C_322
      | k2_zfmisc_1(A_321,B_324) = k1_xboole_0
      | k3_zfmisc_1(A_323,B_319,C_320) != k3_zfmisc_1(A_321,B_324,C_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2092])).

tff(c_3601,plain,(
    ! [A_323,B_319,C_320] :
      ( k2_zfmisc_1(A_323,B_319) = k2_zfmisc_1('#skF_5','#skF_6')
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1(A_323,B_319,C_320) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3392,c_3595])).

tff(c_3632,plain,(
    ! [A_323,B_319,C_320] :
      ( k2_zfmisc_1(A_323,B_319) = k2_zfmisc_1('#skF_5','#skF_6')
      | k3_zfmisc_1(A_323,B_319,C_320) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3126,c_3390,c_3601])).

tff(c_3658,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3632])).

tff(c_8,plain,(
    ! [D_6,B_4,A_3,C_5] :
      ( D_6 = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3698,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_6'
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3658,c_8])).

tff(c_3957,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3698])).

tff(c_3976,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3957])).

tff(c_4017,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3976,c_3976,c_6])).

tff(c_3688,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_3126])).

tff(c_3980,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3976,c_3688])).

tff(c_4046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4017,c_3980])).

tff(c_4048,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3957])).

tff(c_16,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4,D_6] :
      ( C_5 = A_3
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3704,plain,(
    ! [A_3,B_4] :
      ( A_3 = '#skF_5'
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3658,c_10])).

tff(c_4295,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3704])).

tff(c_4296,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4048,c_54,c_4295])).

tff(c_4354,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4296,c_4296,c_4])).

tff(c_4319,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4296,c_3688])).

tff(c_4470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4354,c_4319])).

tff(c_4471,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_4477,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4471])).

tff(c_4472,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_4512,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4472,c_20])).

tff(c_4726,plain,(
    ! [D_400,B_401,A_402,C_403] :
      ( D_400 = B_401
      | k1_xboole_0 = B_401
      | k1_xboole_0 = A_402
      | k2_zfmisc_1(C_403,D_400) != k2_zfmisc_1(A_402,B_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5307,plain,(
    ! [A_476,B_475,C_474,D_473,C_478,D_477] :
      ( D_477 = D_473
      | k1_xboole_0 = D_477
      | k3_zfmisc_1(A_476,B_475,C_478) = k1_xboole_0
      | k4_zfmisc_1(A_476,B_475,C_478,D_477) != k2_zfmisc_1(C_474,D_473) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4726])).

tff(c_5331,plain,(
    ! [D_473,C_474] :
      ( D_473 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_474,D_473) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4512,c_5307])).

tff(c_5429,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5331])).

tff(c_4478,plain,(
    ! [A_368,B_369,C_370] : k2_zfmisc_1(k2_zfmisc_1(A_368,B_369),C_370) = k3_zfmisc_1(A_368,B_369,C_370) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4487,plain,(
    ! [C_370,A_368,B_369] :
      ( k1_xboole_0 = C_370
      | k2_zfmisc_1(A_368,B_369) = k1_xboole_0
      | k3_zfmisc_1(A_368,B_369,C_370) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4478,c_2])).

tff(c_5466,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5429,c_4487])).

tff(c_5470,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5466])).

tff(c_5501,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5470,c_2])).

tff(c_5503,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5501])).

tff(c_5530,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5503,c_18])).

tff(c_5461,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_5429,c_14])).

tff(c_5467,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5461])).

tff(c_5753,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5503,c_5467])).

tff(c_5754,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5753,c_4512])).

tff(c_5756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5530,c_5754])).

tff(c_5757,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5501])).

tff(c_5800,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5757,c_18])).

tff(c_6041,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5757,c_5467])).

tff(c_6042,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6041,c_4512])).

tff(c_6044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5800,c_6042])).

tff(c_6045,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5466])).

tff(c_6072,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6045,c_18])).

tff(c_6280,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6045,c_5467])).

tff(c_6281,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6280,c_4512])).

tff(c_6283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6072,c_6281])).

tff(c_6284,plain,(
    ! [D_473,C_474] :
      ( k1_xboole_0 = '#skF_8'
      | D_473 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_474,D_473) ) ),
    inference(splitRight,[status(thm)],[c_5331])).

tff(c_6286,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_6284])).

tff(c_6313,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6286,c_18])).

tff(c_4540,plain,(
    ! [A_375,B_376,C_377,D_378] : k2_zfmisc_1(k3_zfmisc_1(A_375,B_376,C_377),D_378) = k4_zfmisc_1(A_375,B_376,C_377,D_378) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4553,plain,(
    ! [A_375,B_376,C_377] : k4_zfmisc_1(A_375,B_376,C_377,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4540,c_4])).

tff(c_6308,plain,(
    ! [A_375,B_376,C_377] : k4_zfmisc_1(A_375,B_376,C_377,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6286,c_6286,c_4553])).

tff(c_6514,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6308,c_4512])).

tff(c_6516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6313,c_6514])).

tff(c_6524,plain,(
    ! [D_544,C_545] :
      ( D_544 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_545,D_544) ) ),
    inference(splitRight,[status(thm)],[c_6284])).

tff(c_6527,plain,(
    ! [D_13,A_10,B_11,C_12] :
      ( D_13 = '#skF_8'
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6524])).

tff(c_6571,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6527])).

tff(c_6573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4477,c_6571])).

tff(c_6574,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4471])).

tff(c_6585,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6574])).

tff(c_6575,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4471])).

tff(c_6580,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6575,c_4472,c_20])).

tff(c_6829,plain,(
    ! [D_583,B_584,A_585,C_586] :
      ( D_583 = B_584
      | k1_xboole_0 = B_584
      | k1_xboole_0 = A_585
      | k2_zfmisc_1(C_586,D_583) != k2_zfmisc_1(A_585,B_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7363,plain,(
    ! [B_649,D_652,D_654,C_650,C_653,A_651] :
      ( D_654 = D_652
      | k1_xboole_0 = D_652
      | k3_zfmisc_1(A_651,B_649,C_653) = k1_xboole_0
      | k4_zfmisc_1(A_651,B_649,C_653,D_652) != k2_zfmisc_1(C_650,D_654) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6829])).

tff(c_7390,plain,(
    ! [D_654,C_650] :
      ( D_654 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_650,D_654) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6580,c_7363])).

tff(c_7417,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7390])).

tff(c_6586,plain,(
    ! [A_551,B_552,C_553] : k2_zfmisc_1(k2_zfmisc_1(A_551,B_552),C_553) = k3_zfmisc_1(A_551,B_552,C_553) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6595,plain,(
    ! [C_553,A_551,B_552] :
      ( k1_xboole_0 = C_553
      | k2_zfmisc_1(A_551,B_552) = k1_xboole_0
      | k3_zfmisc_1(A_551,B_552,C_553) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6586,c_2])).

tff(c_7454,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7417,c_6595])).

tff(c_7457,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7454])).

tff(c_7488,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7457,c_2])).

tff(c_7490,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7488])).

tff(c_7555,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7490,c_18])).

tff(c_7449,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_7417,c_14])).

tff(c_7455,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7449])).

tff(c_7772,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7490,c_7455])).

tff(c_7773,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7772,c_6580])).

tff(c_7775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7555,c_7773])).

tff(c_7776,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7488])).

tff(c_7801,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7776,c_18])).

tff(c_8054,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7776,c_7455])).

tff(c_8055,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8054,c_6580])).

tff(c_8057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7801,c_8055])).

tff(c_8058,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7454])).

tff(c_8081,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8058,c_18])).

tff(c_8409,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8058,c_7455])).

tff(c_8410,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8409,c_6580])).

tff(c_8412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8081,c_8410])).

tff(c_8413,plain,(
    ! [D_654,C_650] :
      ( k1_xboole_0 = '#skF_4'
      | D_654 = '#skF_4'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_650,D_654) ) ),
    inference(splitRight,[status(thm)],[c_7390])).

tff(c_8415,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8413])).

tff(c_6642,plain,(
    ! [A_558,B_559,C_560,D_561] : k2_zfmisc_1(k3_zfmisc_1(A_558,B_559,C_560),D_561) = k4_zfmisc_1(A_558,B_559,C_560,D_561) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6655,plain,(
    ! [A_558,B_559,C_560] : k4_zfmisc_1(A_558,B_559,C_560,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6642,c_4])).

tff(c_8433,plain,(
    ! [A_558,B_559,C_560] : k4_zfmisc_1(A_558,B_559,C_560,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8415,c_8415,c_6655])).

tff(c_8438,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8415,c_18])).

tff(c_8674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8433,c_8438])).

tff(c_8676,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8413])).

tff(c_6712,plain,(
    ! [C_567,A_568,B_569,D_570] :
      ( C_567 = A_568
      | k1_xboole_0 = B_569
      | k1_xboole_0 = A_568
      | k2_zfmisc_1(C_567,D_570) != k2_zfmisc_1(A_568,B_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7322,plain,(
    ! [A_645,A_644,C_648,B_647,B_643,D_646] :
      ( k3_zfmisc_1(A_645,B_643,C_648) = A_644
      | k1_xboole_0 = B_647
      | k1_xboole_0 = A_644
      | k4_zfmisc_1(A_645,B_643,C_648,D_646) != k2_zfmisc_1(A_644,B_647) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6712])).

tff(c_7404,plain,(
    ! [A_655,B_656] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = A_655
      | k1_xboole_0 = B_656
      | k1_xboole_0 = A_655
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(A_655,B_656) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6580,c_7322])).

tff(c_7407,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
      | k1_xboole_0 = D_13
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7404])).

tff(c_8879,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7407])).

tff(c_8880,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8676,c_8879])).

tff(c_8915,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8880])).

tff(c_8951,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8915,c_6595])).

tff(c_8954,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8951])).

tff(c_8985,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8954,c_2])).

tff(c_8987,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8985])).

tff(c_6615,plain,(
    ! [B_2,C_553] : k3_zfmisc_1(k1_xboole_0,B_2,C_553) = k2_zfmisc_1(k1_xboole_0,C_553) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_6586])).

tff(c_6619,plain,(
    ! [B_2,C_553] : k3_zfmisc_1(k1_xboole_0,B_2,C_553) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6615])).

tff(c_9056,plain,(
    ! [B_2,C_553] : k3_zfmisc_1('#skF_1',B_2,C_553) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8987,c_8987,c_6619])).

tff(c_8414,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7390])).

tff(c_9039,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8987,c_8414])).

tff(c_9259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9056,c_9039])).

tff(c_9260,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8985])).

tff(c_8946,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_8915,c_14])).

tff(c_8952,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8946])).

tff(c_9576,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_13) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9260,c_8952])).

tff(c_9290,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9260,c_18])).

tff(c_9585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9576,c_9290])).

tff(c_9586,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8951])).

tff(c_9593,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9586,c_8414])).

tff(c_6599,plain,(
    ! [A_551,B_552] : k3_zfmisc_1(A_551,B_552,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6586,c_4])).

tff(c_9612,plain,(
    ! [A_551,B_552] : k3_zfmisc_1(A_551,B_552,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9586,c_9586,c_6599])).

tff(c_8800,plain,(
    ! [A_757,C_759,C_756,B_755,D_758,D_754] :
      ( k3_zfmisc_1(A_757,B_755,C_759) = C_756
      | k1_xboole_0 = D_758
      | k3_zfmisc_1(A_757,B_755,C_759) = k1_xboole_0
      | k4_zfmisc_1(A_757,B_755,C_759,D_758) != k2_zfmisc_1(C_756,D_754) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6712])).

tff(c_8827,plain,(
    ! [C_756,D_754] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_756
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_756,D_754) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6580,c_8800])).

tff(c_8841,plain,(
    ! [C_760,D_761] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_760
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_760,D_761) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8414,c_8676,c_8827])).

tff(c_8844,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_8841])).

tff(c_9812,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8844])).

tff(c_9813,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9612,c_9812])).

tff(c_9815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9593,c_9813])).

tff(c_9816,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_8880])).

tff(c_6841,plain,(
    ! [D_583,A_7,C_586,B_8,C_9] :
      ( D_583 = C_9
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_586,D_583) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6829])).

tff(c_9840,plain,(
    ! [D_583,C_586] :
      ( D_583 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_586,D_583) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9816,c_6841])).

tff(c_10106,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9840])).

tff(c_10138,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_10106,c_2])).

tff(c_10140,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10138])).

tff(c_10168,plain,(
    ! [B_2,C_553] : k3_zfmisc_1('#skF_1',B_2,C_553) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10140,c_10140,c_6619])).

tff(c_9817,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8880])).

tff(c_10148,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10140,c_9817])).

tff(c_10276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10168,c_10148])).

tff(c_10277,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10138])).

tff(c_10287,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10277,c_9817])).

tff(c_10129,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_1','#skF_6',C_9) = k2_zfmisc_1(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10106,c_12])).

tff(c_10137,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_1','#skF_6',C_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10129])).

tff(c_10403,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_1','#skF_6',C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10277,c_10137])).

tff(c_10404,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10403,c_9816])).

tff(c_10406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10287,c_10404])).

tff(c_10408,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9840])).

tff(c_10407,plain,(
    ! [D_583,C_586] :
      ( k1_xboole_0 = '#skF_7'
      | D_583 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_586,D_583) ) ),
    inference(splitRight,[status(thm)],[c_9840])).

tff(c_10409,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_10407])).

tff(c_10440,plain,(
    ! [A_551,B_552] : k3_zfmisc_1(A_551,B_552,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10409,c_10409,c_6599])).

tff(c_10546,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10440,c_9816])).

tff(c_10418,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10409,c_9817])).

tff(c_10603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10546,c_10418])).

tff(c_10606,plain,(
    ! [D_867,C_868] :
      ( D_867 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_868,D_867) ) ),
    inference(splitRight,[status(thm)],[c_10407])).

tff(c_10612,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_7'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10606])).

tff(c_10622,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10612])).

tff(c_10605,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10407])).

tff(c_10648,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10622,c_10605])).

tff(c_10650,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10622,c_9816])).

tff(c_6724,plain,(
    ! [A_7,D_570,C_567,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = C_567
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_567,D_570) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6712])).

tff(c_10658,plain,(
    ! [C_567,D_570] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = C_567
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_567,D_570) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10650,c_6724])).

tff(c_10843,plain,(
    ! [C_885,D_886] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = C_885
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_885,D_886) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10408,c_10648,c_10658])).

tff(c_10849,plain,(
    ! [A_7,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = k2_zfmisc_1('#skF_1','#skF_6')
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10843])).

tff(c_10915,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10849])).

tff(c_10964,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_1'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10915,c_10])).

tff(c_11176,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10964])).

tff(c_11214,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11176,c_11176,c_6])).

tff(c_10945,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10915,c_10408])).

tff(c_11180,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11176,c_10945])).

tff(c_11300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11214,c_11180])).

tff(c_11302,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10964])).

tff(c_11301,plain,(
    ! [C_5,D_6] :
      ( k1_xboole_0 = '#skF_6'
      | C_5 = '#skF_1'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_10964])).

tff(c_11303,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11301])).

tff(c_11341,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11303,c_11303,c_4])).

tff(c_11347,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11341,c_10915])).

tff(c_11308,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11303,c_10945])).

tff(c_11477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11347,c_11308])).

tff(c_11479,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11301])).

tff(c_10958,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10915,c_8])).

tff(c_11529,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_6'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_11302,c_11479,c_10958])).

tff(c_11532,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11529])).

tff(c_11534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6585,c_11532])).

tff(c_11535,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6574])).

tff(c_11536,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6574])).

tff(c_11537,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11536,c_6580])).

tff(c_11673,plain,(
    ! [D_943,B_944,A_945,C_946] :
      ( D_943 = B_944
      | k1_xboole_0 = B_944
      | k1_xboole_0 = A_945
      | k2_zfmisc_1(C_946,D_943) != k2_zfmisc_1(A_945,B_944) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12323,plain,(
    ! [D_1029,B_1026,D_1027,A_1028,C_1030,C_1025] :
      ( D_1029 = D_1027
      | k1_xboole_0 = D_1029
      | k3_zfmisc_1(A_1028,B_1026,C_1030) = k1_xboole_0
      | k4_zfmisc_1(A_1028,B_1026,C_1030,D_1029) != k2_zfmisc_1(C_1025,D_1027) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_11673])).

tff(c_12347,plain,(
    ! [D_1027,C_1025] :
      ( D_1027 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1025,D_1027) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11537,c_12323])).

tff(c_12459,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12347])).

tff(c_11542,plain,(
    ! [A_927,B_928,C_929] : k2_zfmisc_1(k2_zfmisc_1(A_927,B_928),C_929) = k3_zfmisc_1(A_927,B_928,C_929) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11551,plain,(
    ! [C_929,A_927,B_928] :
      ( k1_xboole_0 = C_929
      | k2_zfmisc_1(A_927,B_928) = k1_xboole_0
      | k3_zfmisc_1(A_927,B_928,C_929) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11542,c_2])).

tff(c_12497,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12459,c_11551])).

tff(c_12501,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12497])).

tff(c_12532,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12501,c_2])).

tff(c_12534,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12532])).

tff(c_12573,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12534,c_18])).

tff(c_12492,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_12459,c_14])).

tff(c_12498,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12492])).

tff(c_12805,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_13) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12534,c_12498])).

tff(c_12806,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12805,c_11537])).

tff(c_12808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12573,c_12806])).

tff(c_12809,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12532])).

tff(c_12836,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12809,c_18])).

tff(c_13125,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_13) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12809,c_12498])).

tff(c_13126,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13125,c_11537])).

tff(c_13128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12836,c_13126])).

tff(c_13129,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_12497])).

tff(c_13154,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13129,c_18])).

tff(c_11555,plain,(
    ! [A_927,B_928] : k3_zfmisc_1(A_927,B_928,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11542,c_4])).

tff(c_11626,plain,(
    ! [A_936,B_937,C_938,D_939] : k2_zfmisc_1(k3_zfmisc_1(A_936,B_937,C_938),D_939) = k4_zfmisc_1(A_936,B_937,C_938,D_939) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11651,plain,(
    ! [A_927,B_928,D_939] : k4_zfmisc_1(A_927,B_928,k1_xboole_0,D_939) = k2_zfmisc_1(k1_xboole_0,D_939) ),
    inference(superposition,[status(thm),theory(equality)],[c_11555,c_11626])).

tff(c_11660,plain,(
    ! [A_927,B_928,D_939] : k4_zfmisc_1(A_927,B_928,k1_xboole_0,D_939) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11651])).

tff(c_13147,plain,(
    ! [A_927,B_928,D_939] : k4_zfmisc_1(A_927,B_928,'#skF_7',D_939) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13129,c_13129,c_11660])).

tff(c_13392,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13147,c_11537])).

tff(c_13394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13154,c_13392])).

tff(c_13396,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12347])).

tff(c_13395,plain,(
    ! [D_1027,C_1025] :
      ( k1_xboole_0 = '#skF_4'
      | D_1027 = '#skF_4'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1025,D_1027) ) ),
    inference(splitRight,[status(thm)],[c_12347])).

tff(c_13397,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13395])).

tff(c_11639,plain,(
    ! [A_936,B_937,C_938] : k4_zfmisc_1(A_936,B_937,C_938,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11626,c_4])).

tff(c_13419,plain,(
    ! [A_936,B_937,C_938] : k4_zfmisc_1(A_936,B_937,C_938,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13397,c_13397,c_11639])).

tff(c_13424,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13397,c_18])).

tff(c_13605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13419,c_13424])).

tff(c_13607,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13395])).

tff(c_11773,plain,(
    ! [C_956,A_957,B_958,D_959] :
      ( C_956 = A_957
      | k1_xboole_0 = B_958
      | k1_xboole_0 = A_957
      | k2_zfmisc_1(C_956,D_959) != k2_zfmisc_1(A_957,B_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12406,plain,(
    ! [D_1042,C_1043,B_1038,C_1039,D_1041,A_1040] :
      ( k3_zfmisc_1(A_1040,B_1038,C_1043) = C_1039
      | k1_xboole_0 = D_1041
      | k3_zfmisc_1(A_1040,B_1038,C_1043) = k1_xboole_0
      | k4_zfmisc_1(A_1040,B_1038,C_1043,D_1041) != k2_zfmisc_1(C_1039,D_1042) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_11773])).

tff(c_12430,plain,(
    ! [C_1039,D_1042] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = C_1039
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1039,D_1042) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11537,c_12406])).

tff(c_13712,plain,(
    ! [C_1128,D_1129] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = C_1128
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1128,D_1129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13396,c_13607,c_12430])).

tff(c_13715,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( k3_zfmisc_1(A_10,B_11,C_12) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_13712])).

tff(c_13750,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13715])).

tff(c_11685,plain,(
    ! [A_7,C_946,D_943,B_8,C_9] :
      ( D_943 = C_9
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_946,D_943) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_11673])).

tff(c_13856,plain,(
    ! [D_943,C_946] :
      ( D_943 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_946,D_943) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13750,c_11685])).

tff(c_14106,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13856])).

tff(c_14137,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14106,c_2])).

tff(c_14139,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14137])).

tff(c_11571,plain,(
    ! [B_2,C_929] : k3_zfmisc_1(k1_xboole_0,B_2,C_929) = k2_zfmisc_1(k1_xboole_0,C_929) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_11542])).

tff(c_11575,plain,(
    ! [B_2,C_929] : k3_zfmisc_1(k1_xboole_0,B_2,C_929) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11571])).

tff(c_14171,plain,(
    ! [B_2,C_929] : k3_zfmisc_1('#skF_1',B_2,C_929) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14139,c_14139,c_11575])).

tff(c_13840,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13750,c_13396])).

tff(c_14148,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14139,c_13840])).

tff(c_14324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14171,c_14148])).

tff(c_14325,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14137])).

tff(c_11564,plain,(
    ! [A_1,C_929] : k3_zfmisc_1(A_1,k1_xboole_0,C_929) = k2_zfmisc_1(k1_xboole_0,C_929) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_11542])).

tff(c_11574,plain,(
    ! [A_1,C_929] : k3_zfmisc_1(A_1,k1_xboole_0,C_929) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11564])).

tff(c_14358,plain,(
    ! [A_1,C_929] : k3_zfmisc_1(A_1,'#skF_2',C_929) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14325,c_14325,c_11574])).

tff(c_14336,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14325,c_13840])).

tff(c_14547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14358,c_14336])).

tff(c_14548,plain,(
    ! [D_943,C_946] :
      ( k1_xboole_0 = '#skF_7'
      | D_943 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_946,D_943) ) ),
    inference(splitRight,[status(thm)],[c_13856])).

tff(c_14550,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_14548])).

tff(c_14559,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14550,c_13840])).

tff(c_14583,plain,(
    ! [A_927,B_928] : k3_zfmisc_1(A_927,B_928,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14550,c_14550,c_11555])).

tff(c_14689,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14583,c_13750])).

tff(c_14773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14559,c_14689])).

tff(c_14776,plain,(
    ! [D_1197,C_1198] :
      ( D_1197 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_1198,D_1197) ) ),
    inference(splitRight,[status(thm)],[c_14548])).

tff(c_14782,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_7'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_14776])).

tff(c_14792,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_14782])).

tff(c_14794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11535,c_14792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:42:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.36/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.92  
% 8.53/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.92  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 8.53/2.92  
% 8.53/2.92  %Foreground sorts:
% 8.53/2.92  
% 8.53/2.92  
% 8.53/2.92  %Background operators:
% 8.53/2.92  
% 8.53/2.92  
% 8.53/2.92  %Foreground operators:
% 8.53/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.53/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.53/2.92  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 8.53/2.92  tff('#skF_7', type, '#skF_7': $i).
% 8.53/2.92  tff('#skF_5', type, '#skF_5': $i).
% 8.53/2.92  tff('#skF_6', type, '#skF_6': $i).
% 8.53/2.92  tff('#skF_2', type, '#skF_2': $i).
% 8.53/2.92  tff('#skF_3', type, '#skF_3': $i).
% 8.53/2.92  tff('#skF_1', type, '#skF_1': $i).
% 8.53/2.92  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.53/2.92  tff('#skF_8', type, '#skF_8': $i).
% 8.53/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.53/2.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.53/2.92  tff('#skF_4', type, '#skF_4': $i).
% 8.53/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.53/2.92  
% 8.90/2.96  tff(f_45, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 8.90/2.96  tff(f_58, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 8.90/2.96  tff(f_41, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 8.90/2.96  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.90/2.96  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.90/2.96  tff(c_14, plain, (![A_10, B_11, C_12, D_13]: (k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), D_13)=k4_zfmisc_1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.90/2.96  tff(c_20, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.90/2.96  tff(c_286, plain, (![D_47, B_48, A_49, C_50]: (D_47=B_48 | k1_xboole_0=B_48 | k1_xboole_0=A_49 | k2_zfmisc_1(C_50, D_47)!=k2_zfmisc_1(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.96  tff(c_707, plain, (![C_102, B_103, A_104, C_106, D_101, D_105]: (D_105=D_101 | k1_xboole_0=D_105 | k3_zfmisc_1(A_104, B_103, C_106)=k1_xboole_0 | k4_zfmisc_1(A_104, B_103, C_106, D_105)!=k2_zfmisc_1(C_102, D_101))), inference(superposition, [status(thm), theory('equality')], [c_14, c_286])).
% 8.90/2.96  tff(c_728, plain, (![D_101, C_102]: (D_101='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_102, D_101))), inference(superposition, [status(thm), theory('equality')], [c_20, c_707])).
% 8.90/2.96  tff(c_814, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_728])).
% 8.90/2.96  tff(c_55, plain, (![A_18, B_19, C_20]: (k2_zfmisc_1(k2_zfmisc_1(A_18, B_19), C_20)=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.90/2.96  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.90/2.96  tff(c_64, plain, (![C_20, A_18, B_19]: (k1_xboole_0=C_20 | k2_zfmisc_1(A_18, B_19)=k1_xboole_0 | k3_zfmisc_1(A_18, B_19, C_20)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 8.90/2.96  tff(c_847, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_814, c_64])).
% 8.90/2.96  tff(c_850, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_847])).
% 8.90/2.96  tff(c_881, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_850, c_2])).
% 8.90/2.96  tff(c_883, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_881])).
% 8.90/2.96  tff(c_18, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.90/2.96  tff(c_905, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_883, c_18])).
% 8.90/2.96  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.90/2.96  tff(c_842, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_814, c_14])).
% 8.90/2.96  tff(c_848, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_842])).
% 8.90/2.96  tff(c_1179, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_848])).
% 8.90/2.96  tff(c_1180, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_20])).
% 8.90/2.96  tff(c_1182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_905, c_1180])).
% 8.90/2.96  tff(c_1183, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_881])).
% 8.90/2.96  tff(c_1207, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_18])).
% 8.90/2.96  tff(c_1479, plain, (![D_13]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_848])).
% 8.90/2.96  tff(c_1480, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_20])).
% 8.90/2.96  tff(c_1482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1207, c_1480])).
% 8.90/2.96  tff(c_1483, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_847])).
% 8.90/2.96  tff(c_1526, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1483, c_18])).
% 8.90/2.96  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.90/2.96  tff(c_68, plain, (![A_18, B_19]: (k3_zfmisc_1(A_18, B_19, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55, c_4])).
% 8.90/2.96  tff(c_139, plain, (![A_27, B_28, C_29, D_30]: (k2_zfmisc_1(k3_zfmisc_1(A_27, B_28, C_29), D_30)=k4_zfmisc_1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.90/2.96  tff(c_164, plain, (![A_18, B_19, D_30]: (k4_zfmisc_1(A_18, B_19, k1_xboole_0, D_30)=k2_zfmisc_1(k1_xboole_0, D_30))), inference(superposition, [status(thm), theory('equality')], [c_68, c_139])).
% 8.90/2.96  tff(c_173, plain, (![A_18, B_19, D_30]: (k4_zfmisc_1(A_18, B_19, k1_xboole_0, D_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 8.90/2.96  tff(c_1519, plain, (![A_18, B_19, D_30]: (k4_zfmisc_1(A_18, B_19, '#skF_7', D_30)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1483, c_1483, c_173])).
% 8.90/2.96  tff(c_1733, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1519, c_20])).
% 8.90/2.96  tff(c_1735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1526, c_1733])).
% 8.90/2.96  tff(c_1737, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_728])).
% 8.90/2.96  tff(c_1736, plain, (![D_101, C_102]: (k1_xboole_0='#skF_8' | D_101='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_102, D_101))), inference(splitRight, [status(thm)], [c_728])).
% 8.90/2.96  tff(c_1779, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_1736])).
% 8.90/2.96  tff(c_1801, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_18])).
% 8.90/2.96  tff(c_152, plain, (![A_27, B_28, C_29]: (k4_zfmisc_1(A_27, B_28, C_29, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_139, c_4])).
% 8.90/2.96  tff(c_1796, plain, (![A_27, B_28, C_29]: (k4_zfmisc_1(A_27, B_28, C_29, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_1779, c_152])).
% 8.90/2.96  tff(c_2028, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1796, c_20])).
% 8.90/2.96  tff(c_2030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1801, c_2028])).
% 8.90/2.96  tff(c_2033, plain, (![D_193, C_194]: (D_193='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_194, D_193))), inference(splitRight, [status(thm)], [c_1736])).
% 8.90/2.96  tff(c_2036, plain, (![D_13, A_10, B_11, C_12]: (D_13='#skF_8' | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2033])).
% 8.90/2.96  tff(c_2066, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_2036])).
% 8.90/2.96  tff(c_2032, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_1736])).
% 8.90/2.96  tff(c_2128, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2066, c_2032])).
% 8.90/2.96  tff(c_2129, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2066, c_20])).
% 8.90/2.96  tff(c_186, plain, (![C_34, A_35, B_36, D_37]: (C_34=A_35 | k1_xboole_0=B_36 | k1_xboole_0=A_35 | k2_zfmisc_1(C_34, D_37)!=k2_zfmisc_1(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.96  tff(c_2226, plain, (![B_220, A_221, D_222, C_223, D_218, C_219]: (k3_zfmisc_1(A_221, B_220, C_223)=C_219 | k1_xboole_0=D_222 | k3_zfmisc_1(A_221, B_220, C_223)=k1_xboole_0 | k4_zfmisc_1(A_221, B_220, C_223, D_222)!=k2_zfmisc_1(C_219, D_218))), inference(superposition, [status(thm), theory('equality')], [c_14, c_186])).
% 8.90/2.96  tff(c_2229, plain, (![C_219, D_218]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=C_219 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_219, D_218))), inference(superposition, [status(thm), theory('equality')], [c_2129, c_2226])).
% 8.90/2.96  tff(c_2268, plain, (![C_224, D_225]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=C_224 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_224, D_225))), inference(negUnitSimplification, [status(thm)], [c_1737, c_2128, c_2229])).
% 8.90/2.96  tff(c_2271, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2268])).
% 8.90/2.96  tff(c_2394, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_2271])).
% 8.90/2.96  tff(c_12, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.90/2.96  tff(c_298, plain, (![A_7, C_50, B_8, C_9, D_47]: (D_47=C_9 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_50, D_47))), inference(superposition, [status(thm), theory('equality')], [c_12, c_286])).
% 8.90/2.96  tff(c_2449, plain, (![D_47, C_50]: (D_47='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_50, D_47))), inference(superposition, [status(thm), theory('equality')], [c_2394, c_298])).
% 8.90/2.96  tff(c_2719, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2449])).
% 8.90/2.96  tff(c_2751, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2719, c_2])).
% 8.90/2.96  tff(c_2753, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2751])).
% 8.90/2.96  tff(c_2430, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2394, c_1737])).
% 8.90/2.96  tff(c_2762, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2753, c_2430])).
% 8.90/2.96  tff(c_84, plain, (![B_2, C_20]: (k3_zfmisc_1(k1_xboole_0, B_2, C_20)=k2_zfmisc_1(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_6, c_55])).
% 8.90/2.96  tff(c_88, plain, (![B_2, C_20]: (k3_zfmisc_1(k1_xboole_0, B_2, C_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_84])).
% 8.90/2.96  tff(c_2784, plain, (![B_2, C_20]: (k3_zfmisc_1('#skF_5', B_2, C_20)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2753, c_2753, c_88])).
% 8.90/2.96  tff(c_2865, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2784, c_2394])).
% 8.90/2.96  tff(c_2934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2762, c_2865])).
% 8.90/2.96  tff(c_2935, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2751])).
% 8.90/2.96  tff(c_2985, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2935, c_2430])).
% 8.90/2.96  tff(c_2742, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)=k2_zfmisc_1(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_2719, c_12])).
% 8.90/2.96  tff(c_2750, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2742])).
% 8.90/2.96  tff(c_3102, plain, (![C_9]: (k3_zfmisc_1('#skF_5', '#skF_6', C_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2935, c_2750])).
% 8.90/2.96  tff(c_3103, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3102, c_2394])).
% 8.90/2.96  tff(c_3124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2985, c_3103])).
% 8.90/2.96  tff(c_3126, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2449])).
% 8.90/2.96  tff(c_3125, plain, (![D_47, C_50]: (k1_xboole_0='#skF_7' | D_47='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_50, D_47))), inference(splitRight, [status(thm)], [c_2449])).
% 8.90/2.96  tff(c_3127, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_3125])).
% 8.90/2.96  tff(c_3137, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3127, c_2430])).
% 8.90/2.96  tff(c_3160, plain, (![A_18, B_19]: (k3_zfmisc_1(A_18, B_19, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3127, c_3127, c_68])).
% 8.90/2.96  tff(c_3306, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3160, c_2394])).
% 8.90/2.96  tff(c_3308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3137, c_3306])).
% 8.90/2.96  tff(c_3311, plain, (![D_297, C_298]: (D_297='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_298, D_297))), inference(splitRight, [status(thm)], [c_3125])).
% 8.90/2.96  tff(c_3317, plain, (![C_9, A_7, B_8]: (C_9='#skF_7' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3311])).
% 8.90/2.96  tff(c_3327, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_3317])).
% 8.90/2.96  tff(c_3310, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_3125])).
% 8.90/2.96  tff(c_3390, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3327, c_3310])).
% 8.90/2.96  tff(c_3392, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3327, c_2394])).
% 8.90/2.96  tff(c_2092, plain, (![A_206, C_204, B_203, C_205, D_202]: (k2_zfmisc_1(A_206, B_203)=C_204 | k1_xboole_0=C_205 | k2_zfmisc_1(A_206, B_203)=k1_xboole_0 | k3_zfmisc_1(A_206, B_203, C_205)!=k2_zfmisc_1(C_204, D_202))), inference(superposition, [status(thm), theory('equality')], [c_12, c_186])).
% 8.90/2.96  tff(c_3595, plain, (![C_320, C_322, A_321, B_319, B_324, A_323]: (k2_zfmisc_1(A_323, B_319)=k2_zfmisc_1(A_321, B_324) | k1_xboole_0=C_322 | k2_zfmisc_1(A_321, B_324)=k1_xboole_0 | k3_zfmisc_1(A_323, B_319, C_320)!=k3_zfmisc_1(A_321, B_324, C_322))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2092])).
% 8.90/2.96  tff(c_3601, plain, (![A_323, B_319, C_320]: (k2_zfmisc_1(A_323, B_319)=k2_zfmisc_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1(A_323, B_319, C_320)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3392, c_3595])).
% 8.90/2.96  tff(c_3632, plain, (![A_323, B_319, C_320]: (k2_zfmisc_1(A_323, B_319)=k2_zfmisc_1('#skF_5', '#skF_6') | k3_zfmisc_1(A_323, B_319, C_320)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3126, c_3390, c_3601])).
% 8.90/2.96  tff(c_3658, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_3632])).
% 8.90/2.96  tff(c_8, plain, (![D_6, B_4, A_3, C_5]: (D_6=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.96  tff(c_3698, plain, (![B_4, A_3]: (B_4='#skF_6' | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3658, c_8])).
% 8.90/2.96  tff(c_3957, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_3698])).
% 8.90/2.96  tff(c_3976, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3957])).
% 8.90/2.96  tff(c_4017, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3976, c_3976, c_6])).
% 8.90/2.96  tff(c_3688, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_3126])).
% 8.90/2.96  tff(c_3980, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3976, c_3688])).
% 8.90/2.96  tff(c_4046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4017, c_3980])).
% 8.90/2.96  tff(c_4048, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_3957])).
% 8.90/2.96  tff(c_16, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.90/2.96  tff(c_54, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_16])).
% 8.90/2.96  tff(c_10, plain, (![C_5, A_3, B_4, D_6]: (C_5=A_3 | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.96  tff(c_3704, plain, (![A_3, B_4]: (A_3='#skF_5' | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3658, c_10])).
% 8.90/2.96  tff(c_4295, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_3704])).
% 8.90/2.96  tff(c_4296, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4048, c_54, c_4295])).
% 8.90/2.96  tff(c_4354, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4296, c_4296, c_4])).
% 8.90/2.96  tff(c_4319, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4296, c_3688])).
% 8.90/2.96  tff(c_4470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4354, c_4319])).
% 8.90/2.96  tff(c_4471, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 8.90/2.96  tff(c_4477, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_4471])).
% 8.90/2.96  tff(c_4472, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 8.90/2.96  tff(c_4512, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4472, c_20])).
% 8.90/2.96  tff(c_4726, plain, (![D_400, B_401, A_402, C_403]: (D_400=B_401 | k1_xboole_0=B_401 | k1_xboole_0=A_402 | k2_zfmisc_1(C_403, D_400)!=k2_zfmisc_1(A_402, B_401))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.96  tff(c_5307, plain, (![A_476, B_475, C_474, D_473, C_478, D_477]: (D_477=D_473 | k1_xboole_0=D_477 | k3_zfmisc_1(A_476, B_475, C_478)=k1_xboole_0 | k4_zfmisc_1(A_476, B_475, C_478, D_477)!=k2_zfmisc_1(C_474, D_473))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4726])).
% 8.90/2.96  tff(c_5331, plain, (![D_473, C_474]: (D_473='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_474, D_473))), inference(superposition, [status(thm), theory('equality')], [c_4512, c_5307])).
% 8.90/2.96  tff(c_5429, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5331])).
% 8.90/2.96  tff(c_4478, plain, (![A_368, B_369, C_370]: (k2_zfmisc_1(k2_zfmisc_1(A_368, B_369), C_370)=k3_zfmisc_1(A_368, B_369, C_370))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.90/2.96  tff(c_4487, plain, (![C_370, A_368, B_369]: (k1_xboole_0=C_370 | k2_zfmisc_1(A_368, B_369)=k1_xboole_0 | k3_zfmisc_1(A_368, B_369, C_370)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4478, c_2])).
% 8.90/2.96  tff(c_5466, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5429, c_4487])).
% 8.90/2.96  tff(c_5470, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5466])).
% 8.90/2.96  tff(c_5501, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5470, c_2])).
% 8.90/2.96  tff(c_5503, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_5501])).
% 8.90/2.96  tff(c_5530, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5503, c_18])).
% 8.90/2.96  tff(c_5461, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_5429, c_14])).
% 8.90/2.96  tff(c_5467, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5461])).
% 8.90/2.96  tff(c_5753, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5503, c_5467])).
% 8.90/2.96  tff(c_5754, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5753, c_4512])).
% 8.90/2.96  tff(c_5756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5530, c_5754])).
% 8.90/2.96  tff(c_5757, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_5501])).
% 8.90/2.96  tff(c_5800, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5757, c_18])).
% 8.90/2.96  tff(c_6041, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5757, c_5467])).
% 8.90/2.96  tff(c_6042, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6041, c_4512])).
% 8.90/2.96  tff(c_6044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5800, c_6042])).
% 8.90/2.96  tff(c_6045, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_5466])).
% 8.90/2.96  tff(c_6072, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6045, c_18])).
% 8.90/2.96  tff(c_6280, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6045, c_5467])).
% 8.90/2.96  tff(c_6281, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6280, c_4512])).
% 8.90/2.96  tff(c_6283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6072, c_6281])).
% 8.90/2.96  tff(c_6284, plain, (![D_473, C_474]: (k1_xboole_0='#skF_8' | D_473='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_474, D_473))), inference(splitRight, [status(thm)], [c_5331])).
% 8.90/2.96  tff(c_6286, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_6284])).
% 8.90/2.96  tff(c_6313, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6286, c_18])).
% 8.90/2.96  tff(c_4540, plain, (![A_375, B_376, C_377, D_378]: (k2_zfmisc_1(k3_zfmisc_1(A_375, B_376, C_377), D_378)=k4_zfmisc_1(A_375, B_376, C_377, D_378))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.90/2.96  tff(c_4553, plain, (![A_375, B_376, C_377]: (k4_zfmisc_1(A_375, B_376, C_377, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4540, c_4])).
% 8.90/2.96  tff(c_6308, plain, (![A_375, B_376, C_377]: (k4_zfmisc_1(A_375, B_376, C_377, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6286, c_6286, c_4553])).
% 8.90/2.96  tff(c_6514, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6308, c_4512])).
% 8.90/2.96  tff(c_6516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6313, c_6514])).
% 8.90/2.96  tff(c_6524, plain, (![D_544, C_545]: (D_544='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_545, D_544))), inference(splitRight, [status(thm)], [c_6284])).
% 8.90/2.96  tff(c_6527, plain, (![D_13, A_10, B_11, C_12]: (D_13='#skF_8' | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6524])).
% 8.90/2.96  tff(c_6571, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_6527])).
% 8.90/2.96  tff(c_6573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4477, c_6571])).
% 8.90/2.96  tff(c_6574, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_4471])).
% 8.90/2.96  tff(c_6585, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_6574])).
% 8.90/2.96  tff(c_6575, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_4471])).
% 8.90/2.96  tff(c_6580, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6575, c_4472, c_20])).
% 8.90/2.96  tff(c_6829, plain, (![D_583, B_584, A_585, C_586]: (D_583=B_584 | k1_xboole_0=B_584 | k1_xboole_0=A_585 | k2_zfmisc_1(C_586, D_583)!=k2_zfmisc_1(A_585, B_584))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.96  tff(c_7363, plain, (![B_649, D_652, D_654, C_650, C_653, A_651]: (D_654=D_652 | k1_xboole_0=D_652 | k3_zfmisc_1(A_651, B_649, C_653)=k1_xboole_0 | k4_zfmisc_1(A_651, B_649, C_653, D_652)!=k2_zfmisc_1(C_650, D_654))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6829])).
% 8.90/2.96  tff(c_7390, plain, (![D_654, C_650]: (D_654='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_650, D_654))), inference(superposition, [status(thm), theory('equality')], [c_6580, c_7363])).
% 8.90/2.96  tff(c_7417, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7390])).
% 8.90/2.96  tff(c_6586, plain, (![A_551, B_552, C_553]: (k2_zfmisc_1(k2_zfmisc_1(A_551, B_552), C_553)=k3_zfmisc_1(A_551, B_552, C_553))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.90/2.96  tff(c_6595, plain, (![C_553, A_551, B_552]: (k1_xboole_0=C_553 | k2_zfmisc_1(A_551, B_552)=k1_xboole_0 | k3_zfmisc_1(A_551, B_552, C_553)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6586, c_2])).
% 8.90/2.96  tff(c_7454, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7417, c_6595])).
% 8.90/2.96  tff(c_7457, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7454])).
% 8.90/2.96  tff(c_7488, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7457, c_2])).
% 8.90/2.96  tff(c_7490, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_7488])).
% 8.90/2.96  tff(c_7555, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7490, c_18])).
% 8.90/2.96  tff(c_7449, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_7417, c_14])).
% 8.90/2.96  tff(c_7455, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7449])).
% 8.90/2.96  tff(c_7772, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7490, c_7455])).
% 8.90/2.96  tff(c_7773, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7772, c_6580])).
% 8.90/2.96  tff(c_7775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7555, c_7773])).
% 8.90/2.96  tff(c_7776, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7488])).
% 8.90/2.96  tff(c_7801, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7776, c_18])).
% 8.90/2.96  tff(c_8054, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7776, c_7455])).
% 8.90/2.96  tff(c_8055, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8054, c_6580])).
% 8.90/2.96  tff(c_8057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7801, c_8055])).
% 8.90/2.96  tff(c_8058, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7454])).
% 8.90/2.96  tff(c_8081, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8058, c_18])).
% 8.90/2.96  tff(c_8409, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8058, c_7455])).
% 8.90/2.96  tff(c_8410, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8409, c_6580])).
% 8.90/2.96  tff(c_8412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8081, c_8410])).
% 8.90/2.96  tff(c_8413, plain, (![D_654, C_650]: (k1_xboole_0='#skF_4' | D_654='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_650, D_654))), inference(splitRight, [status(thm)], [c_7390])).
% 8.90/2.96  tff(c_8415, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_8413])).
% 8.90/2.96  tff(c_6642, plain, (![A_558, B_559, C_560, D_561]: (k2_zfmisc_1(k3_zfmisc_1(A_558, B_559, C_560), D_561)=k4_zfmisc_1(A_558, B_559, C_560, D_561))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.90/2.96  tff(c_6655, plain, (![A_558, B_559, C_560]: (k4_zfmisc_1(A_558, B_559, C_560, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6642, c_4])).
% 8.90/2.96  tff(c_8433, plain, (![A_558, B_559, C_560]: (k4_zfmisc_1(A_558, B_559, C_560, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8415, c_8415, c_6655])).
% 8.90/2.96  tff(c_8438, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8415, c_18])).
% 8.90/2.96  tff(c_8674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8433, c_8438])).
% 8.90/2.97  tff(c_8676, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_8413])).
% 8.90/2.97  tff(c_6712, plain, (![C_567, A_568, B_569, D_570]: (C_567=A_568 | k1_xboole_0=B_569 | k1_xboole_0=A_568 | k2_zfmisc_1(C_567, D_570)!=k2_zfmisc_1(A_568, B_569))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.97  tff(c_7322, plain, (![A_645, A_644, C_648, B_647, B_643, D_646]: (k3_zfmisc_1(A_645, B_643, C_648)=A_644 | k1_xboole_0=B_647 | k1_xboole_0=A_644 | k4_zfmisc_1(A_645, B_643, C_648, D_646)!=k2_zfmisc_1(A_644, B_647))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6712])).
% 8.90/2.97  tff(c_7404, plain, (![A_655, B_656]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=A_655 | k1_xboole_0=B_656 | k1_xboole_0=A_655 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(A_655, B_656))), inference(superposition, [status(thm), theory('equality')], [c_6580, c_7322])).
% 8.90/2.97  tff(c_7407, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k1_xboole_0=D_13 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7404])).
% 8.90/2.97  tff(c_8879, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_7407])).
% 8.90/2.97  tff(c_8880, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_8676, c_8879])).
% 8.90/2.97  tff(c_8915, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8880])).
% 8.90/2.97  tff(c_8951, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8915, c_6595])).
% 8.90/2.97  tff(c_8954, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8951])).
% 8.90/2.97  tff(c_8985, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8954, c_2])).
% 8.90/2.97  tff(c_8987, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_8985])).
% 8.90/2.97  tff(c_6615, plain, (![B_2, C_553]: (k3_zfmisc_1(k1_xboole_0, B_2, C_553)=k2_zfmisc_1(k1_xboole_0, C_553))), inference(superposition, [status(thm), theory('equality')], [c_6, c_6586])).
% 8.90/2.97  tff(c_6619, plain, (![B_2, C_553]: (k3_zfmisc_1(k1_xboole_0, B_2, C_553)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6615])).
% 8.90/2.97  tff(c_9056, plain, (![B_2, C_553]: (k3_zfmisc_1('#skF_1', B_2, C_553)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8987, c_8987, c_6619])).
% 8.90/2.97  tff(c_8414, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_7390])).
% 8.90/2.97  tff(c_9039, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8987, c_8414])).
% 8.90/2.97  tff(c_9259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9056, c_9039])).
% 8.90/2.97  tff(c_9260, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8985])).
% 8.90/2.97  tff(c_8946, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_8915, c_14])).
% 8.90/2.97  tff(c_8952, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8946])).
% 8.90/2.97  tff(c_9576, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_13)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9260, c_8952])).
% 8.90/2.97  tff(c_9290, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9260, c_18])).
% 8.90/2.97  tff(c_9585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9576, c_9290])).
% 8.90/2.97  tff(c_9586, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8951])).
% 8.90/2.97  tff(c_9593, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9586, c_8414])).
% 8.90/2.97  tff(c_6599, plain, (![A_551, B_552]: (k3_zfmisc_1(A_551, B_552, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6586, c_4])).
% 8.90/2.97  tff(c_9612, plain, (![A_551, B_552]: (k3_zfmisc_1(A_551, B_552, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9586, c_9586, c_6599])).
% 8.90/2.97  tff(c_8800, plain, (![A_757, C_759, C_756, B_755, D_758, D_754]: (k3_zfmisc_1(A_757, B_755, C_759)=C_756 | k1_xboole_0=D_758 | k3_zfmisc_1(A_757, B_755, C_759)=k1_xboole_0 | k4_zfmisc_1(A_757, B_755, C_759, D_758)!=k2_zfmisc_1(C_756, D_754))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6712])).
% 8.90/2.97  tff(c_8827, plain, (![C_756, D_754]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_756 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_756, D_754))), inference(superposition, [status(thm), theory('equality')], [c_6580, c_8800])).
% 8.90/2.97  tff(c_8841, plain, (![C_760, D_761]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_760 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_760, D_761))), inference(negUnitSimplification, [status(thm)], [c_8414, c_8676, c_8827])).
% 8.90/2.97  tff(c_8844, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_8841])).
% 8.90/2.97  tff(c_9812, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_8844])).
% 8.90/2.97  tff(c_9813, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9612, c_9812])).
% 8.90/2.97  tff(c_9815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9593, c_9813])).
% 8.90/2.97  tff(c_9816, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_8880])).
% 8.90/2.97  tff(c_6841, plain, (![D_583, A_7, C_586, B_8, C_9]: (D_583=C_9 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_586, D_583))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6829])).
% 8.90/2.97  tff(c_9840, plain, (![D_583, C_586]: (D_583='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_586, D_583))), inference(superposition, [status(thm), theory('equality')], [c_9816, c_6841])).
% 8.90/2.97  tff(c_10106, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9840])).
% 8.90/2.97  tff(c_10138, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_10106, c_2])).
% 8.90/2.97  tff(c_10140, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_10138])).
% 8.90/2.97  tff(c_10168, plain, (![B_2, C_553]: (k3_zfmisc_1('#skF_1', B_2, C_553)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10140, c_10140, c_6619])).
% 8.90/2.97  tff(c_9817, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8880])).
% 8.90/2.97  tff(c_10148, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10140, c_9817])).
% 8.90/2.97  tff(c_10276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10168, c_10148])).
% 8.90/2.97  tff(c_10277, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_10138])).
% 8.90/2.97  tff(c_10287, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10277, c_9817])).
% 8.90/2.97  tff(c_10129, plain, (![C_9]: (k3_zfmisc_1('#skF_1', '#skF_6', C_9)=k2_zfmisc_1(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_10106, c_12])).
% 8.90/2.97  tff(c_10137, plain, (![C_9]: (k3_zfmisc_1('#skF_1', '#skF_6', C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10129])).
% 8.90/2.97  tff(c_10403, plain, (![C_9]: (k3_zfmisc_1('#skF_1', '#skF_6', C_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10277, c_10137])).
% 8.90/2.97  tff(c_10404, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10403, c_9816])).
% 8.90/2.97  tff(c_10406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10287, c_10404])).
% 8.90/2.97  tff(c_10408, plain, (k2_zfmisc_1('#skF_1', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_9840])).
% 8.90/2.97  tff(c_10407, plain, (![D_583, C_586]: (k1_xboole_0='#skF_7' | D_583='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_586, D_583))), inference(splitRight, [status(thm)], [c_9840])).
% 8.90/2.97  tff(c_10409, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_10407])).
% 8.90/2.97  tff(c_10440, plain, (![A_551, B_552]: (k3_zfmisc_1(A_551, B_552, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10409, c_10409, c_6599])).
% 8.90/2.97  tff(c_10546, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10440, c_9816])).
% 8.90/2.97  tff(c_10418, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10409, c_9817])).
% 8.90/2.97  tff(c_10603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10546, c_10418])).
% 8.90/2.97  tff(c_10606, plain, (![D_867, C_868]: (D_867='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_868, D_867))), inference(splitRight, [status(thm)], [c_10407])).
% 8.90/2.97  tff(c_10612, plain, (![C_9, A_7, B_8]: (C_9='#skF_7' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_10606])).
% 8.90/2.97  tff(c_10622, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_10612])).
% 8.90/2.97  tff(c_10605, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_10407])).
% 8.90/2.97  tff(c_10648, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10622, c_10605])).
% 8.90/2.97  tff(c_10650, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10622, c_9816])).
% 8.90/2.97  tff(c_6724, plain, (![A_7, D_570, C_567, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=C_567 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_567, D_570))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6712])).
% 8.90/2.97  tff(c_10658, plain, (![C_567, D_570]: (k2_zfmisc_1('#skF_1', '#skF_6')=C_567 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_567, D_570))), inference(superposition, [status(thm), theory('equality')], [c_10650, c_6724])).
% 8.90/2.97  tff(c_10843, plain, (![C_885, D_886]: (k2_zfmisc_1('#skF_1', '#skF_6')=C_885 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_885, D_886))), inference(negUnitSimplification, [status(thm)], [c_10408, c_10648, c_10658])).
% 8.90/2.97  tff(c_10849, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=k2_zfmisc_1('#skF_1', '#skF_6') | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_10843])).
% 8.90/2.97  tff(c_10915, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_10849])).
% 8.90/2.97  tff(c_10964, plain, (![C_5, D_6]: (C_5='#skF_1' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10915, c_10])).
% 8.90/2.97  tff(c_11176, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_10964])).
% 8.90/2.97  tff(c_11214, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11176, c_11176, c_6])).
% 8.90/2.97  tff(c_10945, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10915, c_10408])).
% 8.90/2.97  tff(c_11180, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11176, c_10945])).
% 8.90/2.97  tff(c_11300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11214, c_11180])).
% 8.90/2.97  tff(c_11302, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_10964])).
% 8.90/2.97  tff(c_11301, plain, (![C_5, D_6]: (k1_xboole_0='#skF_6' | C_5='#skF_1' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_10964])).
% 8.90/2.97  tff(c_11303, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_11301])).
% 8.90/2.97  tff(c_11341, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11303, c_11303, c_4])).
% 8.90/2.97  tff(c_11347, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11341, c_10915])).
% 8.90/2.97  tff(c_11308, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11303, c_10945])).
% 8.90/2.97  tff(c_11477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11347, c_11308])).
% 8.90/2.97  tff(c_11479, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_11301])).
% 8.90/2.97  tff(c_10958, plain, (![D_6, C_5]: (D_6='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10915, c_8])).
% 8.90/2.97  tff(c_11529, plain, (![D_6, C_5]: (D_6='#skF_6' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_11302, c_11479, c_10958])).
% 8.90/2.97  tff(c_11532, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_11529])).
% 8.90/2.97  tff(c_11534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6585, c_11532])).
% 8.90/2.97  tff(c_11535, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_6574])).
% 8.90/2.97  tff(c_11536, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_6574])).
% 8.90/2.97  tff(c_11537, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11536, c_6580])).
% 8.90/2.97  tff(c_11673, plain, (![D_943, B_944, A_945, C_946]: (D_943=B_944 | k1_xboole_0=B_944 | k1_xboole_0=A_945 | k2_zfmisc_1(C_946, D_943)!=k2_zfmisc_1(A_945, B_944))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.97  tff(c_12323, plain, (![D_1029, B_1026, D_1027, A_1028, C_1030, C_1025]: (D_1029=D_1027 | k1_xboole_0=D_1029 | k3_zfmisc_1(A_1028, B_1026, C_1030)=k1_xboole_0 | k4_zfmisc_1(A_1028, B_1026, C_1030, D_1029)!=k2_zfmisc_1(C_1025, D_1027))), inference(superposition, [status(thm), theory('equality')], [c_14, c_11673])).
% 8.90/2.97  tff(c_12347, plain, (![D_1027, C_1025]: (D_1027='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1025, D_1027))), inference(superposition, [status(thm), theory('equality')], [c_11537, c_12323])).
% 8.90/2.97  tff(c_12459, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12347])).
% 8.90/2.97  tff(c_11542, plain, (![A_927, B_928, C_929]: (k2_zfmisc_1(k2_zfmisc_1(A_927, B_928), C_929)=k3_zfmisc_1(A_927, B_928, C_929))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.90/2.97  tff(c_11551, plain, (![C_929, A_927, B_928]: (k1_xboole_0=C_929 | k2_zfmisc_1(A_927, B_928)=k1_xboole_0 | k3_zfmisc_1(A_927, B_928, C_929)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11542, c_2])).
% 8.90/2.97  tff(c_12497, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12459, c_11551])).
% 8.90/2.97  tff(c_12501, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12497])).
% 8.90/2.97  tff(c_12532, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12501, c_2])).
% 8.90/2.97  tff(c_12534, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_12532])).
% 8.90/2.97  tff(c_12573, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12534, c_18])).
% 8.90/2.97  tff(c_12492, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_12459, c_14])).
% 8.90/2.97  tff(c_12498, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12492])).
% 8.90/2.97  tff(c_12805, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_13)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12534, c_12498])).
% 8.90/2.97  tff(c_12806, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12805, c_11537])).
% 8.90/2.97  tff(c_12808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12573, c_12806])).
% 8.90/2.97  tff(c_12809, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_12532])).
% 8.90/2.97  tff(c_12836, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12809, c_18])).
% 8.90/2.97  tff(c_13125, plain, (![D_13]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_13)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12809, c_12498])).
% 8.90/2.97  tff(c_13126, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13125, c_11537])).
% 8.90/2.97  tff(c_13128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12836, c_13126])).
% 8.90/2.97  tff(c_13129, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_12497])).
% 8.90/2.97  tff(c_13154, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13129, c_18])).
% 8.90/2.97  tff(c_11555, plain, (![A_927, B_928]: (k3_zfmisc_1(A_927, B_928, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11542, c_4])).
% 8.90/2.97  tff(c_11626, plain, (![A_936, B_937, C_938, D_939]: (k2_zfmisc_1(k3_zfmisc_1(A_936, B_937, C_938), D_939)=k4_zfmisc_1(A_936, B_937, C_938, D_939))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.90/2.97  tff(c_11651, plain, (![A_927, B_928, D_939]: (k4_zfmisc_1(A_927, B_928, k1_xboole_0, D_939)=k2_zfmisc_1(k1_xboole_0, D_939))), inference(superposition, [status(thm), theory('equality')], [c_11555, c_11626])).
% 8.90/2.97  tff(c_11660, plain, (![A_927, B_928, D_939]: (k4_zfmisc_1(A_927, B_928, k1_xboole_0, D_939)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11651])).
% 8.90/2.97  tff(c_13147, plain, (![A_927, B_928, D_939]: (k4_zfmisc_1(A_927, B_928, '#skF_7', D_939)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13129, c_13129, c_11660])).
% 8.90/2.97  tff(c_13392, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13147, c_11537])).
% 8.90/2.97  tff(c_13394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13154, c_13392])).
% 8.90/2.97  tff(c_13396, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_12347])).
% 8.90/2.97  tff(c_13395, plain, (![D_1027, C_1025]: (k1_xboole_0='#skF_4' | D_1027='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1025, D_1027))), inference(splitRight, [status(thm)], [c_12347])).
% 8.90/2.97  tff(c_13397, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_13395])).
% 8.90/2.97  tff(c_11639, plain, (![A_936, B_937, C_938]: (k4_zfmisc_1(A_936, B_937, C_938, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11626, c_4])).
% 8.90/2.97  tff(c_13419, plain, (![A_936, B_937, C_938]: (k4_zfmisc_1(A_936, B_937, C_938, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13397, c_13397, c_11639])).
% 8.90/2.97  tff(c_13424, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13397, c_18])).
% 8.90/2.97  tff(c_13605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13419, c_13424])).
% 8.90/2.97  tff(c_13607, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_13395])).
% 8.90/2.97  tff(c_11773, plain, (![C_956, A_957, B_958, D_959]: (C_956=A_957 | k1_xboole_0=B_958 | k1_xboole_0=A_957 | k2_zfmisc_1(C_956, D_959)!=k2_zfmisc_1(A_957, B_958))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/2.97  tff(c_12406, plain, (![D_1042, C_1043, B_1038, C_1039, D_1041, A_1040]: (k3_zfmisc_1(A_1040, B_1038, C_1043)=C_1039 | k1_xboole_0=D_1041 | k3_zfmisc_1(A_1040, B_1038, C_1043)=k1_xboole_0 | k4_zfmisc_1(A_1040, B_1038, C_1043, D_1041)!=k2_zfmisc_1(C_1039, D_1042))), inference(superposition, [status(thm), theory('equality')], [c_14, c_11773])).
% 8.90/2.97  tff(c_12430, plain, (![C_1039, D_1042]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=C_1039 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1039, D_1042))), inference(superposition, [status(thm), theory('equality')], [c_11537, c_12406])).
% 8.90/2.97  tff(c_13712, plain, (![C_1128, D_1129]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=C_1128 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1128, D_1129))), inference(negUnitSimplification, [status(thm)], [c_13396, c_13607, c_12430])).
% 8.90/2.97  tff(c_13715, plain, (![A_10, B_11, C_12, D_13]: (k3_zfmisc_1(A_10, B_11, C_12)=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7') | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_13712])).
% 8.90/2.97  tff(c_13750, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_13715])).
% 8.90/2.97  tff(c_11685, plain, (![A_7, C_946, D_943, B_8, C_9]: (D_943=C_9 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_946, D_943))), inference(superposition, [status(thm), theory('equality')], [c_12, c_11673])).
% 8.90/2.97  tff(c_13856, plain, (![D_943, C_946]: (D_943='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_946, D_943))), inference(superposition, [status(thm), theory('equality')], [c_13750, c_11685])).
% 8.90/2.97  tff(c_14106, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13856])).
% 8.90/2.97  tff(c_14137, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14106, c_2])).
% 8.90/2.97  tff(c_14139, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_14137])).
% 8.90/2.97  tff(c_11571, plain, (![B_2, C_929]: (k3_zfmisc_1(k1_xboole_0, B_2, C_929)=k2_zfmisc_1(k1_xboole_0, C_929))), inference(superposition, [status(thm), theory('equality')], [c_6, c_11542])).
% 8.90/2.97  tff(c_11575, plain, (![B_2, C_929]: (k3_zfmisc_1(k1_xboole_0, B_2, C_929)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11571])).
% 8.90/2.97  tff(c_14171, plain, (![B_2, C_929]: (k3_zfmisc_1('#skF_1', B_2, C_929)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14139, c_14139, c_11575])).
% 8.90/2.97  tff(c_13840, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13750, c_13396])).
% 8.90/2.97  tff(c_14148, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14139, c_13840])).
% 8.90/2.97  tff(c_14324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14171, c_14148])).
% 8.90/2.97  tff(c_14325, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14137])).
% 8.90/2.97  tff(c_11564, plain, (![A_1, C_929]: (k3_zfmisc_1(A_1, k1_xboole_0, C_929)=k2_zfmisc_1(k1_xboole_0, C_929))), inference(superposition, [status(thm), theory('equality')], [c_4, c_11542])).
% 8.90/2.97  tff(c_11574, plain, (![A_1, C_929]: (k3_zfmisc_1(A_1, k1_xboole_0, C_929)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11564])).
% 8.90/2.97  tff(c_14358, plain, (![A_1, C_929]: (k3_zfmisc_1(A_1, '#skF_2', C_929)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14325, c_14325, c_11574])).
% 8.90/2.97  tff(c_14336, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14325, c_13840])).
% 8.90/2.97  tff(c_14547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14358, c_14336])).
% 8.90/2.97  tff(c_14548, plain, (![D_943, C_946]: (k1_xboole_0='#skF_7' | D_943='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_946, D_943))), inference(splitRight, [status(thm)], [c_13856])).
% 8.90/2.97  tff(c_14550, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_14548])).
% 8.90/2.97  tff(c_14559, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14550, c_13840])).
% 8.90/2.97  tff(c_14583, plain, (![A_927, B_928]: (k3_zfmisc_1(A_927, B_928, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14550, c_14550, c_11555])).
% 8.90/2.97  tff(c_14689, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14583, c_13750])).
% 8.90/2.97  tff(c_14773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14559, c_14689])).
% 8.90/2.97  tff(c_14776, plain, (![D_1197, C_1198]: (D_1197='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_1198, D_1197))), inference(splitRight, [status(thm)], [c_14548])).
% 8.90/2.97  tff(c_14782, plain, (![C_9, A_7, B_8]: (C_9='#skF_7' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_14776])).
% 8.90/2.97  tff(c_14792, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_14782])).
% 8.90/2.97  tff(c_14794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11535, c_14792])).
% 8.90/2.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.90/2.97  
% 8.90/2.97  Inference rules
% 8.90/2.97  ----------------------
% 8.90/2.97  #Ref     : 48
% 8.90/2.97  #Sup     : 3563
% 8.90/2.97  #Fact    : 0
% 8.90/2.97  #Define  : 0
% 8.90/2.97  #Split   : 38
% 8.90/2.97  #Chain   : 0
% 8.90/2.97  #Close   : 0
% 8.90/2.97  
% 8.90/2.97  Ordering : KBO
% 8.90/2.97  
% 8.90/2.97  Simplification rules
% 8.90/2.97  ----------------------
% 8.90/2.97  #Subsume      : 917
% 8.90/2.97  #Demod        : 3591
% 8.90/2.97  #Tautology    : 1495
% 8.90/2.97  #SimpNegUnit  : 213
% 8.90/2.97  #BackRed      : 1088
% 8.90/2.97  
% 8.90/2.97  #Partial instantiations: 0
% 8.90/2.97  #Strategies tried      : 1
% 8.90/2.97  
% 8.90/2.97  Timing (in seconds)
% 8.90/2.97  ----------------------
% 8.90/2.97  Preprocessing        : 0.29
% 8.90/2.97  Parsing              : 0.16
% 8.90/2.97  CNF conversion       : 0.02
% 8.90/2.97  Main loop            : 1.77
% 8.90/2.97  Inferencing          : 0.56
% 8.90/2.97  Reduction            : 0.59
% 8.90/2.97  Demodulation         : 0.41
% 8.90/2.97  BG Simplification    : 0.08
% 8.90/2.97  Subsumption          : 0.40
% 8.90/2.97  Abstraction          : 0.10
% 8.90/2.97  MUC search           : 0.00
% 8.90/2.97  Cooper               : 0.00
% 8.90/2.97  Total                : 2.17
% 8.90/2.97  Index Insertion      : 0.00
% 8.90/2.97  Index Deletion       : 0.00
% 8.90/2.97  Index Matching       : 0.00
% 8.90/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
