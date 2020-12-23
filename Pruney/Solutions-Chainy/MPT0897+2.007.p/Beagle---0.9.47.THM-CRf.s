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
% DateTime   : Thu Dec  3 10:09:48 EST 2020

% Result     : Theorem 6.49s
% Output     : CNFRefutation 6.91s
% Verified   : 
% Statistics : Number of formulae       :  190 (9824 expanded)
%              Number of leaves         :   20 (3150 expanded)
%              Depth                    :   31
%              Number of atoms          :  307 (18361 expanded)
%              Number of equality atoms :  298 (18352 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_20,B_21,C_22] : k2_zfmisc_1(k2_zfmisc_1(A_20,B_21),C_22) = k3_zfmisc_1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_20,B_21,C_22,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_20,B_21),C_22,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_20,B_21,C_22),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_8])).

tff(c_321,plain,(
    ! [A_20,B_21,C_22,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_20,B_21),C_22,C_5) = k4_zfmisc_1(A_20,B_21,C_22,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_60])).

tff(c_20,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_415,plain,(
    ! [C_73,A_70,B_68,F_72,E_69,D_71] :
      ( E_69 = B_68
      | k3_zfmisc_1(A_70,B_68,C_73) = k1_xboole_0
      | k3_zfmisc_1(D_71,E_69,F_72) != k3_zfmisc_1(A_70,B_68,C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_421,plain,(
    ! [C_22,A_20,B_21,F_72,C_5,E_69,D_71] :
      ( E_69 = C_22
      | k3_zfmisc_1(k2_zfmisc_1(A_20,B_21),C_22,C_5) = k1_xboole_0
      | k4_zfmisc_1(A_20,B_21,C_22,C_5) != k3_zfmisc_1(D_71,E_69,F_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_415])).

tff(c_776,plain,(
    ! [C_110,E_115,F_112,D_111,B_113,C_116,A_114] :
      ( E_115 = C_110
      | k4_zfmisc_1(A_114,B_113,C_110,C_116) = k1_xboole_0
      | k4_zfmisc_1(A_114,B_113,C_110,C_116) != k3_zfmisc_1(D_111,E_115,F_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_421])).

tff(c_806,plain,(
    ! [E_115,D_111,F_112] :
      ( E_115 = '#skF_7'
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_111,E_115,F_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_776])).

tff(c_819,plain,(
    ! [E_115,D_111,F_112] :
      ( E_115 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_111,E_115,F_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_806])).

tff(c_821,plain,(
    ! [E_117,D_118,F_119] :
      ( E_117 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_118,E_117,F_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_819])).

tff(c_827,plain,(
    ! [C_22,A_20,B_21,C_5] :
      ( C_22 = '#skF_7'
      | k4_zfmisc_1(A_20,B_21,C_22,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_821])).

tff(c_839,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_827])).

tff(c_866,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_22])).

tff(c_322,plain,(
    ! [A_60,B_61,C_62,C_63] : k3_zfmisc_1(k2_zfmisc_1(A_60,B_61),C_62,C_63) = k4_zfmisc_1(A_60,B_61,C_62,C_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_60])).

tff(c_12,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( F_15 = C_12
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,(
    ! [A_60,C_62,C_63,F_15,E_14,B_61,D_13] :
      ( F_15 = C_63
      | k3_zfmisc_1(k2_zfmisc_1(A_60,B_61),C_62,C_63) = k1_xboole_0
      | k4_zfmisc_1(A_60,B_61,C_62,C_63) != k3_zfmisc_1(D_13,E_14,F_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_12])).

tff(c_932,plain,(
    ! [B_133,C_132,E_134,D_136,F_137,C_131,A_135] :
      ( F_137 = C_132
      | k4_zfmisc_1(A_135,B_133,C_131,C_132) = k1_xboole_0
      | k4_zfmisc_1(A_135,B_133,C_131,C_132) != k3_zfmisc_1(D_136,E_134,F_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_334])).

tff(c_935,plain,(
    ! [F_137,D_136,E_134] :
      ( F_137 = '#skF_8'
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_136,E_134,F_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_932])).

tff(c_969,plain,(
    ! [F_137,D_136,E_134] :
      ( F_137 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_136,E_134,F_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_935])).

tff(c_977,plain,(
    ! [F_138,D_139,E_140] :
      ( F_138 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_139,E_140,F_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_969])).

tff(c_983,plain,(
    ! [C_5,A_20,B_21,C_22] :
      ( C_5 = '#skF_8'
      | k4_zfmisc_1(A_20,B_21,C_22,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_977])).

tff(c_995,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_983])).

tff(c_1054,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_866])).

tff(c_16,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( D_13 = A_10
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_340,plain,(
    ! [A_60,C_62,C_63,F_15,E_14,B_61,D_13] :
      ( k2_zfmisc_1(A_60,B_61) = D_13
      | k3_zfmisc_1(k2_zfmisc_1(A_60,B_61),C_62,C_63) = k1_xboole_0
      | k4_zfmisc_1(A_60,B_61,C_62,C_63) != k3_zfmisc_1(D_13,E_14,F_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_16])).

tff(c_1415,plain,(
    ! [B_203,A_205,C_202,F_207,C_201,E_204,D_206] :
      ( k2_zfmisc_1(A_205,B_203) = D_206
      | k4_zfmisc_1(A_205,B_203,C_201,C_202) = k1_xboole_0
      | k4_zfmisc_1(A_205,B_203,C_201,C_202) != k3_zfmisc_1(D_206,E_204,F_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_340])).

tff(c_1418,plain,(
    ! [D_206,E_204,F_207] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_206
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_206,E_204,F_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_1415])).

tff(c_1452,plain,(
    ! [D_206,E_204,F_207] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_206
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_206,E_204,F_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_1418])).

tff(c_1460,plain,(
    ! [D_208,E_209,F_210] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_208
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_208,E_209,F_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1452])).

tff(c_1466,plain,(
    ! [A_20,B_21,C_22,C_5] :
      ( k2_zfmisc_1(A_20,B_21) = k2_zfmisc_1('#skF_5','#skF_6')
      | k4_zfmisc_1(A_20,B_21,C_22,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_1460])).

tff(c_1478,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1466])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1521,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_2])).

tff(c_1544,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1521])).

tff(c_18,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_1518,plain,(
    ! [C_5] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_5) = k3_zfmisc_1('#skF_5','#skF_6',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_8])).

tff(c_1545,plain,(
    ! [C_218] : k3_zfmisc_1('#skF_5','#skF_6',C_218) = k3_zfmisc_1('#skF_1','#skF_2',C_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1518])).

tff(c_1605,plain,(
    ! [A_10,B_11,C_12,C_218] :
      ( A_10 = '#skF_5'
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(A_10,B_11,C_12) != k3_zfmisc_1('#skF_1','#skF_2',C_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_16])).

tff(c_2112,plain,(
    ! [C_218] :
      ( '#skF_5' = '#skF_1'
      | k3_zfmisc_1('#skF_1','#skF_2',C_218) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1605])).

tff(c_2113,plain,(
    ! [C_218] : k3_zfmisc_1('#skF_1','#skF_2',C_218) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2112])).

tff(c_66,plain,(
    ! [C_22,A_20,B_21] :
      ( k1_xboole_0 = C_22
      | k2_zfmisc_1(A_20,B_21) = k1_xboole_0
      | k3_zfmisc_1(A_20,B_21,C_22) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_1596,plain,(
    ! [C_218] :
      ( k1_xboole_0 = C_218
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2',C_218) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_66])).

tff(c_1632,plain,(
    ! [C_218] :
      ( k1_xboole_0 = C_218
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2',C_218) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_1596])).

tff(c_1633,plain,(
    ! [C_218] :
      ( k1_xboole_0 = C_218
      | k3_zfmisc_1('#skF_1','#skF_2',C_218) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1544,c_1632])).

tff(c_2244,plain,(
    ! [C_252] : k1_xboole_0 = C_252 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2113,c_1633])).

tff(c_1526,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_5','#skF_6',C_5) = k3_zfmisc_1('#skF_1','#skF_2',C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1518])).

tff(c_14,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( E_14 = B_11
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1593,plain,(
    ! [E_14,C_218,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k3_zfmisc_1('#skF_5','#skF_6',C_218) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_14])).

tff(c_1631,plain,(
    ! [E_14,C_218,D_13,F_15] :
      ( E_14 = '#skF_6'
      | k3_zfmisc_1('#skF_1','#skF_2',C_218) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1('#skF_1','#skF_2',C_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1526,c_1593])).

tff(c_1777,plain,(
    ! [C_218] :
      ( '#skF_6' = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_2',C_218) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1631])).

tff(c_1803,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1777])).

tff(c_1808,plain,(
    k2_zfmisc_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1803,c_1478])).

tff(c_2276,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_1808])).

tff(c_2362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1544,c_2276])).

tff(c_2363,plain,(
    ! [C_218] : k3_zfmisc_1('#skF_1','#skF_2',C_218) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1777])).

tff(c_2462,plain,(
    ! [C_497] : k1_xboole_0 = C_497 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_1633])).

tff(c_2576,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2462,c_1544])).

tff(c_2577,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1521])).

tff(c_2579,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2577])).

tff(c_2604,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_20])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_1,C_22] : k3_zfmisc_1(A_1,k1_xboole_0,C_22) = k2_zfmisc_1(k1_xboole_0,C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_89,plain,(
    ! [A_1,C_22] : k3_zfmisc_1(A_1,k1_xboole_0,C_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_79])).

tff(c_141,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_zfmisc_1(k3_zfmisc_1(A_29,B_30,C_31),D_32) = k4_zfmisc_1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [A_1,C_22,D_32] : k4_zfmisc_1(A_1,k1_xboole_0,C_22,D_32) = k2_zfmisc_1(k1_xboole_0,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_141])).

tff(c_174,plain,(
    ! [A_1,C_22,D_32] : k4_zfmisc_1(A_1,k1_xboole_0,C_22,D_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_163])).

tff(c_2595,plain,(
    ! [A_1,C_22,D_32] : k4_zfmisc_1(A_1,'#skF_6',C_22,D_32) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_2579,c_174])).

tff(c_2977,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2595,c_1054])).

tff(c_2979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2604,c_2977])).

tff(c_2980,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2577])).

tff(c_3007,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2980,c_20])).

tff(c_86,plain,(
    ! [B_2,C_22] : k3_zfmisc_1(k1_xboole_0,B_2,C_22) = k2_zfmisc_1(k1_xboole_0,C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_90,plain,(
    ! [B_2,C_22] : k3_zfmisc_1(k1_xboole_0,B_2,C_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_86])).

tff(c_160,plain,(
    ! [B_2,C_22,D_32] : k4_zfmisc_1(k1_xboole_0,B_2,C_22,D_32) = k2_zfmisc_1(k1_xboole_0,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_141])).

tff(c_173,plain,(
    ! [B_2,C_22,D_32] : k4_zfmisc_1(k1_xboole_0,B_2,C_22,D_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_160])).

tff(c_3000,plain,(
    ! [B_2,C_22,D_32] : k4_zfmisc_1('#skF_5',B_2,C_22,D_32) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2980,c_2980,c_173])).

tff(c_3384,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3000,c_1054])).

tff(c_3386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3007,c_3384])).

tff(c_3387,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_3393,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3387])).

tff(c_3399,plain,(
    ! [A_763,B_764,C_765] : k2_zfmisc_1(k2_zfmisc_1(A_763,B_764),C_765) = k3_zfmisc_1(A_763,B_764,C_765) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3402,plain,(
    ! [A_763,B_764,C_765,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_763,B_764),C_765,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_763,B_764,C_765),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_8])).

tff(c_3633,plain,(
    ! [A_763,B_764,C_765,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_763,B_764),C_765,C_5) = k4_zfmisc_1(A_763,B_764,C_765,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3402])).

tff(c_3388,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_3394,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3388,c_22])).

tff(c_3753,plain,(
    ! [D_814,E_812,A_813,B_811,F_815,C_816] :
      ( F_815 = C_816
      | k3_zfmisc_1(A_813,B_811,C_816) = k1_xboole_0
      | k3_zfmisc_1(D_814,E_812,F_815) != k3_zfmisc_1(A_813,B_811,C_816) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3759,plain,(
    ! [D_814,E_812,C_765,F_815,C_5,B_764,A_763] :
      ( F_815 = C_5
      | k3_zfmisc_1(k2_zfmisc_1(A_763,B_764),C_765,C_5) = k1_xboole_0
      | k4_zfmisc_1(A_763,B_764,C_765,C_5) != k3_zfmisc_1(D_814,E_812,F_815) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3633,c_3753])).

tff(c_4115,plain,(
    ! [D_858,E_855,C_853,B_856,A_854,F_857,C_859] :
      ( F_857 = C_859
      | k4_zfmisc_1(A_854,B_856,C_853,C_859) = k1_xboole_0
      | k4_zfmisc_1(A_854,B_856,C_853,C_859) != k3_zfmisc_1(D_858,E_855,F_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3633,c_3759])).

tff(c_4151,plain,(
    ! [F_857,D_858,E_855] :
      ( F_857 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_858,E_855,F_857) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3394,c_4115])).

tff(c_4158,plain,(
    ! [F_857,D_858,E_855] :
      ( F_857 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_858,E_855,F_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3394,c_4151])).

tff(c_4160,plain,(
    ! [F_860,D_861,E_862] :
      ( F_860 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_861,E_862,F_860) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_4158])).

tff(c_4166,plain,(
    ! [C_5,A_763,B_764,C_765] :
      ( C_5 = '#skF_8'
      | k4_zfmisc_1(A_763,B_764,C_765,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3633,c_4160])).

tff(c_4178,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4166])).

tff(c_4180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3393,c_4178])).

tff(c_4181,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3387])).

tff(c_4187,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4181])).

tff(c_4188,plain,(
    ! [A_863,B_864,C_865] : k2_zfmisc_1(k2_zfmisc_1(A_863,B_864),C_865) = k3_zfmisc_1(A_863,B_864,C_865) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4191,plain,(
    ! [A_863,B_864,C_865,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_863,B_864),C_865,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_863,B_864,C_865),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_4188,c_8])).

tff(c_4453,plain,(
    ! [A_863,B_864,C_865,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_863,B_864),C_865,C_5) = k4_zfmisc_1(A_863,B_864,C_865,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4191])).

tff(c_4182,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3387])).

tff(c_4229,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4182,c_3388,c_22])).

tff(c_4547,plain,(
    ! [E_912,D_914,F_915,B_911,A_913,C_916] :
      ( E_912 = B_911
      | k3_zfmisc_1(A_913,B_911,C_916) = k1_xboole_0
      | k3_zfmisc_1(D_914,E_912,F_915) != k3_zfmisc_1(A_913,B_911,C_916) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4553,plain,(
    ! [E_912,D_914,F_915,A_863,C_5,C_865,B_864] :
      ( E_912 = C_865
      | k3_zfmisc_1(k2_zfmisc_1(A_863,B_864),C_865,C_5) = k1_xboole_0
      | k4_zfmisc_1(A_863,B_864,C_865,C_5) != k3_zfmisc_1(D_914,E_912,F_915) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4453,c_4547])).

tff(c_5000,plain,(
    ! [C_975,B_974,C_969,D_972,A_970,F_971,E_973] :
      ( E_973 = C_969
      | k4_zfmisc_1(A_970,B_974,C_969,C_975) = k1_xboole_0
      | k4_zfmisc_1(A_970,B_974,C_969,C_975) != k3_zfmisc_1(D_972,E_973,F_971) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4453,c_4553])).

tff(c_5033,plain,(
    ! [E_973,D_972,F_971] :
      ( E_973 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_972,E_973,F_971) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4229,c_5000])).

tff(c_5043,plain,(
    ! [E_973,D_972,F_971] :
      ( E_973 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_972,E_973,F_971) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4229,c_5033])).

tff(c_5045,plain,(
    ! [E_976,D_977,F_978] :
      ( E_976 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_977,E_976,F_978) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_5043])).

tff(c_5051,plain,(
    ! [C_865,A_863,B_864,C_5] :
      ( C_865 = '#skF_7'
      | k4_zfmisc_1(A_863,B_864,C_865,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4453,c_5045])).

tff(c_5063,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5051])).

tff(c_5136,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5063,c_4229])).

tff(c_4454,plain,(
    ! [A_903,B_904,C_905,C_906] : k3_zfmisc_1(k2_zfmisc_1(A_903,B_904),C_905,C_906) = k4_zfmisc_1(A_903,B_904,C_905,C_906) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4191])).

tff(c_4472,plain,(
    ! [C_905,A_903,C_906,F_15,E_14,D_13,B_904] :
      ( k2_zfmisc_1(A_903,B_904) = D_13
      | k3_zfmisc_1(k2_zfmisc_1(A_903,B_904),C_905,C_906) = k1_xboole_0
      | k4_zfmisc_1(A_903,B_904,C_905,C_906) != k3_zfmisc_1(D_13,E_14,F_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4454,c_16])).

tff(c_5476,plain,(
    ! [D_1042,B_1038,C_1039,E_1041,F_1043,C_1037,A_1040] :
      ( k2_zfmisc_1(A_1040,B_1038) = D_1042
      | k4_zfmisc_1(A_1040,B_1038,C_1037,C_1039) = k1_xboole_0
      | k4_zfmisc_1(A_1040,B_1038,C_1037,C_1039) != k3_zfmisc_1(D_1042,E_1041,F_1043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4453,c_4472])).

tff(c_5479,plain,(
    ! [D_1042,E_1041,F_1043] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1042
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1042,E_1041,F_1043) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5136,c_5476])).

tff(c_5513,plain,(
    ! [D_1042,E_1041,F_1043] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1042
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1042,E_1041,F_1043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5136,c_5479])).

tff(c_5521,plain,(
    ! [D_1044,E_1045,F_1046] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1044
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1044,E_1045,F_1046) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_5513])).

tff(c_5527,plain,(
    ! [A_863,B_864,C_865,C_5] :
      ( k2_zfmisc_1(A_863,B_864) = k2_zfmisc_1('#skF_1','#skF_6')
      | k4_zfmisc_1(A_863,B_864,C_865,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4453,c_5521])).

tff(c_5539,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5527])).

tff(c_5579,plain,(
    ! [C_5] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_5) = k3_zfmisc_1('#skF_1','#skF_6',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_5539,c_8])).

tff(c_5606,plain,(
    ! [C_1054] : k3_zfmisc_1('#skF_1','#skF_6',C_1054) = k3_zfmisc_1('#skF_1','#skF_2',C_1054) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5579])).

tff(c_5651,plain,(
    ! [B_11,A_10,C_12,C_1054] :
      ( B_11 = '#skF_6'
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(A_10,B_11,C_12) != k3_zfmisc_1('#skF_1','#skF_2',C_1054) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5606,c_14])).

tff(c_5838,plain,(
    ! [C_1054] :
      ( '#skF_6' = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_2',C_1054) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5651])).

tff(c_5839,plain,(
    ! [C_1054] : k3_zfmisc_1('#skF_1','#skF_2',C_1054) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4187,c_5838])).

tff(c_5582,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5539,c_2])).

tff(c_5605,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5582])).

tff(c_4197,plain,(
    ! [C_865,A_863,B_864] :
      ( k1_xboole_0 = C_865
      | k2_zfmisc_1(A_863,B_864) = k1_xboole_0
      | k3_zfmisc_1(A_863,B_864,C_865) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4188,c_2])).

tff(c_5657,plain,(
    ! [C_1054] :
      ( k1_xboole_0 = C_1054
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2',C_1054) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5606,c_4197])).

tff(c_5693,plain,(
    ! [C_1054] :
      ( k1_xboole_0 = C_1054
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2',C_1054) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5539,c_5657])).

tff(c_5694,plain,(
    ! [C_1054] :
      ( k1_xboole_0 = C_1054
      | k3_zfmisc_1('#skF_1','#skF_2',C_1054) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_5605,c_5693])).

tff(c_5966,plain,(
    ! [C_1069] : k1_xboole_0 = C_1069 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5839,c_5694])).

tff(c_6080,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5966,c_5605])).

tff(c_6081,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5582])).

tff(c_6084,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6081])).

tff(c_6108,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6084,c_20])).

tff(c_4210,plain,(
    ! [A_1,C_865] : k3_zfmisc_1(A_1,k1_xboole_0,C_865) = k2_zfmisc_1(k1_xboole_0,C_865) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4188])).

tff(c_4220,plain,(
    ! [A_1,C_865] : k3_zfmisc_1(A_1,k1_xboole_0,C_865) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4210])).

tff(c_4273,plain,(
    ! [A_872,B_873,C_874,D_875] : k2_zfmisc_1(k3_zfmisc_1(A_872,B_873,C_874),D_875) = k4_zfmisc_1(A_872,B_873,C_874,D_875) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4292,plain,(
    ! [A_1,C_865,D_875] : k4_zfmisc_1(A_1,k1_xboole_0,C_865,D_875) = k2_zfmisc_1(k1_xboole_0,D_875) ),
    inference(superposition,[status(thm),theory(equality)],[c_4220,c_4273])).

tff(c_4305,plain,(
    ! [A_1,C_865,D_875] : k4_zfmisc_1(A_1,k1_xboole_0,C_865,D_875) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4292])).

tff(c_6101,plain,(
    ! [A_1,C_865,D_875] : k4_zfmisc_1(A_1,'#skF_6',C_865,D_875) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6084,c_6084,c_4305])).

tff(c_6480,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6101,c_5136])).

tff(c_6482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6108,c_6480])).

tff(c_6483,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6081])).

tff(c_4217,plain,(
    ! [B_2,C_865] : k3_zfmisc_1(k1_xboole_0,B_2,C_865) = k2_zfmisc_1(k1_xboole_0,C_865) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4188])).

tff(c_4221,plain,(
    ! [B_2,C_865] : k3_zfmisc_1(k1_xboole_0,B_2,C_865) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4217])).

tff(c_4295,plain,(
    ! [B_2,C_865,D_875] : k4_zfmisc_1(k1_xboole_0,B_2,C_865,D_875) = k2_zfmisc_1(k1_xboole_0,D_875) ),
    inference(superposition,[status(thm),theory(equality)],[c_4221,c_4273])).

tff(c_4306,plain,(
    ! [B_2,C_865,D_875] : k4_zfmisc_1(k1_xboole_0,B_2,C_865,D_875) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4295])).

tff(c_6500,plain,(
    ! [B_2,C_865,D_875] : k4_zfmisc_1('#skF_1',B_2,C_865,D_875) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6483,c_6483,c_4306])).

tff(c_6510,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6483,c_20])).

tff(c_6909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6500,c_6510])).

tff(c_6910,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4181])).

tff(c_6916,plain,(
    ! [A_1335,B_1336,C_1337] : k2_zfmisc_1(k2_zfmisc_1(A_1335,B_1336),C_1337) = k3_zfmisc_1(A_1335,B_1336,C_1337) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6919,plain,(
    ! [A_1335,B_1336,C_1337,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_1335,B_1336),C_1337,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_1335,B_1336,C_1337),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6916,c_8])).

tff(c_7181,plain,(
    ! [A_1335,B_1336,C_1337,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_1335,B_1336),C_1337,C_5) = k4_zfmisc_1(A_1335,B_1336,C_1337,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6919])).

tff(c_6911,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4181])).

tff(c_6957,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6911,c_3388,c_4182,c_22])).

tff(c_7182,plain,(
    ! [A_1375,B_1376,C_1377,C_1378] : k3_zfmisc_1(k2_zfmisc_1(A_1375,B_1376),C_1377,C_1378) = k4_zfmisc_1(A_1375,B_1376,C_1377,C_1378) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6919])).

tff(c_7200,plain,(
    ! [B_1376,C_1377,F_15,A_1375,E_14,C_1378,D_13] :
      ( E_14 = C_1377
      | k3_zfmisc_1(k2_zfmisc_1(A_1375,B_1376),C_1377,C_1378) = k1_xboole_0
      | k4_zfmisc_1(A_1375,B_1376,C_1377,C_1378) != k3_zfmisc_1(D_13,E_14,F_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7182,c_14])).

tff(c_7593,plain,(
    ! [F_1425,D_1423,A_1420,C_1419,E_1421,C_1422,B_1424] :
      ( E_1421 = C_1419
      | k4_zfmisc_1(A_1420,B_1424,C_1419,C_1422) = k1_xboole_0
      | k4_zfmisc_1(A_1420,B_1424,C_1419,C_1422) != k3_zfmisc_1(D_1423,E_1421,F_1425) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7181,c_7200])).

tff(c_7626,plain,(
    ! [E_1421,D_1423,F_1425] :
      ( E_1421 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1423,E_1421,F_1425) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6957,c_7593])).

tff(c_7636,plain,(
    ! [E_1421,D_1423,F_1425] :
      ( E_1421 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1423,E_1421,F_1425) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6957,c_7626])).

tff(c_7638,plain,(
    ! [E_1426,D_1427,F_1428] :
      ( E_1426 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1427,E_1426,F_1428) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_7636])).

tff(c_7644,plain,(
    ! [C_1337,A_1335,B_1336,C_5] :
      ( C_1337 = '#skF_7'
      | k4_zfmisc_1(A_1335,B_1336,C_1337,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7181,c_7638])).

tff(c_7656,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7644])).

tff(c_7658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6910,c_7656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.49/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.40  
% 6.91/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.41  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 6.91/2.41  
% 6.91/2.41  %Foreground sorts:
% 6.91/2.41  
% 6.91/2.41  
% 6.91/2.41  %Background operators:
% 6.91/2.41  
% 6.91/2.41  
% 6.91/2.41  %Foreground operators:
% 6.91/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.91/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.91/2.41  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 6.91/2.41  tff('#skF_7', type, '#skF_7': $i).
% 6.91/2.41  tff('#skF_5', type, '#skF_5': $i).
% 6.91/2.41  tff('#skF_6', type, '#skF_6': $i).
% 6.91/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.91/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.91/2.41  tff('#skF_1', type, '#skF_1': $i).
% 6.91/2.41  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.91/2.41  tff('#skF_8', type, '#skF_8': $i).
% 6.91/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.91/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.91/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.91/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.91/2.41  
% 6.91/2.43  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 6.91/2.43  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 6.91/2.43  tff(f_58, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 6.91/2.43  tff(f_45, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 6.91/2.43  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.91/2.43  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.91/2.43  tff(c_57, plain, (![A_20, B_21, C_22]: (k2_zfmisc_1(k2_zfmisc_1(A_20, B_21), C_22)=k3_zfmisc_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.91/2.43  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.91/2.43  tff(c_60, plain, (![A_20, B_21, C_22, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_20, B_21), C_22, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_20, B_21, C_22), C_5))), inference(superposition, [status(thm), theory('equality')], [c_57, c_8])).
% 6.91/2.43  tff(c_321, plain, (![A_20, B_21, C_22, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_20, B_21), C_22, C_5)=k4_zfmisc_1(A_20, B_21, C_22, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_60])).
% 6.91/2.43  tff(c_20, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.91/2.43  tff(c_22, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.91/2.43  tff(c_415, plain, (![C_73, A_70, B_68, F_72, E_69, D_71]: (E_69=B_68 | k3_zfmisc_1(A_70, B_68, C_73)=k1_xboole_0 | k3_zfmisc_1(D_71, E_69, F_72)!=k3_zfmisc_1(A_70, B_68, C_73))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.91/2.43  tff(c_421, plain, (![C_22, A_20, B_21, F_72, C_5, E_69, D_71]: (E_69=C_22 | k3_zfmisc_1(k2_zfmisc_1(A_20, B_21), C_22, C_5)=k1_xboole_0 | k4_zfmisc_1(A_20, B_21, C_22, C_5)!=k3_zfmisc_1(D_71, E_69, F_72))), inference(superposition, [status(thm), theory('equality')], [c_321, c_415])).
% 6.91/2.43  tff(c_776, plain, (![C_110, E_115, F_112, D_111, B_113, C_116, A_114]: (E_115=C_110 | k4_zfmisc_1(A_114, B_113, C_110, C_116)=k1_xboole_0 | k4_zfmisc_1(A_114, B_113, C_110, C_116)!=k3_zfmisc_1(D_111, E_115, F_112))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_421])).
% 6.91/2.43  tff(c_806, plain, (![E_115, D_111, F_112]: (E_115='#skF_7' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_111, E_115, F_112))), inference(superposition, [status(thm), theory('equality')], [c_22, c_776])).
% 6.91/2.43  tff(c_819, plain, (![E_115, D_111, F_112]: (E_115='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_111, E_115, F_112))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_806])).
% 6.91/2.43  tff(c_821, plain, (![E_117, D_118, F_119]: (E_117='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_118, E_117, F_119))), inference(negUnitSimplification, [status(thm)], [c_20, c_819])).
% 6.91/2.43  tff(c_827, plain, (![C_22, A_20, B_21, C_5]: (C_22='#skF_7' | k4_zfmisc_1(A_20, B_21, C_22, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_321, c_821])).
% 6.91/2.43  tff(c_839, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_827])).
% 6.91/2.43  tff(c_866, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_22])).
% 6.91/2.43  tff(c_322, plain, (![A_60, B_61, C_62, C_63]: (k3_zfmisc_1(k2_zfmisc_1(A_60, B_61), C_62, C_63)=k4_zfmisc_1(A_60, B_61, C_62, C_63))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_60])).
% 6.91/2.43  tff(c_12, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (F_15=C_12 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.91/2.43  tff(c_334, plain, (![A_60, C_62, C_63, F_15, E_14, B_61, D_13]: (F_15=C_63 | k3_zfmisc_1(k2_zfmisc_1(A_60, B_61), C_62, C_63)=k1_xboole_0 | k4_zfmisc_1(A_60, B_61, C_62, C_63)!=k3_zfmisc_1(D_13, E_14, F_15))), inference(superposition, [status(thm), theory('equality')], [c_322, c_12])).
% 6.91/2.43  tff(c_932, plain, (![B_133, C_132, E_134, D_136, F_137, C_131, A_135]: (F_137=C_132 | k4_zfmisc_1(A_135, B_133, C_131, C_132)=k1_xboole_0 | k4_zfmisc_1(A_135, B_133, C_131, C_132)!=k3_zfmisc_1(D_136, E_134, F_137))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_334])).
% 6.91/2.43  tff(c_935, plain, (![F_137, D_136, E_134]: (F_137='#skF_8' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_136, E_134, F_137))), inference(superposition, [status(thm), theory('equality')], [c_866, c_932])).
% 6.91/2.43  tff(c_969, plain, (![F_137, D_136, E_134]: (F_137='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_136, E_134, F_137))), inference(demodulation, [status(thm), theory('equality')], [c_866, c_935])).
% 6.91/2.43  tff(c_977, plain, (![F_138, D_139, E_140]: (F_138='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_139, E_140, F_138))), inference(negUnitSimplification, [status(thm)], [c_20, c_969])).
% 6.91/2.43  tff(c_983, plain, (![C_5, A_20, B_21, C_22]: (C_5='#skF_8' | k4_zfmisc_1(A_20, B_21, C_22, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_321, c_977])).
% 6.91/2.43  tff(c_995, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_983])).
% 6.91/2.43  tff(c_1054, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_995, c_866])).
% 6.91/2.43  tff(c_16, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (D_13=A_10 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.91/2.43  tff(c_340, plain, (![A_60, C_62, C_63, F_15, E_14, B_61, D_13]: (k2_zfmisc_1(A_60, B_61)=D_13 | k3_zfmisc_1(k2_zfmisc_1(A_60, B_61), C_62, C_63)=k1_xboole_0 | k4_zfmisc_1(A_60, B_61, C_62, C_63)!=k3_zfmisc_1(D_13, E_14, F_15))), inference(superposition, [status(thm), theory('equality')], [c_322, c_16])).
% 6.91/2.43  tff(c_1415, plain, (![B_203, A_205, C_202, F_207, C_201, E_204, D_206]: (k2_zfmisc_1(A_205, B_203)=D_206 | k4_zfmisc_1(A_205, B_203, C_201, C_202)=k1_xboole_0 | k4_zfmisc_1(A_205, B_203, C_201, C_202)!=k3_zfmisc_1(D_206, E_204, F_207))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_340])).
% 6.91/2.43  tff(c_1418, plain, (![D_206, E_204, F_207]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_206 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_206, E_204, F_207))), inference(superposition, [status(thm), theory('equality')], [c_1054, c_1415])).
% 6.91/2.43  tff(c_1452, plain, (![D_206, E_204, F_207]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_206 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_206, E_204, F_207))), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_1418])).
% 6.91/2.43  tff(c_1460, plain, (![D_208, E_209, F_210]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_208 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_208, E_209, F_210))), inference(negUnitSimplification, [status(thm)], [c_20, c_1452])).
% 6.91/2.43  tff(c_1466, plain, (![A_20, B_21, C_22, C_5]: (k2_zfmisc_1(A_20, B_21)=k2_zfmisc_1('#skF_5', '#skF_6') | k4_zfmisc_1(A_20, B_21, C_22, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_321, c_1460])).
% 6.91/2.43  tff(c_1478, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_1466])).
% 6.91/2.43  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.91/2.43  tff(c_1521, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1478, c_2])).
% 6.91/2.43  tff(c_1544, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1521])).
% 6.91/2.43  tff(c_18, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.91/2.43  tff(c_56, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_18])).
% 6.91/2.43  tff(c_1518, plain, (![C_5]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_5)=k3_zfmisc_1('#skF_5', '#skF_6', C_5))), inference(superposition, [status(thm), theory('equality')], [c_1478, c_8])).
% 6.91/2.43  tff(c_1545, plain, (![C_218]: (k3_zfmisc_1('#skF_5', '#skF_6', C_218)=k3_zfmisc_1('#skF_1', '#skF_2', C_218))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1518])).
% 6.91/2.43  tff(c_1605, plain, (![A_10, B_11, C_12, C_218]: (A_10='#skF_5' | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(A_10, B_11, C_12)!=k3_zfmisc_1('#skF_1', '#skF_2', C_218))), inference(superposition, [status(thm), theory('equality')], [c_1545, c_16])).
% 6.91/2.43  tff(c_2112, plain, (![C_218]: ('#skF_5'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_2', C_218)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_1605])).
% 6.91/2.43  tff(c_2113, plain, (![C_218]: (k3_zfmisc_1('#skF_1', '#skF_2', C_218)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_2112])).
% 6.91/2.43  tff(c_66, plain, (![C_22, A_20, B_21]: (k1_xboole_0=C_22 | k2_zfmisc_1(A_20, B_21)=k1_xboole_0 | k3_zfmisc_1(A_20, B_21, C_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 6.91/2.43  tff(c_1596, plain, (![C_218]: (k1_xboole_0=C_218 | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', C_218)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1545, c_66])).
% 6.91/2.43  tff(c_1632, plain, (![C_218]: (k1_xboole_0=C_218 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', C_218)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_1596])).
% 6.91/2.43  tff(c_1633, plain, (![C_218]: (k1_xboole_0=C_218 | k3_zfmisc_1('#skF_1', '#skF_2', C_218)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1544, c_1632])).
% 6.91/2.43  tff(c_2244, plain, (![C_252]: (k1_xboole_0=C_252)), inference(demodulation, [status(thm), theory('equality')], [c_2113, c_1633])).
% 6.91/2.43  tff(c_1526, plain, (![C_5]: (k3_zfmisc_1('#skF_5', '#skF_6', C_5)=k3_zfmisc_1('#skF_1', '#skF_2', C_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1518])).
% 6.91/2.43  tff(c_14, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (E_14=B_11 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.91/2.43  tff(c_1593, plain, (![E_14, C_218, D_13, F_15]: (E_14='#skF_6' | k3_zfmisc_1('#skF_5', '#skF_6', C_218)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_218))), inference(superposition, [status(thm), theory('equality')], [c_1545, c_14])).
% 6.91/2.43  tff(c_1631, plain, (![E_14, C_218, D_13, F_15]: (E_14='#skF_6' | k3_zfmisc_1('#skF_1', '#skF_2', C_218)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1('#skF_1', '#skF_2', C_218))), inference(demodulation, [status(thm), theory('equality')], [c_1526, c_1593])).
% 6.91/2.43  tff(c_1777, plain, (![C_218]: ('#skF_6'='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_2', C_218)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_1631])).
% 6.91/2.43  tff(c_1803, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_1777])).
% 6.91/2.43  tff(c_1808, plain, (k2_zfmisc_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1803, c_1478])).
% 6.91/2.43  tff(c_2276, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2244, c_1808])).
% 6.91/2.43  tff(c_2362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1544, c_2276])).
% 6.91/2.43  tff(c_2363, plain, (![C_218]: (k3_zfmisc_1('#skF_1', '#skF_2', C_218)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_1777])).
% 6.91/2.43  tff(c_2462, plain, (![C_497]: (k1_xboole_0=C_497)), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_1633])).
% 6.91/2.43  tff(c_2576, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2462, c_1544])).
% 6.91/2.43  tff(c_2577, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1521])).
% 6.91/2.43  tff(c_2579, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2577])).
% 6.91/2.43  tff(c_2604, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_20])).
% 6.91/2.43  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.91/2.43  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.91/2.43  tff(c_79, plain, (![A_1, C_22]: (k3_zfmisc_1(A_1, k1_xboole_0, C_22)=k2_zfmisc_1(k1_xboole_0, C_22))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 6.91/2.43  tff(c_89, plain, (![A_1, C_22]: (k3_zfmisc_1(A_1, k1_xboole_0, C_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_79])).
% 6.91/2.43  tff(c_141, plain, (![A_29, B_30, C_31, D_32]: (k2_zfmisc_1(k3_zfmisc_1(A_29, B_30, C_31), D_32)=k4_zfmisc_1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.91/2.43  tff(c_163, plain, (![A_1, C_22, D_32]: (k4_zfmisc_1(A_1, k1_xboole_0, C_22, D_32)=k2_zfmisc_1(k1_xboole_0, D_32))), inference(superposition, [status(thm), theory('equality')], [c_89, c_141])).
% 6.91/2.43  tff(c_174, plain, (![A_1, C_22, D_32]: (k4_zfmisc_1(A_1, k1_xboole_0, C_22, D_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_163])).
% 6.91/2.43  tff(c_2595, plain, (![A_1, C_22, D_32]: (k4_zfmisc_1(A_1, '#skF_6', C_22, D_32)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_2579, c_174])).
% 6.91/2.43  tff(c_2977, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2595, c_1054])).
% 6.91/2.43  tff(c_2979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2604, c_2977])).
% 6.91/2.43  tff(c_2980, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2577])).
% 6.91/2.43  tff(c_3007, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2980, c_20])).
% 6.91/2.43  tff(c_86, plain, (![B_2, C_22]: (k3_zfmisc_1(k1_xboole_0, B_2, C_22)=k2_zfmisc_1(k1_xboole_0, C_22))), inference(superposition, [status(thm), theory('equality')], [c_6, c_57])).
% 6.91/2.43  tff(c_90, plain, (![B_2, C_22]: (k3_zfmisc_1(k1_xboole_0, B_2, C_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_86])).
% 6.91/2.43  tff(c_160, plain, (![B_2, C_22, D_32]: (k4_zfmisc_1(k1_xboole_0, B_2, C_22, D_32)=k2_zfmisc_1(k1_xboole_0, D_32))), inference(superposition, [status(thm), theory('equality')], [c_90, c_141])).
% 6.91/2.43  tff(c_173, plain, (![B_2, C_22, D_32]: (k4_zfmisc_1(k1_xboole_0, B_2, C_22, D_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_160])).
% 6.91/2.43  tff(c_3000, plain, (![B_2, C_22, D_32]: (k4_zfmisc_1('#skF_5', B_2, C_22, D_32)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2980, c_2980, c_173])).
% 6.91/2.43  tff(c_3384, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3000, c_1054])).
% 6.91/2.43  tff(c_3386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3007, c_3384])).
% 6.91/2.43  tff(c_3387, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 6.91/2.43  tff(c_3393, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_3387])).
% 6.91/2.43  tff(c_3399, plain, (![A_763, B_764, C_765]: (k2_zfmisc_1(k2_zfmisc_1(A_763, B_764), C_765)=k3_zfmisc_1(A_763, B_764, C_765))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.91/2.43  tff(c_3402, plain, (![A_763, B_764, C_765, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_763, B_764), C_765, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_763, B_764, C_765), C_5))), inference(superposition, [status(thm), theory('equality')], [c_3399, c_8])).
% 6.91/2.43  tff(c_3633, plain, (![A_763, B_764, C_765, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_763, B_764), C_765, C_5)=k4_zfmisc_1(A_763, B_764, C_765, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3402])).
% 6.91/2.43  tff(c_3388, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 6.91/2.43  tff(c_3394, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3388, c_22])).
% 6.91/2.43  tff(c_3753, plain, (![D_814, E_812, A_813, B_811, F_815, C_816]: (F_815=C_816 | k3_zfmisc_1(A_813, B_811, C_816)=k1_xboole_0 | k3_zfmisc_1(D_814, E_812, F_815)!=k3_zfmisc_1(A_813, B_811, C_816))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.91/2.43  tff(c_3759, plain, (![D_814, E_812, C_765, F_815, C_5, B_764, A_763]: (F_815=C_5 | k3_zfmisc_1(k2_zfmisc_1(A_763, B_764), C_765, C_5)=k1_xboole_0 | k4_zfmisc_1(A_763, B_764, C_765, C_5)!=k3_zfmisc_1(D_814, E_812, F_815))), inference(superposition, [status(thm), theory('equality')], [c_3633, c_3753])).
% 6.91/2.43  tff(c_4115, plain, (![D_858, E_855, C_853, B_856, A_854, F_857, C_859]: (F_857=C_859 | k4_zfmisc_1(A_854, B_856, C_853, C_859)=k1_xboole_0 | k4_zfmisc_1(A_854, B_856, C_853, C_859)!=k3_zfmisc_1(D_858, E_855, F_857))), inference(demodulation, [status(thm), theory('equality')], [c_3633, c_3759])).
% 6.91/2.43  tff(c_4151, plain, (![F_857, D_858, E_855]: (F_857='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_858, E_855, F_857))), inference(superposition, [status(thm), theory('equality')], [c_3394, c_4115])).
% 6.91/2.43  tff(c_4158, plain, (![F_857, D_858, E_855]: (F_857='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_858, E_855, F_857))), inference(demodulation, [status(thm), theory('equality')], [c_3394, c_4151])).
% 6.91/2.43  tff(c_4160, plain, (![F_860, D_861, E_862]: (F_860='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_861, E_862, F_860))), inference(negUnitSimplification, [status(thm)], [c_20, c_4158])).
% 6.91/2.43  tff(c_4166, plain, (![C_5, A_763, B_764, C_765]: (C_5='#skF_8' | k4_zfmisc_1(A_763, B_764, C_765, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3633, c_4160])).
% 6.91/2.43  tff(c_4178, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_4166])).
% 6.91/2.43  tff(c_4180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3393, c_4178])).
% 6.91/2.43  tff(c_4181, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_3387])).
% 6.91/2.43  tff(c_4187, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_4181])).
% 6.91/2.43  tff(c_4188, plain, (![A_863, B_864, C_865]: (k2_zfmisc_1(k2_zfmisc_1(A_863, B_864), C_865)=k3_zfmisc_1(A_863, B_864, C_865))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.91/2.43  tff(c_4191, plain, (![A_863, B_864, C_865, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_863, B_864), C_865, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_863, B_864, C_865), C_5))), inference(superposition, [status(thm), theory('equality')], [c_4188, c_8])).
% 6.91/2.43  tff(c_4453, plain, (![A_863, B_864, C_865, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_863, B_864), C_865, C_5)=k4_zfmisc_1(A_863, B_864, C_865, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4191])).
% 6.91/2.43  tff(c_4182, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_3387])).
% 6.91/2.43  tff(c_4229, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4182, c_3388, c_22])).
% 6.91/2.43  tff(c_4547, plain, (![E_912, D_914, F_915, B_911, A_913, C_916]: (E_912=B_911 | k3_zfmisc_1(A_913, B_911, C_916)=k1_xboole_0 | k3_zfmisc_1(D_914, E_912, F_915)!=k3_zfmisc_1(A_913, B_911, C_916))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.91/2.43  tff(c_4553, plain, (![E_912, D_914, F_915, A_863, C_5, C_865, B_864]: (E_912=C_865 | k3_zfmisc_1(k2_zfmisc_1(A_863, B_864), C_865, C_5)=k1_xboole_0 | k4_zfmisc_1(A_863, B_864, C_865, C_5)!=k3_zfmisc_1(D_914, E_912, F_915))), inference(superposition, [status(thm), theory('equality')], [c_4453, c_4547])).
% 6.91/2.43  tff(c_5000, plain, (![C_975, B_974, C_969, D_972, A_970, F_971, E_973]: (E_973=C_969 | k4_zfmisc_1(A_970, B_974, C_969, C_975)=k1_xboole_0 | k4_zfmisc_1(A_970, B_974, C_969, C_975)!=k3_zfmisc_1(D_972, E_973, F_971))), inference(demodulation, [status(thm), theory('equality')], [c_4453, c_4553])).
% 6.91/2.43  tff(c_5033, plain, (![E_973, D_972, F_971]: (E_973='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_972, E_973, F_971))), inference(superposition, [status(thm), theory('equality')], [c_4229, c_5000])).
% 6.91/2.43  tff(c_5043, plain, (![E_973, D_972, F_971]: (E_973='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_972, E_973, F_971))), inference(demodulation, [status(thm), theory('equality')], [c_4229, c_5033])).
% 6.91/2.43  tff(c_5045, plain, (![E_976, D_977, F_978]: (E_976='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_977, E_976, F_978))), inference(negUnitSimplification, [status(thm)], [c_20, c_5043])).
% 6.91/2.43  tff(c_5051, plain, (![C_865, A_863, B_864, C_5]: (C_865='#skF_7' | k4_zfmisc_1(A_863, B_864, C_865, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4453, c_5045])).
% 6.91/2.43  tff(c_5063, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_5051])).
% 6.91/2.43  tff(c_5136, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5063, c_4229])).
% 6.91/2.43  tff(c_4454, plain, (![A_903, B_904, C_905, C_906]: (k3_zfmisc_1(k2_zfmisc_1(A_903, B_904), C_905, C_906)=k4_zfmisc_1(A_903, B_904, C_905, C_906))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4191])).
% 6.91/2.43  tff(c_4472, plain, (![C_905, A_903, C_906, F_15, E_14, D_13, B_904]: (k2_zfmisc_1(A_903, B_904)=D_13 | k3_zfmisc_1(k2_zfmisc_1(A_903, B_904), C_905, C_906)=k1_xboole_0 | k4_zfmisc_1(A_903, B_904, C_905, C_906)!=k3_zfmisc_1(D_13, E_14, F_15))), inference(superposition, [status(thm), theory('equality')], [c_4454, c_16])).
% 6.91/2.43  tff(c_5476, plain, (![D_1042, B_1038, C_1039, E_1041, F_1043, C_1037, A_1040]: (k2_zfmisc_1(A_1040, B_1038)=D_1042 | k4_zfmisc_1(A_1040, B_1038, C_1037, C_1039)=k1_xboole_0 | k4_zfmisc_1(A_1040, B_1038, C_1037, C_1039)!=k3_zfmisc_1(D_1042, E_1041, F_1043))), inference(demodulation, [status(thm), theory('equality')], [c_4453, c_4472])).
% 6.91/2.43  tff(c_5479, plain, (![D_1042, E_1041, F_1043]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1042 | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1042, E_1041, F_1043))), inference(superposition, [status(thm), theory('equality')], [c_5136, c_5476])).
% 6.91/2.43  tff(c_5513, plain, (![D_1042, E_1041, F_1043]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1042 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1042, E_1041, F_1043))), inference(demodulation, [status(thm), theory('equality')], [c_5136, c_5479])).
% 6.91/2.43  tff(c_5521, plain, (![D_1044, E_1045, F_1046]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1044 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1044, E_1045, F_1046))), inference(negUnitSimplification, [status(thm)], [c_20, c_5513])).
% 6.91/2.43  tff(c_5527, plain, (![A_863, B_864, C_865, C_5]: (k2_zfmisc_1(A_863, B_864)=k2_zfmisc_1('#skF_1', '#skF_6') | k4_zfmisc_1(A_863, B_864, C_865, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4453, c_5521])).
% 6.91/2.43  tff(c_5539, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_5527])).
% 6.91/2.43  tff(c_5579, plain, (![C_5]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_5)=k3_zfmisc_1('#skF_1', '#skF_6', C_5))), inference(superposition, [status(thm), theory('equality')], [c_5539, c_8])).
% 6.91/2.43  tff(c_5606, plain, (![C_1054]: (k3_zfmisc_1('#skF_1', '#skF_6', C_1054)=k3_zfmisc_1('#skF_1', '#skF_2', C_1054))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5579])).
% 6.91/2.43  tff(c_5651, plain, (![B_11, A_10, C_12, C_1054]: (B_11='#skF_6' | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(A_10, B_11, C_12)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1054))), inference(superposition, [status(thm), theory('equality')], [c_5606, c_14])).
% 6.91/2.43  tff(c_5838, plain, (![C_1054]: ('#skF_6'='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_2', C_1054)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_5651])).
% 6.91/2.43  tff(c_5839, plain, (![C_1054]: (k3_zfmisc_1('#skF_1', '#skF_2', C_1054)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_4187, c_5838])).
% 6.91/2.43  tff(c_5582, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5539, c_2])).
% 6.91/2.43  tff(c_5605, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5582])).
% 6.91/2.43  tff(c_4197, plain, (![C_865, A_863, B_864]: (k1_xboole_0=C_865 | k2_zfmisc_1(A_863, B_864)=k1_xboole_0 | k3_zfmisc_1(A_863, B_864, C_865)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4188, c_2])).
% 6.91/2.43  tff(c_5657, plain, (![C_1054]: (k1_xboole_0=C_1054 | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', C_1054)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5606, c_4197])).
% 6.91/2.43  tff(c_5693, plain, (![C_1054]: (k1_xboole_0=C_1054 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', C_1054)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5539, c_5657])).
% 6.91/2.43  tff(c_5694, plain, (![C_1054]: (k1_xboole_0=C_1054 | k3_zfmisc_1('#skF_1', '#skF_2', C_1054)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_5605, c_5693])).
% 6.91/2.43  tff(c_5966, plain, (![C_1069]: (k1_xboole_0=C_1069)), inference(demodulation, [status(thm), theory('equality')], [c_5839, c_5694])).
% 6.91/2.43  tff(c_6080, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5966, c_5605])).
% 6.91/2.43  tff(c_6081, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_5582])).
% 6.91/2.43  tff(c_6084, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_6081])).
% 6.91/2.43  tff(c_6108, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6084, c_20])).
% 6.91/2.43  tff(c_4210, plain, (![A_1, C_865]: (k3_zfmisc_1(A_1, k1_xboole_0, C_865)=k2_zfmisc_1(k1_xboole_0, C_865))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4188])).
% 6.91/2.43  tff(c_4220, plain, (![A_1, C_865]: (k3_zfmisc_1(A_1, k1_xboole_0, C_865)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4210])).
% 6.91/2.43  tff(c_4273, plain, (![A_872, B_873, C_874, D_875]: (k2_zfmisc_1(k3_zfmisc_1(A_872, B_873, C_874), D_875)=k4_zfmisc_1(A_872, B_873, C_874, D_875))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.91/2.43  tff(c_4292, plain, (![A_1, C_865, D_875]: (k4_zfmisc_1(A_1, k1_xboole_0, C_865, D_875)=k2_zfmisc_1(k1_xboole_0, D_875))), inference(superposition, [status(thm), theory('equality')], [c_4220, c_4273])).
% 6.91/2.43  tff(c_4305, plain, (![A_1, C_865, D_875]: (k4_zfmisc_1(A_1, k1_xboole_0, C_865, D_875)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4292])).
% 6.91/2.43  tff(c_6101, plain, (![A_1, C_865, D_875]: (k4_zfmisc_1(A_1, '#skF_6', C_865, D_875)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6084, c_6084, c_4305])).
% 6.91/2.43  tff(c_6480, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6101, c_5136])).
% 6.91/2.43  tff(c_6482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6108, c_6480])).
% 6.91/2.43  tff(c_6483, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6081])).
% 6.91/2.43  tff(c_4217, plain, (![B_2, C_865]: (k3_zfmisc_1(k1_xboole_0, B_2, C_865)=k2_zfmisc_1(k1_xboole_0, C_865))), inference(superposition, [status(thm), theory('equality')], [c_6, c_4188])).
% 6.91/2.43  tff(c_4221, plain, (![B_2, C_865]: (k3_zfmisc_1(k1_xboole_0, B_2, C_865)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4217])).
% 6.91/2.43  tff(c_4295, plain, (![B_2, C_865, D_875]: (k4_zfmisc_1(k1_xboole_0, B_2, C_865, D_875)=k2_zfmisc_1(k1_xboole_0, D_875))), inference(superposition, [status(thm), theory('equality')], [c_4221, c_4273])).
% 6.91/2.43  tff(c_4306, plain, (![B_2, C_865, D_875]: (k4_zfmisc_1(k1_xboole_0, B_2, C_865, D_875)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4295])).
% 6.91/2.43  tff(c_6500, plain, (![B_2, C_865, D_875]: (k4_zfmisc_1('#skF_1', B_2, C_865, D_875)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6483, c_6483, c_4306])).
% 6.91/2.43  tff(c_6510, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6483, c_20])).
% 6.91/2.43  tff(c_6909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6500, c_6510])).
% 6.91/2.43  tff(c_6910, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_4181])).
% 6.91/2.43  tff(c_6916, plain, (![A_1335, B_1336, C_1337]: (k2_zfmisc_1(k2_zfmisc_1(A_1335, B_1336), C_1337)=k3_zfmisc_1(A_1335, B_1336, C_1337))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.91/2.43  tff(c_6919, plain, (![A_1335, B_1336, C_1337, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_1335, B_1336), C_1337, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_1335, B_1336, C_1337), C_5))), inference(superposition, [status(thm), theory('equality')], [c_6916, c_8])).
% 6.91/2.43  tff(c_7181, plain, (![A_1335, B_1336, C_1337, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_1335, B_1336), C_1337, C_5)=k4_zfmisc_1(A_1335, B_1336, C_1337, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6919])).
% 6.91/2.43  tff(c_6911, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_4181])).
% 6.91/2.43  tff(c_6957, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6911, c_3388, c_4182, c_22])).
% 6.91/2.43  tff(c_7182, plain, (![A_1375, B_1376, C_1377, C_1378]: (k3_zfmisc_1(k2_zfmisc_1(A_1375, B_1376), C_1377, C_1378)=k4_zfmisc_1(A_1375, B_1376, C_1377, C_1378))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6919])).
% 6.91/2.43  tff(c_7200, plain, (![B_1376, C_1377, F_15, A_1375, E_14, C_1378, D_13]: (E_14=C_1377 | k3_zfmisc_1(k2_zfmisc_1(A_1375, B_1376), C_1377, C_1378)=k1_xboole_0 | k4_zfmisc_1(A_1375, B_1376, C_1377, C_1378)!=k3_zfmisc_1(D_13, E_14, F_15))), inference(superposition, [status(thm), theory('equality')], [c_7182, c_14])).
% 6.91/2.43  tff(c_7593, plain, (![F_1425, D_1423, A_1420, C_1419, E_1421, C_1422, B_1424]: (E_1421=C_1419 | k4_zfmisc_1(A_1420, B_1424, C_1419, C_1422)=k1_xboole_0 | k4_zfmisc_1(A_1420, B_1424, C_1419, C_1422)!=k3_zfmisc_1(D_1423, E_1421, F_1425))), inference(demodulation, [status(thm), theory('equality')], [c_7181, c_7200])).
% 6.91/2.43  tff(c_7626, plain, (![E_1421, D_1423, F_1425]: (E_1421='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1423, E_1421, F_1425))), inference(superposition, [status(thm), theory('equality')], [c_6957, c_7593])).
% 6.91/2.43  tff(c_7636, plain, (![E_1421, D_1423, F_1425]: (E_1421='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1423, E_1421, F_1425))), inference(demodulation, [status(thm), theory('equality')], [c_6957, c_7626])).
% 6.91/2.43  tff(c_7638, plain, (![E_1426, D_1427, F_1428]: (E_1426='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1427, E_1426, F_1428))), inference(negUnitSimplification, [status(thm)], [c_20, c_7636])).
% 6.91/2.43  tff(c_7644, plain, (![C_1337, A_1335, B_1336, C_5]: (C_1337='#skF_7' | k4_zfmisc_1(A_1335, B_1336, C_1337, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7181, c_7638])).
% 6.91/2.43  tff(c_7656, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_7644])).
% 6.91/2.43  tff(c_7658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6910, c_7656])).
% 6.91/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.43  
% 6.91/2.43  Inference rules
% 6.91/2.43  ----------------------
% 6.91/2.43  #Ref     : 31
% 6.91/2.43  #Sup     : 1979
% 6.91/2.43  #Fact    : 0
% 6.91/2.43  #Define  : 0
% 6.91/2.43  #Split   : 10
% 6.91/2.43  #Chain   : 0
% 6.91/2.43  #Close   : 0
% 6.91/2.43  
% 6.91/2.43  Ordering : KBO
% 6.91/2.43  
% 6.91/2.43  Simplification rules
% 6.91/2.43  ----------------------
% 6.91/2.43  #Subsume      : 546
% 6.91/2.43  #Demod        : 1305
% 6.91/2.43  #Tautology    : 1020
% 6.91/2.43  #SimpNegUnit  : 39
% 6.91/2.43  #BackRed      : 151
% 6.91/2.43  
% 6.91/2.43  #Partial instantiations: 584
% 6.91/2.43  #Strategies tried      : 1
% 6.91/2.43  
% 6.91/2.43  Timing (in seconds)
% 6.91/2.43  ----------------------
% 6.91/2.44  Preprocessing        : 0.30
% 6.91/2.44  Parsing              : 0.16
% 6.91/2.44  CNF conversion       : 0.02
% 6.91/2.44  Main loop            : 1.30
% 6.91/2.44  Inferencing          : 0.48
% 6.91/2.44  Reduction            : 0.44
% 6.91/2.44  Demodulation         : 0.32
% 6.91/2.44  BG Simplification    : 0.05
% 6.91/2.44  Subsumption          : 0.26
% 6.91/2.44  Abstraction          : 0.09
% 6.91/2.44  MUC search           : 0.00
% 6.91/2.44  Cooper               : 0.00
% 6.91/2.44  Total                : 1.66
% 6.91/2.44  Index Insertion      : 0.00
% 6.91/2.44  Index Deletion       : 0.00
% 6.91/2.44  Index Matching       : 0.00
% 6.91/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
