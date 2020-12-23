%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:48 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.72s
% Verified   : 
% Statistics : Number of formulae       :  233 (2991 expanded)
%              Number of leaves         :   20 ( 805 expanded)
%              Depth                    :   15
%              Number of atoms          :  390 (10941 expanded)
%              Number of equality atoms :  369 (10920 expanded)
%              Maximal formula depth    :   17 (   4 average)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G,H] :
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(c_20,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_47,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_190,plain,(
    ! [A_42,B_39,G_38,F_44,E_41,C_45,D_43,H_40] :
      ( E_41 = A_42
      | k1_xboole_0 = D_43
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_39
      | k1_xboole_0 = A_42
      | k4_zfmisc_1(E_41,F_44,G_38,H_40) != k4_zfmisc_1(A_42,B_39,C_45,D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_199,plain,(
    ! [A_42,D_43,C_45,B_39] :
      ( A_42 = '#skF_5'
      | k1_xboole_0 = D_43
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_39
      | k1_xboole_0 = A_42
      | k4_zfmisc_1(A_42,B_39,C_45,D_43) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_190])).

tff(c_296,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_199])).

tff(c_297,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_296])).

tff(c_316,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_22,B_23,C_24] : k2_zfmisc_1(k2_zfmisc_1(A_22,B_23),C_24) = k3_zfmisc_1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [B_2,C_24] : k3_zfmisc_1(k1_xboole_0,B_2,C_24) = k2_zfmisc_1(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_59])).

tff(c_92,plain,(
    ! [B_2,C_24] : k3_zfmisc_1(k1_xboole_0,B_2,C_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_88])).

tff(c_143,plain,(
    ! [A_31,B_32,C_33,D_34] : k2_zfmisc_1(k3_zfmisc_1(A_31,B_32,C_33),D_34) = k4_zfmisc_1(A_31,B_32,C_33,D_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_162,plain,(
    ! [B_2,C_24,D_34] : k4_zfmisc_1(k1_xboole_0,B_2,C_24,D_34) = k2_zfmisc_1(k1_xboole_0,D_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_143])).

tff(c_175,plain,(
    ! [B_2,C_24,D_34] : k4_zfmisc_1(k1_xboole_0,B_2,C_24,D_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_162])).

tff(c_320,plain,(
    ! [B_2,C_24,D_34] : k4_zfmisc_1('#skF_1',B_2,C_24,D_34) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_316,c_175])).

tff(c_22,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_327,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_22])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_327])).

tff(c_492,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_533,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_31,B_32,C_33] : k4_zfmisc_1(A_31,B_32,C_33,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_4])).

tff(c_541,plain,(
    ! [A_31,B_32,C_33] : k4_zfmisc_1(A_31,B_32,C_33,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_156])).

tff(c_546,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_22])).

tff(c_703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_546])).

tff(c_704,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_706,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_704])).

tff(c_81,plain,(
    ! [A_1,C_24] : k3_zfmisc_1(A_1,k1_xboole_0,C_24) = k2_zfmisc_1(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_91,plain,(
    ! [A_1,C_24] : k3_zfmisc_1(A_1,k1_xboole_0,C_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_165,plain,(
    ! [A_1,C_24,D_34] : k4_zfmisc_1(A_1,k1_xboole_0,C_24,D_34) = k2_zfmisc_1(k1_xboole_0,D_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_143])).

tff(c_176,plain,(
    ! [A_1,C_24,D_34] : k4_zfmisc_1(A_1,k1_xboole_0,C_24,D_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_165])).

tff(c_752,plain,(
    ! [A_1,C_24,D_34] : k4_zfmisc_1(A_1,'#skF_2',C_24,D_34) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_706,c_176])).

tff(c_760,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_22])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_760])).

tff(c_931,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_72,plain,(
    ! [A_22,B_23] : k3_zfmisc_1(A_22,B_23,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_168,plain,(
    ! [A_22,B_23,D_34] : k4_zfmisc_1(A_22,B_23,k1_xboole_0,D_34) = k2_zfmisc_1(k1_xboole_0,D_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_143])).

tff(c_177,plain,(
    ! [A_22,B_23,D_34] : k4_zfmisc_1(A_22,B_23,k1_xboole_0,D_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_168])).

tff(c_978,plain,(
    ! [A_22,B_23,D_34] : k4_zfmisc_1(A_22,B_23,'#skF_3',D_34) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_931,c_177])).

tff(c_987,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_22])).

tff(c_1137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_987])).

tff(c_1139,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1156,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_24])).

tff(c_1303,plain,(
    ! [F_196,B_191,A_194,E_193,D_195,C_197,G_190,H_192] :
      ( E_193 = A_194
      | k1_xboole_0 = D_195
      | k1_xboole_0 = C_197
      | k1_xboole_0 = B_191
      | k1_xboole_0 = A_194
      | k4_zfmisc_1(E_193,F_196,G_190,H_192) != k4_zfmisc_1(A_194,B_191,C_197,D_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1321,plain,(
    ! [E_193,F_196,G_190,H_192] :
      ( E_193 = '#skF_1'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_193,F_196,G_190,H_192) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_1303])).

tff(c_1583,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1321])).

tff(c_1161,plain,(
    ! [A_171,B_172,C_173] : k2_zfmisc_1(k2_zfmisc_1(A_171,B_172),C_173) = k3_zfmisc_1(A_171,B_172,C_173) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1190,plain,(
    ! [B_2,C_173] : k3_zfmisc_1(k1_xboole_0,B_2,C_173) = k2_zfmisc_1(k1_xboole_0,C_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1161])).

tff(c_1194,plain,(
    ! [B_2,C_173] : k3_zfmisc_1(k1_xboole_0,B_2,C_173) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1190])).

tff(c_1241,plain,(
    ! [A_180,B_181,C_182,D_183] : k2_zfmisc_1(k3_zfmisc_1(A_180,B_181,C_182),D_183) = k4_zfmisc_1(A_180,B_181,C_182,D_183) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1260,plain,(
    ! [B_2,C_173,D_183] : k4_zfmisc_1(k1_xboole_0,B_2,C_173,D_183) = k2_zfmisc_1(k1_xboole_0,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_1241])).

tff(c_1273,plain,(
    ! [B_2,C_173,D_183] : k4_zfmisc_1(k1_xboole_0,B_2,C_173,D_183) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1260])).

tff(c_1590,plain,(
    ! [B_2,C_173,D_183] : k4_zfmisc_1('#skF_1',B_2,C_173,D_183) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_1583,c_1273])).

tff(c_1596,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_22])).

tff(c_1879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1590,c_1596])).

tff(c_1881,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1321])).

tff(c_1464,plain,(
    ! [B_212,F_217,D_216,A_215,C_218,G_211,H_213,E_214] :
      ( F_217 = B_212
      | k1_xboole_0 = D_216
      | k1_xboole_0 = C_218
      | k1_xboole_0 = B_212
      | k1_xboole_0 = A_215
      | k4_zfmisc_1(E_214,F_217,G_211,H_213) != k4_zfmisc_1(A_215,B_212,C_218,D_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1491,plain,(
    ! [B_212,D_216,C_218,A_215] :
      ( B_212 = '#skF_6'
      | k1_xboole_0 = D_216
      | k1_xboole_0 = C_218
      | k1_xboole_0 = B_212
      | k1_xboole_0 = A_215
      | k4_zfmisc_1(A_215,B_212,C_218,D_216) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_1464])).

tff(c_1884,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1491])).

tff(c_1903,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1881,c_1884])).

tff(c_1904,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1903])).

tff(c_1183,plain,(
    ! [A_1,C_173] : k3_zfmisc_1(A_1,k1_xboole_0,C_173) = k2_zfmisc_1(k1_xboole_0,C_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1161])).

tff(c_1193,plain,(
    ! [A_1,C_173] : k3_zfmisc_1(A_1,k1_xboole_0,C_173) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1183])).

tff(c_1263,plain,(
    ! [A_1,C_173,D_183] : k4_zfmisc_1(A_1,k1_xboole_0,C_173,D_183) = k2_zfmisc_1(k1_xboole_0,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_1241])).

tff(c_1274,plain,(
    ! [A_1,C_173,D_183] : k4_zfmisc_1(A_1,k1_xboole_0,C_173,D_183) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1263])).

tff(c_1910,plain,(
    ! [A_1,C_173,D_183] : k4_zfmisc_1(A_1,'#skF_2',C_173,D_183) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1904,c_1904,c_1274])).

tff(c_1919,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1904,c_22])).

tff(c_2161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_1919])).

tff(c_2163,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1903])).

tff(c_1138,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1144,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1138])).

tff(c_2162,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1903])).

tff(c_3051,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2162])).

tff(c_3054,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3051,c_1156])).

tff(c_3415,plain,(
    ! [G_412,A_416,F_418,C_419,B_413,H_414,E_415,D_417] :
      ( H_414 = D_417
      | k1_xboole_0 = D_417
      | k1_xboole_0 = C_419
      | k1_xboole_0 = B_413
      | k1_xboole_0 = A_416
      | k4_zfmisc_1(E_415,F_418,G_412,H_414) != k4_zfmisc_1(A_416,B_413,C_419,D_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3424,plain,(
    ! [D_417,C_419,B_413,A_416] :
      ( D_417 = '#skF_8'
      | k1_xboole_0 = D_417
      | k1_xboole_0 = C_419
      | k1_xboole_0 = B_413
      | k1_xboole_0 = A_416
      | k4_zfmisc_1(A_416,B_413,C_419,D_417) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3054,c_3415])).

tff(c_4283,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3424])).

tff(c_4284,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1881,c_2163,c_1144,c_4283])).

tff(c_4309,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4284])).

tff(c_1174,plain,(
    ! [A_171,B_172] : k3_zfmisc_1(A_171,B_172,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_4])).

tff(c_1266,plain,(
    ! [A_171,B_172,D_183] : k4_zfmisc_1(A_171,B_172,k1_xboole_0,D_183) = k2_zfmisc_1(k1_xboole_0,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_1241])).

tff(c_1275,plain,(
    ! [A_171,B_172,D_183] : k4_zfmisc_1(A_171,B_172,k1_xboole_0,D_183) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1266])).

tff(c_4321,plain,(
    ! [A_171,B_172,D_183] : k4_zfmisc_1(A_171,B_172,'#skF_3',D_183) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4309,c_4309,c_1275])).

tff(c_4329,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4309,c_22])).

tff(c_4645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4321,c_4329])).

tff(c_4646,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4284])).

tff(c_1254,plain,(
    ! [A_180,B_181,C_182] : k4_zfmisc_1(A_180,B_181,C_182,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_4])).

tff(c_4663,plain,(
    ! [A_180,B_181,C_182] : k4_zfmisc_1(A_180,B_181,C_182,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4646,c_1254])).

tff(c_4668,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_22])).

tff(c_4935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4663,c_4668])).

tff(c_4936,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2162])).

tff(c_4938,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4936])).

tff(c_4947,plain,(
    ! [A_171,B_172,D_183] : k4_zfmisc_1(A_171,B_172,'#skF_3',D_183) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4938,c_4938,c_1275])).

tff(c_4955,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4938,c_22])).

tff(c_5188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4947,c_4955])).

tff(c_5189,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4936])).

tff(c_5203,plain,(
    ! [A_180,B_181,C_182] : k4_zfmisc_1(A_180,B_181,C_182,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5189,c_5189,c_1254])).

tff(c_5208,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5189,c_22])).

tff(c_5441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5203,c_5208])).

tff(c_5443,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1138])).

tff(c_5501,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5443,c_1139,c_24])).

tff(c_5591,plain,(
    ! [D_623,A_622,H_620,B_619,C_625,E_621,G_618,F_624] :
      ( H_620 = D_623
      | k1_xboole_0 = D_623
      | k1_xboole_0 = C_625
      | k1_xboole_0 = B_619
      | k1_xboole_0 = A_622
      | k4_zfmisc_1(E_621,F_624,G_618,H_620) != k4_zfmisc_1(A_622,B_619,C_625,D_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5603,plain,(
    ! [H_620,E_621,F_624,G_618] :
      ( H_620 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_621,F_624,G_618,H_620) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5501,c_5591])).

tff(c_5658,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5603])).

tff(c_5460,plain,(
    ! [A_602,B_603,C_604] : k2_zfmisc_1(k2_zfmisc_1(A_602,B_603),C_604) = k3_zfmisc_1(A_602,B_603,C_604) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5489,plain,(
    ! [B_2,C_604] : k3_zfmisc_1(k1_xboole_0,B_2,C_604) = k2_zfmisc_1(k1_xboole_0,C_604) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5460])).

tff(c_5493,plain,(
    ! [B_2,C_604] : k3_zfmisc_1(k1_xboole_0,B_2,C_604) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5489])).

tff(c_5545,plain,(
    ! [A_611,B_612,C_613,D_614] : k2_zfmisc_1(k3_zfmisc_1(A_611,B_612,C_613),D_614) = k4_zfmisc_1(A_611,B_612,C_613,D_614) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5567,plain,(
    ! [B_2,C_604,D_614] : k4_zfmisc_1(k1_xboole_0,B_2,C_604,D_614) = k2_zfmisc_1(k1_xboole_0,D_614) ),
    inference(superposition,[status(thm),theory(equality)],[c_5493,c_5545])).

tff(c_5578,plain,(
    ! [B_2,C_604,D_614] : k4_zfmisc_1(k1_xboole_0,B_2,C_604,D_614) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5567])).

tff(c_5660,plain,(
    ! [B_2,C_604,D_614] : k4_zfmisc_1('#skF_1',B_2,C_604,D_614) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_5658,c_5578])).

tff(c_5667,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_22])).

tff(c_5898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5660,c_5667])).

tff(c_5900,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5603])).

tff(c_5899,plain,(
    ! [H_620,E_621,F_624,G_618] :
      ( k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_4'
      | H_620 = '#skF_4'
      | k4_zfmisc_1(E_621,F_624,G_618,H_620) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_5603])).

tff(c_5901,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5899])).

tff(c_5558,plain,(
    ! [A_611,B_612,C_613] : k4_zfmisc_1(A_611,B_612,C_613,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5545,c_4])).

tff(c_5906,plain,(
    ! [A_611,B_612,C_613] : k4_zfmisc_1(A_611,B_612,C_613,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5901,c_5901,c_5558])).

tff(c_5911,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5901,c_22])).

tff(c_6040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5906,c_5911])).

tff(c_6042,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5899])).

tff(c_6085,plain,(
    ! [E_687,H_686,F_690,B_685,C_691,G_684,D_689,A_688] :
      ( G_684 = C_691
      | k1_xboole_0 = D_689
      | k1_xboole_0 = C_691
      | k1_xboole_0 = B_685
      | k1_xboole_0 = A_688
      | k4_zfmisc_1(E_687,F_690,G_684,H_686) != k4_zfmisc_1(A_688,B_685,C_691,D_689) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6112,plain,(
    ! [C_691,D_689,B_685,A_688] :
      ( C_691 = '#skF_7'
      | k1_xboole_0 = D_689
      | k1_xboole_0 = C_691
      | k1_xboole_0 = B_685
      | k1_xboole_0 = A_688
      | k4_zfmisc_1(A_688,B_685,C_691,D_689) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5501,c_6085])).

tff(c_6191,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6112])).

tff(c_6192,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5900,c_6042,c_6191])).

tff(c_6213,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6192])).

tff(c_5482,plain,(
    ! [A_1,C_604] : k3_zfmisc_1(A_1,k1_xboole_0,C_604) = k2_zfmisc_1(k1_xboole_0,C_604) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5460])).

tff(c_5492,plain,(
    ! [A_1,C_604] : k3_zfmisc_1(A_1,k1_xboole_0,C_604) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5482])).

tff(c_5564,plain,(
    ! [A_1,C_604,D_614] : k4_zfmisc_1(A_1,k1_xboole_0,C_604,D_614) = k2_zfmisc_1(k1_xboole_0,D_614) ),
    inference(superposition,[status(thm),theory(equality)],[c_5492,c_5545])).

tff(c_5577,plain,(
    ! [A_1,C_604,D_614] : k4_zfmisc_1(A_1,k1_xboole_0,C_604,D_614) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5564])).

tff(c_6217,plain,(
    ! [A_1,C_604,D_614] : k4_zfmisc_1(A_1,'#skF_2',C_604,D_614) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6213,c_6213,c_5577])).

tff(c_6228,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6213,c_22])).

tff(c_6412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6217,c_6228])).

tff(c_6413,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6192])).

tff(c_6415,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6413])).

tff(c_6115,plain,(
    ! [G_684,E_687,F_690,H_686] :
      ( G_684 = '#skF_7'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_687,F_690,G_684,H_686) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5501,c_6085])).

tff(c_6120,plain,(
    ! [G_684,E_687,F_690,H_686] :
      ( G_684 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k4_zfmisc_1(E_687,F_690,G_684,H_686) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5900,c_6042,c_6115])).

tff(c_6416,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6120])).

tff(c_6432,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6416,c_22])).

tff(c_6434,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_6',B_2) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6416,c_6416,c_6])).

tff(c_6539,plain,(
    ! [A_744,C_745] : k3_zfmisc_1(A_744,'#skF_6',C_745) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6416,c_6416,c_5492])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6554,plain,(
    ! [A_744,C_745,D_9] : k4_zfmisc_1(A_744,'#skF_6',C_745,D_9) = k2_zfmisc_1('#skF_6',D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_6539,c_10])).

tff(c_6570,plain,(
    ! [A_744,C_745,D_9] : k4_zfmisc_1(A_744,'#skF_6',C_745,D_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6434,c_6554])).

tff(c_6439,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6415,c_5501])).

tff(c_6671,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6570,c_6439])).

tff(c_6672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6432,c_6671])).

tff(c_6673,plain,(
    ! [G_684,E_687,F_690,H_686] :
      ( k1_xboole_0 = '#skF_7'
      | G_684 = '#skF_7'
      | k4_zfmisc_1(E_687,F_690,G_684,H_686) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_6120])).

tff(c_6824,plain,(
    ! [G_684,E_687,F_690,H_686] :
      ( k1_xboole_0 = '#skF_3'
      | G_684 = '#skF_3'
      | k4_zfmisc_1(E_687,F_690,G_684,H_686) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6415,c_6415,c_6673])).

tff(c_6825,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6824])).

tff(c_5473,plain,(
    ! [A_602,B_603] : k3_zfmisc_1(A_602,B_603,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5460,c_4])).

tff(c_5570,plain,(
    ! [A_602,B_603,D_614] : k4_zfmisc_1(A_602,B_603,k1_xboole_0,D_614) = k2_zfmisc_1(k1_xboole_0,D_614) ),
    inference(superposition,[status(thm),theory(equality)],[c_5473,c_5545])).

tff(c_5579,plain,(
    ! [A_602,B_603,D_614] : k4_zfmisc_1(A_602,B_603,k1_xboole_0,D_614) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5570])).

tff(c_6835,plain,(
    ! [A_602,B_603,D_614] : k4_zfmisc_1(A_602,B_603,'#skF_3',D_614) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6825,c_6825,c_5579])).

tff(c_6843,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6825,c_22])).

tff(c_7086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6835,c_6843])).

tff(c_7088,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6824])).

tff(c_6414,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6192])).

tff(c_5442,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1138])).

tff(c_5448,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5442])).

tff(c_6676,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6415,c_5501])).

tff(c_6728,plain,(
    ! [A_771,B_768,C_774,G_767,D_772,E_770,H_769,F_773] :
      ( F_773 = B_768
      | k1_xboole_0 = D_772
      | k1_xboole_0 = C_774
      | k1_xboole_0 = B_768
      | k1_xboole_0 = A_771
      | k4_zfmisc_1(E_770,F_773,G_767,H_769) != k4_zfmisc_1(A_771,B_768,C_774,D_772) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6731,plain,(
    ! [B_768,D_772,C_774,A_771] :
      ( B_768 = '#skF_6'
      | k1_xboole_0 = D_772
      | k1_xboole_0 = C_774
      | k1_xboole_0 = B_768
      | k1_xboole_0 = A_771
      | k4_zfmisc_1(A_771,B_768,C_774,D_772) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6676,c_6728])).

tff(c_7091,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6731])).

tff(c_7092,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5900,c_6414,c_6042,c_5448,c_7091])).

tff(c_7114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7088,c_7092])).

tff(c_7115,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6413])).

tff(c_7124,plain,(
    ! [A_602,B_603,D_614] : k4_zfmisc_1(A_602,B_603,'#skF_3',D_614) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7115,c_7115,c_5579])).

tff(c_7132,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7115,c_22])).

tff(c_7407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7124,c_7132])).

tff(c_7409,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5442])).

tff(c_7466,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7409,c_1139,c_5443,c_24])).

tff(c_7556,plain,(
    ! [F_871,E_868,B_866,C_872,H_867,A_869,D_870,G_865] :
      ( H_867 = D_870
      | k1_xboole_0 = D_870
      | k1_xboole_0 = C_872
      | k1_xboole_0 = B_866
      | k1_xboole_0 = A_869
      | k4_zfmisc_1(E_868,F_871,G_865,H_867) != k4_zfmisc_1(A_869,B_866,C_872,D_870) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7568,plain,(
    ! [H_867,E_868,F_871,G_865] :
      ( H_867 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_868,F_871,G_865,H_867) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7466,c_7556])).

tff(c_7623,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7568])).

tff(c_7425,plain,(
    ! [A_849,B_850,C_851] : k2_zfmisc_1(k2_zfmisc_1(A_849,B_850),C_851) = k3_zfmisc_1(A_849,B_850,C_851) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7454,plain,(
    ! [B_2,C_851] : k3_zfmisc_1(k1_xboole_0,B_2,C_851) = k2_zfmisc_1(k1_xboole_0,C_851) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_7425])).

tff(c_7458,plain,(
    ! [B_2,C_851] : k3_zfmisc_1(k1_xboole_0,B_2,C_851) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7454])).

tff(c_7510,plain,(
    ! [A_858,B_859,C_860,D_861] : k2_zfmisc_1(k3_zfmisc_1(A_858,B_859,C_860),D_861) = k4_zfmisc_1(A_858,B_859,C_860,D_861) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7532,plain,(
    ! [B_2,C_851,D_861] : k4_zfmisc_1(k1_xboole_0,B_2,C_851,D_861) = k2_zfmisc_1(k1_xboole_0,D_861) ),
    inference(superposition,[status(thm),theory(equality)],[c_7458,c_7510])).

tff(c_7543,plain,(
    ! [B_2,C_851,D_861] : k4_zfmisc_1(k1_xboole_0,B_2,C_851,D_861) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7532])).

tff(c_7625,plain,(
    ! [B_2,C_851,D_861] : k4_zfmisc_1('#skF_1',B_2,C_851,D_861) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7623,c_7623,c_7543])).

tff(c_7632,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7623,c_22])).

tff(c_7863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7625,c_7632])).

tff(c_7865,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7568])).

tff(c_7864,plain,(
    ! [H_867,E_868,F_871,G_865] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_4'
      | H_867 = '#skF_4'
      | k4_zfmisc_1(E_868,F_871,G_865,H_867) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_7568])).

tff(c_7866,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7864])).

tff(c_7523,plain,(
    ! [A_858,B_859,C_860] : k4_zfmisc_1(A_858,B_859,C_860,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7510,c_4])).

tff(c_7871,plain,(
    ! [A_858,B_859,C_860] : k4_zfmisc_1(A_858,B_859,C_860,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7866,c_7866,c_7523])).

tff(c_7876,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7866,c_22])).

tff(c_8005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7871,c_7876])).

tff(c_8007,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7864])).

tff(c_7408,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5442])).

tff(c_8050,plain,(
    ! [B_932,H_933,D_936,C_938,E_934,F_937,G_931,A_935] :
      ( G_931 = C_938
      | k1_xboole_0 = D_936
      | k1_xboole_0 = C_938
      | k1_xboole_0 = B_932
      | k1_xboole_0 = A_935
      | k4_zfmisc_1(E_934,F_937,G_931,H_933) != k4_zfmisc_1(A_935,B_932,C_938,D_936) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8077,plain,(
    ! [C_938,D_936,B_932,A_935] :
      ( C_938 = '#skF_7'
      | k1_xboole_0 = D_936
      | k1_xboole_0 = C_938
      | k1_xboole_0 = B_932
      | k1_xboole_0 = A_935
      | k4_zfmisc_1(A_935,B_932,C_938,D_936) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7466,c_8050])).

tff(c_8156,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8077])).

tff(c_8157,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_7865,c_8007,c_7408,c_8156])).

tff(c_8178,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8157])).

tff(c_7447,plain,(
    ! [A_1,C_851] : k3_zfmisc_1(A_1,k1_xboole_0,C_851) = k2_zfmisc_1(k1_xboole_0,C_851) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7425])).

tff(c_7457,plain,(
    ! [A_1,C_851] : k3_zfmisc_1(A_1,k1_xboole_0,C_851) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7447])).

tff(c_7529,plain,(
    ! [A_1,C_851,D_861] : k4_zfmisc_1(A_1,k1_xboole_0,C_851,D_861) = k2_zfmisc_1(k1_xboole_0,D_861) ),
    inference(superposition,[status(thm),theory(equality)],[c_7457,c_7510])).

tff(c_7542,plain,(
    ! [A_1,C_851,D_861] : k4_zfmisc_1(A_1,k1_xboole_0,C_851,D_861) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7529])).

tff(c_8182,plain,(
    ! [A_1,C_851,D_861] : k4_zfmisc_1(A_1,'#skF_2',C_851,D_861) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8178,c_8178,c_7542])).

tff(c_8193,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8178,c_22])).

tff(c_8445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8182,c_8193])).

tff(c_8446,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8157])).

tff(c_7438,plain,(
    ! [A_849,B_850] : k3_zfmisc_1(A_849,B_850,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7425,c_4])).

tff(c_7535,plain,(
    ! [A_849,B_850,D_861] : k4_zfmisc_1(A_849,B_850,k1_xboole_0,D_861) = k2_zfmisc_1(k1_xboole_0,D_861) ),
    inference(superposition,[status(thm),theory(equality)],[c_7438,c_7510])).

tff(c_7544,plain,(
    ! [A_849,B_850,D_861] : k4_zfmisc_1(A_849,B_850,k1_xboole_0,D_861) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7535])).

tff(c_8522,plain,(
    ! [A_849,B_850,D_861] : k4_zfmisc_1(A_849,B_850,'#skF_3',D_861) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8446,c_8446,c_7544])).

tff(c_8530,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8446,c_22])).

tff(c_8751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8522,c_8530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.30  
% 6.41/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.30  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 6.41/2.30  
% 6.41/2.30  %Foreground sorts:
% 6.41/2.30  
% 6.41/2.30  
% 6.41/2.30  %Background operators:
% 6.41/2.30  
% 6.41/2.30  
% 6.41/2.30  %Foreground operators:
% 6.41/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.41/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.41/2.30  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 6.41/2.30  tff('#skF_7', type, '#skF_7': $i).
% 6.41/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.41/2.30  tff('#skF_6', type, '#skF_6': $i).
% 6.41/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.41/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.41/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.41/2.30  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.41/2.30  tff('#skF_8', type, '#skF_8': $i).
% 6.41/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.41/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.41/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.41/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.41/2.30  
% 6.72/2.33  tff(f_66, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 6.72/2.33  tff(f_53, axiom, (![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 6.72/2.33  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.72/2.33  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 6.72/2.33  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 6.72/2.33  tff(c_20, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.72/2.33  tff(c_47, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_20])).
% 6.72/2.33  tff(c_24, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.72/2.33  tff(c_190, plain, (![A_42, B_39, G_38, F_44, E_41, C_45, D_43, H_40]: (E_41=A_42 | k1_xboole_0=D_43 | k1_xboole_0=C_45 | k1_xboole_0=B_39 | k1_xboole_0=A_42 | k4_zfmisc_1(E_41, F_44, G_38, H_40)!=k4_zfmisc_1(A_42, B_39, C_45, D_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_199, plain, (![A_42, D_43, C_45, B_39]: (A_42='#skF_5' | k1_xboole_0=D_43 | k1_xboole_0=C_45 | k1_xboole_0=B_39 | k1_xboole_0=A_42 | k4_zfmisc_1(A_42, B_39, C_45, D_43)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_190])).
% 6.72/2.33  tff(c_296, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_199])).
% 6.72/2.33  tff(c_297, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_47, c_296])).
% 6.72/2.33  tff(c_316, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_297])).
% 6.72/2.33  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.72/2.33  tff(c_59, plain, (![A_22, B_23, C_24]: (k2_zfmisc_1(k2_zfmisc_1(A_22, B_23), C_24)=k3_zfmisc_1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.72/2.33  tff(c_88, plain, (![B_2, C_24]: (k3_zfmisc_1(k1_xboole_0, B_2, C_24)=k2_zfmisc_1(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_6, c_59])).
% 6.72/2.33  tff(c_92, plain, (![B_2, C_24]: (k3_zfmisc_1(k1_xboole_0, B_2, C_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_88])).
% 6.72/2.33  tff(c_143, plain, (![A_31, B_32, C_33, D_34]: (k2_zfmisc_1(k3_zfmisc_1(A_31, B_32, C_33), D_34)=k4_zfmisc_1(A_31, B_32, C_33, D_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.72/2.33  tff(c_162, plain, (![B_2, C_24, D_34]: (k4_zfmisc_1(k1_xboole_0, B_2, C_24, D_34)=k2_zfmisc_1(k1_xboole_0, D_34))), inference(superposition, [status(thm), theory('equality')], [c_92, c_143])).
% 6.72/2.33  tff(c_175, plain, (![B_2, C_24, D_34]: (k4_zfmisc_1(k1_xboole_0, B_2, C_24, D_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_162])).
% 6.72/2.33  tff(c_320, plain, (![B_2, C_24, D_34]: (k4_zfmisc_1('#skF_1', B_2, C_24, D_34)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_316, c_175])).
% 6.72/2.33  tff(c_22, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.72/2.33  tff(c_327, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_316, c_22])).
% 6.72/2.33  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_327])).
% 6.72/2.33  tff(c_492, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_297])).
% 6.72/2.33  tff(c_533, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_492])).
% 6.72/2.33  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.72/2.33  tff(c_156, plain, (![A_31, B_32, C_33]: (k4_zfmisc_1(A_31, B_32, C_33, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_143, c_4])).
% 6.72/2.33  tff(c_541, plain, (![A_31, B_32, C_33]: (k4_zfmisc_1(A_31, B_32, C_33, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_156])).
% 6.72/2.33  tff(c_546, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_22])).
% 6.72/2.33  tff(c_703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_541, c_546])).
% 6.72/2.33  tff(c_704, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_492])).
% 6.72/2.33  tff(c_706, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_704])).
% 6.72/2.33  tff(c_81, plain, (![A_1, C_24]: (k3_zfmisc_1(A_1, k1_xboole_0, C_24)=k2_zfmisc_1(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 6.72/2.33  tff(c_91, plain, (![A_1, C_24]: (k3_zfmisc_1(A_1, k1_xboole_0, C_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_81])).
% 6.72/2.33  tff(c_165, plain, (![A_1, C_24, D_34]: (k4_zfmisc_1(A_1, k1_xboole_0, C_24, D_34)=k2_zfmisc_1(k1_xboole_0, D_34))), inference(superposition, [status(thm), theory('equality')], [c_91, c_143])).
% 6.72/2.33  tff(c_176, plain, (![A_1, C_24, D_34]: (k4_zfmisc_1(A_1, k1_xboole_0, C_24, D_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_165])).
% 6.72/2.33  tff(c_752, plain, (![A_1, C_24, D_34]: (k4_zfmisc_1(A_1, '#skF_2', C_24, D_34)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_706, c_706, c_176])).
% 6.72/2.33  tff(c_760, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_706, c_22])).
% 6.72/2.33  tff(c_930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_752, c_760])).
% 6.72/2.33  tff(c_931, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_704])).
% 6.72/2.33  tff(c_72, plain, (![A_22, B_23]: (k3_zfmisc_1(A_22, B_23, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59, c_4])).
% 6.72/2.33  tff(c_168, plain, (![A_22, B_23, D_34]: (k4_zfmisc_1(A_22, B_23, k1_xboole_0, D_34)=k2_zfmisc_1(k1_xboole_0, D_34))), inference(superposition, [status(thm), theory('equality')], [c_72, c_143])).
% 6.72/2.33  tff(c_177, plain, (![A_22, B_23, D_34]: (k4_zfmisc_1(A_22, B_23, k1_xboole_0, D_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_168])).
% 6.72/2.33  tff(c_978, plain, (![A_22, B_23, D_34]: (k4_zfmisc_1(A_22, B_23, '#skF_3', D_34)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_931, c_931, c_177])).
% 6.72/2.33  tff(c_987, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_931, c_22])).
% 6.72/2.33  tff(c_1137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_978, c_987])).
% 6.72/2.33  tff(c_1139, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 6.72/2.33  tff(c_1156, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_24])).
% 6.72/2.33  tff(c_1303, plain, (![F_196, B_191, A_194, E_193, D_195, C_197, G_190, H_192]: (E_193=A_194 | k1_xboole_0=D_195 | k1_xboole_0=C_197 | k1_xboole_0=B_191 | k1_xboole_0=A_194 | k4_zfmisc_1(E_193, F_196, G_190, H_192)!=k4_zfmisc_1(A_194, B_191, C_197, D_195))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_1321, plain, (![E_193, F_196, G_190, H_192]: (E_193='#skF_1' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_193, F_196, G_190, H_192)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_1303])).
% 6.72/2.33  tff(c_1583, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1321])).
% 6.72/2.33  tff(c_1161, plain, (![A_171, B_172, C_173]: (k2_zfmisc_1(k2_zfmisc_1(A_171, B_172), C_173)=k3_zfmisc_1(A_171, B_172, C_173))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.72/2.33  tff(c_1190, plain, (![B_2, C_173]: (k3_zfmisc_1(k1_xboole_0, B_2, C_173)=k2_zfmisc_1(k1_xboole_0, C_173))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1161])).
% 6.72/2.33  tff(c_1194, plain, (![B_2, C_173]: (k3_zfmisc_1(k1_xboole_0, B_2, C_173)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1190])).
% 6.72/2.33  tff(c_1241, plain, (![A_180, B_181, C_182, D_183]: (k2_zfmisc_1(k3_zfmisc_1(A_180, B_181, C_182), D_183)=k4_zfmisc_1(A_180, B_181, C_182, D_183))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.72/2.33  tff(c_1260, plain, (![B_2, C_173, D_183]: (k4_zfmisc_1(k1_xboole_0, B_2, C_173, D_183)=k2_zfmisc_1(k1_xboole_0, D_183))), inference(superposition, [status(thm), theory('equality')], [c_1194, c_1241])).
% 6.72/2.33  tff(c_1273, plain, (![B_2, C_173, D_183]: (k4_zfmisc_1(k1_xboole_0, B_2, C_173, D_183)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1260])).
% 6.72/2.33  tff(c_1590, plain, (![B_2, C_173, D_183]: (k4_zfmisc_1('#skF_1', B_2, C_173, D_183)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_1583, c_1273])).
% 6.72/2.33  tff(c_1596, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_22])).
% 6.72/2.33  tff(c_1879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1590, c_1596])).
% 6.72/2.33  tff(c_1881, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1321])).
% 6.72/2.33  tff(c_1464, plain, (![B_212, F_217, D_216, A_215, C_218, G_211, H_213, E_214]: (F_217=B_212 | k1_xboole_0=D_216 | k1_xboole_0=C_218 | k1_xboole_0=B_212 | k1_xboole_0=A_215 | k4_zfmisc_1(E_214, F_217, G_211, H_213)!=k4_zfmisc_1(A_215, B_212, C_218, D_216))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_1491, plain, (![B_212, D_216, C_218, A_215]: (B_212='#skF_6' | k1_xboole_0=D_216 | k1_xboole_0=C_218 | k1_xboole_0=B_212 | k1_xboole_0=A_215 | k4_zfmisc_1(A_215, B_212, C_218, D_216)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_1464])).
% 6.72/2.33  tff(c_1884, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1491])).
% 6.72/2.33  tff(c_1903, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1881, c_1884])).
% 6.72/2.33  tff(c_1904, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1903])).
% 6.72/2.33  tff(c_1183, plain, (![A_1, C_173]: (k3_zfmisc_1(A_1, k1_xboole_0, C_173)=k2_zfmisc_1(k1_xboole_0, C_173))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1161])).
% 6.72/2.33  tff(c_1193, plain, (![A_1, C_173]: (k3_zfmisc_1(A_1, k1_xboole_0, C_173)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1183])).
% 6.72/2.33  tff(c_1263, plain, (![A_1, C_173, D_183]: (k4_zfmisc_1(A_1, k1_xboole_0, C_173, D_183)=k2_zfmisc_1(k1_xboole_0, D_183))), inference(superposition, [status(thm), theory('equality')], [c_1193, c_1241])).
% 6.72/2.33  tff(c_1274, plain, (![A_1, C_173, D_183]: (k4_zfmisc_1(A_1, k1_xboole_0, C_173, D_183)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1263])).
% 6.72/2.33  tff(c_1910, plain, (![A_1, C_173, D_183]: (k4_zfmisc_1(A_1, '#skF_2', C_173, D_183)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1904, c_1904, c_1274])).
% 6.72/2.33  tff(c_1919, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1904, c_22])).
% 6.72/2.33  tff(c_2161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1910, c_1919])).
% 6.72/2.33  tff(c_2163, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1903])).
% 6.72/2.33  tff(c_1138, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_20])).
% 6.72/2.33  tff(c_1144, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_1138])).
% 6.72/2.33  tff(c_2162, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | '#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_1903])).
% 6.72/2.33  tff(c_3051, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_2162])).
% 6.72/2.33  tff(c_3054, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3051, c_1156])).
% 6.72/2.33  tff(c_3415, plain, (![G_412, A_416, F_418, C_419, B_413, H_414, E_415, D_417]: (H_414=D_417 | k1_xboole_0=D_417 | k1_xboole_0=C_419 | k1_xboole_0=B_413 | k1_xboole_0=A_416 | k4_zfmisc_1(E_415, F_418, G_412, H_414)!=k4_zfmisc_1(A_416, B_413, C_419, D_417))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_3424, plain, (![D_417, C_419, B_413, A_416]: (D_417='#skF_8' | k1_xboole_0=D_417 | k1_xboole_0=C_419 | k1_xboole_0=B_413 | k1_xboole_0=A_416 | k4_zfmisc_1(A_416, B_413, C_419, D_417)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3054, c_3415])).
% 6.72/2.33  tff(c_4283, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_3424])).
% 6.72/2.33  tff(c_4284, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1881, c_2163, c_1144, c_4283])).
% 6.72/2.33  tff(c_4309, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4284])).
% 6.72/2.33  tff(c_1174, plain, (![A_171, B_172]: (k3_zfmisc_1(A_171, B_172, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1161, c_4])).
% 6.72/2.33  tff(c_1266, plain, (![A_171, B_172, D_183]: (k4_zfmisc_1(A_171, B_172, k1_xboole_0, D_183)=k2_zfmisc_1(k1_xboole_0, D_183))), inference(superposition, [status(thm), theory('equality')], [c_1174, c_1241])).
% 6.72/2.33  tff(c_1275, plain, (![A_171, B_172, D_183]: (k4_zfmisc_1(A_171, B_172, k1_xboole_0, D_183)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1266])).
% 6.72/2.33  tff(c_4321, plain, (![A_171, B_172, D_183]: (k4_zfmisc_1(A_171, B_172, '#skF_3', D_183)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4309, c_4309, c_1275])).
% 6.72/2.33  tff(c_4329, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4309, c_22])).
% 6.72/2.33  tff(c_4645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4321, c_4329])).
% 6.72/2.33  tff(c_4646, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4284])).
% 6.72/2.33  tff(c_1254, plain, (![A_180, B_181, C_182]: (k4_zfmisc_1(A_180, B_181, C_182, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1241, c_4])).
% 6.72/2.33  tff(c_4663, plain, (![A_180, B_181, C_182]: (k4_zfmisc_1(A_180, B_181, C_182, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4646, c_1254])).
% 6.72/2.33  tff(c_4668, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_22])).
% 6.72/2.33  tff(c_4935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4663, c_4668])).
% 6.72/2.33  tff(c_4936, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2162])).
% 6.72/2.33  tff(c_4938, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4936])).
% 6.72/2.33  tff(c_4947, plain, (![A_171, B_172, D_183]: (k4_zfmisc_1(A_171, B_172, '#skF_3', D_183)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4938, c_4938, c_1275])).
% 6.72/2.33  tff(c_4955, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4938, c_22])).
% 6.72/2.33  tff(c_5188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4947, c_4955])).
% 6.72/2.33  tff(c_5189, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4936])).
% 6.72/2.33  tff(c_5203, plain, (![A_180, B_181, C_182]: (k4_zfmisc_1(A_180, B_181, C_182, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5189, c_5189, c_1254])).
% 6.72/2.33  tff(c_5208, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5189, c_22])).
% 6.72/2.33  tff(c_5441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5203, c_5208])).
% 6.72/2.33  tff(c_5443, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_1138])).
% 6.72/2.33  tff(c_5501, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5443, c_1139, c_24])).
% 6.72/2.33  tff(c_5591, plain, (![D_623, A_622, H_620, B_619, C_625, E_621, G_618, F_624]: (H_620=D_623 | k1_xboole_0=D_623 | k1_xboole_0=C_625 | k1_xboole_0=B_619 | k1_xboole_0=A_622 | k4_zfmisc_1(E_621, F_624, G_618, H_620)!=k4_zfmisc_1(A_622, B_619, C_625, D_623))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_5603, plain, (![H_620, E_621, F_624, G_618]: (H_620='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_621, F_624, G_618, H_620)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5501, c_5591])).
% 6.72/2.33  tff(c_5658, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_5603])).
% 6.72/2.33  tff(c_5460, plain, (![A_602, B_603, C_604]: (k2_zfmisc_1(k2_zfmisc_1(A_602, B_603), C_604)=k3_zfmisc_1(A_602, B_603, C_604))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.72/2.33  tff(c_5489, plain, (![B_2, C_604]: (k3_zfmisc_1(k1_xboole_0, B_2, C_604)=k2_zfmisc_1(k1_xboole_0, C_604))), inference(superposition, [status(thm), theory('equality')], [c_6, c_5460])).
% 6.72/2.33  tff(c_5493, plain, (![B_2, C_604]: (k3_zfmisc_1(k1_xboole_0, B_2, C_604)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5489])).
% 6.72/2.33  tff(c_5545, plain, (![A_611, B_612, C_613, D_614]: (k2_zfmisc_1(k3_zfmisc_1(A_611, B_612, C_613), D_614)=k4_zfmisc_1(A_611, B_612, C_613, D_614))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.72/2.33  tff(c_5567, plain, (![B_2, C_604, D_614]: (k4_zfmisc_1(k1_xboole_0, B_2, C_604, D_614)=k2_zfmisc_1(k1_xboole_0, D_614))), inference(superposition, [status(thm), theory('equality')], [c_5493, c_5545])).
% 6.72/2.33  tff(c_5578, plain, (![B_2, C_604, D_614]: (k4_zfmisc_1(k1_xboole_0, B_2, C_604, D_614)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5567])).
% 6.72/2.33  tff(c_5660, plain, (![B_2, C_604, D_614]: (k4_zfmisc_1('#skF_1', B_2, C_604, D_614)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_5658, c_5578])).
% 6.72/2.33  tff(c_5667, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_22])).
% 6.72/2.33  tff(c_5898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5660, c_5667])).
% 6.72/2.33  tff(c_5900, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_5603])).
% 6.72/2.33  tff(c_5899, plain, (![H_620, E_621, F_624, G_618]: (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_4' | H_620='#skF_4' | k4_zfmisc_1(E_621, F_624, G_618, H_620)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_5603])).
% 6.72/2.33  tff(c_5901, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5899])).
% 6.72/2.33  tff(c_5558, plain, (![A_611, B_612, C_613]: (k4_zfmisc_1(A_611, B_612, C_613, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5545, c_4])).
% 6.72/2.33  tff(c_5906, plain, (![A_611, B_612, C_613]: (k4_zfmisc_1(A_611, B_612, C_613, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5901, c_5901, c_5558])).
% 6.72/2.33  tff(c_5911, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5901, c_22])).
% 6.72/2.33  tff(c_6040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5906, c_5911])).
% 6.72/2.33  tff(c_6042, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_5899])).
% 6.72/2.33  tff(c_6085, plain, (![E_687, H_686, F_690, B_685, C_691, G_684, D_689, A_688]: (G_684=C_691 | k1_xboole_0=D_689 | k1_xboole_0=C_691 | k1_xboole_0=B_685 | k1_xboole_0=A_688 | k4_zfmisc_1(E_687, F_690, G_684, H_686)!=k4_zfmisc_1(A_688, B_685, C_691, D_689))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_6112, plain, (![C_691, D_689, B_685, A_688]: (C_691='#skF_7' | k1_xboole_0=D_689 | k1_xboole_0=C_691 | k1_xboole_0=B_685 | k1_xboole_0=A_688 | k4_zfmisc_1(A_688, B_685, C_691, D_689)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5501, c_6085])).
% 6.72/2.33  tff(c_6191, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_6112])).
% 6.72/2.33  tff(c_6192, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5900, c_6042, c_6191])).
% 6.72/2.33  tff(c_6213, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6192])).
% 6.72/2.33  tff(c_5482, plain, (![A_1, C_604]: (k3_zfmisc_1(A_1, k1_xboole_0, C_604)=k2_zfmisc_1(k1_xboole_0, C_604))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5460])).
% 6.72/2.33  tff(c_5492, plain, (![A_1, C_604]: (k3_zfmisc_1(A_1, k1_xboole_0, C_604)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5482])).
% 6.72/2.33  tff(c_5564, plain, (![A_1, C_604, D_614]: (k4_zfmisc_1(A_1, k1_xboole_0, C_604, D_614)=k2_zfmisc_1(k1_xboole_0, D_614))), inference(superposition, [status(thm), theory('equality')], [c_5492, c_5545])).
% 6.72/2.33  tff(c_5577, plain, (![A_1, C_604, D_614]: (k4_zfmisc_1(A_1, k1_xboole_0, C_604, D_614)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5564])).
% 6.72/2.33  tff(c_6217, plain, (![A_1, C_604, D_614]: (k4_zfmisc_1(A_1, '#skF_2', C_604, D_614)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6213, c_6213, c_5577])).
% 6.72/2.33  tff(c_6228, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6213, c_22])).
% 6.72/2.33  tff(c_6412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6217, c_6228])).
% 6.72/2.33  tff(c_6413, plain, (k1_xboole_0='#skF_3' | '#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_6192])).
% 6.72/2.33  tff(c_6415, plain, ('#skF_7'='#skF_3'), inference(splitLeft, [status(thm)], [c_6413])).
% 6.72/2.33  tff(c_6115, plain, (![G_684, E_687, F_690, H_686]: (G_684='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_687, F_690, G_684, H_686)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5501, c_6085])).
% 6.72/2.33  tff(c_6120, plain, (![G_684, E_687, F_690, H_686]: (G_684='#skF_7' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k4_zfmisc_1(E_687, F_690, G_684, H_686)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_5900, c_6042, c_6115])).
% 6.72/2.33  tff(c_6416, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_6120])).
% 6.72/2.33  tff(c_6432, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6416, c_22])).
% 6.72/2.33  tff(c_6434, plain, (![B_2]: (k2_zfmisc_1('#skF_6', B_2)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6416, c_6416, c_6])).
% 6.72/2.33  tff(c_6539, plain, (![A_744, C_745]: (k3_zfmisc_1(A_744, '#skF_6', C_745)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6416, c_6416, c_5492])).
% 6.72/2.33  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.72/2.33  tff(c_6554, plain, (![A_744, C_745, D_9]: (k4_zfmisc_1(A_744, '#skF_6', C_745, D_9)=k2_zfmisc_1('#skF_6', D_9))), inference(superposition, [status(thm), theory('equality')], [c_6539, c_10])).
% 6.72/2.33  tff(c_6570, plain, (![A_744, C_745, D_9]: (k4_zfmisc_1(A_744, '#skF_6', C_745, D_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6434, c_6554])).
% 6.72/2.33  tff(c_6439, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6415, c_5501])).
% 6.72/2.33  tff(c_6671, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6570, c_6439])).
% 6.72/2.33  tff(c_6672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6432, c_6671])).
% 6.72/2.33  tff(c_6673, plain, (![G_684, E_687, F_690, H_686]: (k1_xboole_0='#skF_7' | G_684='#skF_7' | k4_zfmisc_1(E_687, F_690, G_684, H_686)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_6120])).
% 6.72/2.33  tff(c_6824, plain, (![G_684, E_687, F_690, H_686]: (k1_xboole_0='#skF_3' | G_684='#skF_3' | k4_zfmisc_1(E_687, F_690, G_684, H_686)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6415, c_6415, c_6673])).
% 6.72/2.33  tff(c_6825, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_6824])).
% 6.72/2.33  tff(c_5473, plain, (![A_602, B_603]: (k3_zfmisc_1(A_602, B_603, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5460, c_4])).
% 6.72/2.33  tff(c_5570, plain, (![A_602, B_603, D_614]: (k4_zfmisc_1(A_602, B_603, k1_xboole_0, D_614)=k2_zfmisc_1(k1_xboole_0, D_614))), inference(superposition, [status(thm), theory('equality')], [c_5473, c_5545])).
% 6.72/2.33  tff(c_5579, plain, (![A_602, B_603, D_614]: (k4_zfmisc_1(A_602, B_603, k1_xboole_0, D_614)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5570])).
% 6.72/2.33  tff(c_6835, plain, (![A_602, B_603, D_614]: (k4_zfmisc_1(A_602, B_603, '#skF_3', D_614)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6825, c_6825, c_5579])).
% 6.72/2.33  tff(c_6843, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6825, c_22])).
% 6.72/2.33  tff(c_7086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6835, c_6843])).
% 6.72/2.33  tff(c_7088, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_6824])).
% 6.72/2.33  tff(c_6414, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_6192])).
% 6.72/2.33  tff(c_5442, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_1138])).
% 6.72/2.33  tff(c_5448, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_5442])).
% 6.72/2.33  tff(c_6676, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6415, c_5501])).
% 6.72/2.33  tff(c_6728, plain, (![A_771, B_768, C_774, G_767, D_772, E_770, H_769, F_773]: (F_773=B_768 | k1_xboole_0=D_772 | k1_xboole_0=C_774 | k1_xboole_0=B_768 | k1_xboole_0=A_771 | k4_zfmisc_1(E_770, F_773, G_767, H_769)!=k4_zfmisc_1(A_771, B_768, C_774, D_772))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_6731, plain, (![B_768, D_772, C_774, A_771]: (B_768='#skF_6' | k1_xboole_0=D_772 | k1_xboole_0=C_774 | k1_xboole_0=B_768 | k1_xboole_0=A_771 | k4_zfmisc_1(A_771, B_768, C_774, D_772)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6676, c_6728])).
% 6.72/2.33  tff(c_7091, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_6731])).
% 6.72/2.33  tff(c_7092, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5900, c_6414, c_6042, c_5448, c_7091])).
% 6.72/2.33  tff(c_7114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7088, c_7092])).
% 6.72/2.33  tff(c_7115, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_6413])).
% 6.72/2.33  tff(c_7124, plain, (![A_602, B_603, D_614]: (k4_zfmisc_1(A_602, B_603, '#skF_3', D_614)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7115, c_7115, c_5579])).
% 6.72/2.33  tff(c_7132, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7115, c_22])).
% 6.72/2.33  tff(c_7407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7124, c_7132])).
% 6.72/2.33  tff(c_7409, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_5442])).
% 6.72/2.33  tff(c_7466, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7409, c_1139, c_5443, c_24])).
% 6.72/2.33  tff(c_7556, plain, (![F_871, E_868, B_866, C_872, H_867, A_869, D_870, G_865]: (H_867=D_870 | k1_xboole_0=D_870 | k1_xboole_0=C_872 | k1_xboole_0=B_866 | k1_xboole_0=A_869 | k4_zfmisc_1(E_868, F_871, G_865, H_867)!=k4_zfmisc_1(A_869, B_866, C_872, D_870))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_7568, plain, (![H_867, E_868, F_871, G_865]: (H_867='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_868, F_871, G_865, H_867)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7466, c_7556])).
% 6.72/2.33  tff(c_7623, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_7568])).
% 6.72/2.33  tff(c_7425, plain, (![A_849, B_850, C_851]: (k2_zfmisc_1(k2_zfmisc_1(A_849, B_850), C_851)=k3_zfmisc_1(A_849, B_850, C_851))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.72/2.33  tff(c_7454, plain, (![B_2, C_851]: (k3_zfmisc_1(k1_xboole_0, B_2, C_851)=k2_zfmisc_1(k1_xboole_0, C_851))), inference(superposition, [status(thm), theory('equality')], [c_6, c_7425])).
% 6.72/2.33  tff(c_7458, plain, (![B_2, C_851]: (k3_zfmisc_1(k1_xboole_0, B_2, C_851)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7454])).
% 6.72/2.33  tff(c_7510, plain, (![A_858, B_859, C_860, D_861]: (k2_zfmisc_1(k3_zfmisc_1(A_858, B_859, C_860), D_861)=k4_zfmisc_1(A_858, B_859, C_860, D_861))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.72/2.33  tff(c_7532, plain, (![B_2, C_851, D_861]: (k4_zfmisc_1(k1_xboole_0, B_2, C_851, D_861)=k2_zfmisc_1(k1_xboole_0, D_861))), inference(superposition, [status(thm), theory('equality')], [c_7458, c_7510])).
% 6.72/2.33  tff(c_7543, plain, (![B_2, C_851, D_861]: (k4_zfmisc_1(k1_xboole_0, B_2, C_851, D_861)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7532])).
% 6.72/2.33  tff(c_7625, plain, (![B_2, C_851, D_861]: (k4_zfmisc_1('#skF_1', B_2, C_851, D_861)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7623, c_7623, c_7543])).
% 6.72/2.33  tff(c_7632, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7623, c_22])).
% 6.72/2.33  tff(c_7863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7625, c_7632])).
% 6.72/2.33  tff(c_7865, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_7568])).
% 6.72/2.33  tff(c_7864, plain, (![H_867, E_868, F_871, G_865]: (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_4' | H_867='#skF_4' | k4_zfmisc_1(E_868, F_871, G_865, H_867)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_7568])).
% 6.72/2.33  tff(c_7866, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_7864])).
% 6.72/2.33  tff(c_7523, plain, (![A_858, B_859, C_860]: (k4_zfmisc_1(A_858, B_859, C_860, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7510, c_4])).
% 6.72/2.33  tff(c_7871, plain, (![A_858, B_859, C_860]: (k4_zfmisc_1(A_858, B_859, C_860, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7866, c_7866, c_7523])).
% 6.72/2.33  tff(c_7876, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7866, c_22])).
% 6.72/2.33  tff(c_8005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7871, c_7876])).
% 6.72/2.33  tff(c_8007, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_7864])).
% 6.72/2.33  tff(c_7408, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_5442])).
% 6.72/2.33  tff(c_8050, plain, (![B_932, H_933, D_936, C_938, E_934, F_937, G_931, A_935]: (G_931=C_938 | k1_xboole_0=D_936 | k1_xboole_0=C_938 | k1_xboole_0=B_932 | k1_xboole_0=A_935 | k4_zfmisc_1(E_934, F_937, G_931, H_933)!=k4_zfmisc_1(A_935, B_932, C_938, D_936))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.33  tff(c_8077, plain, (![C_938, D_936, B_932, A_935]: (C_938='#skF_7' | k1_xboole_0=D_936 | k1_xboole_0=C_938 | k1_xboole_0=B_932 | k1_xboole_0=A_935 | k4_zfmisc_1(A_935, B_932, C_938, D_936)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7466, c_8050])).
% 6.72/2.33  tff(c_8156, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_8077])).
% 6.72/2.33  tff(c_8157, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_7865, c_8007, c_7408, c_8156])).
% 6.72/2.33  tff(c_8178, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_8157])).
% 6.72/2.33  tff(c_7447, plain, (![A_1, C_851]: (k3_zfmisc_1(A_1, k1_xboole_0, C_851)=k2_zfmisc_1(k1_xboole_0, C_851))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7425])).
% 6.72/2.33  tff(c_7457, plain, (![A_1, C_851]: (k3_zfmisc_1(A_1, k1_xboole_0, C_851)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7447])).
% 6.72/2.33  tff(c_7529, plain, (![A_1, C_851, D_861]: (k4_zfmisc_1(A_1, k1_xboole_0, C_851, D_861)=k2_zfmisc_1(k1_xboole_0, D_861))), inference(superposition, [status(thm), theory('equality')], [c_7457, c_7510])).
% 6.72/2.33  tff(c_7542, plain, (![A_1, C_851, D_861]: (k4_zfmisc_1(A_1, k1_xboole_0, C_851, D_861)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7529])).
% 6.72/2.33  tff(c_8182, plain, (![A_1, C_851, D_861]: (k4_zfmisc_1(A_1, '#skF_2', C_851, D_861)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8178, c_8178, c_7542])).
% 6.72/2.33  tff(c_8193, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8178, c_22])).
% 6.72/2.33  tff(c_8445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8182, c_8193])).
% 6.72/2.33  tff(c_8446, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8157])).
% 6.72/2.33  tff(c_7438, plain, (![A_849, B_850]: (k3_zfmisc_1(A_849, B_850, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7425, c_4])).
% 6.72/2.33  tff(c_7535, plain, (![A_849, B_850, D_861]: (k4_zfmisc_1(A_849, B_850, k1_xboole_0, D_861)=k2_zfmisc_1(k1_xboole_0, D_861))), inference(superposition, [status(thm), theory('equality')], [c_7438, c_7510])).
% 6.72/2.33  tff(c_7544, plain, (![A_849, B_850, D_861]: (k4_zfmisc_1(A_849, B_850, k1_xboole_0, D_861)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7535])).
% 6.72/2.33  tff(c_8522, plain, (![A_849, B_850, D_861]: (k4_zfmisc_1(A_849, B_850, '#skF_3', D_861)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8446, c_8446, c_7544])).
% 6.72/2.33  tff(c_8530, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8446, c_22])).
% 6.72/2.33  tff(c_8751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8522, c_8530])).
% 6.72/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.33  
% 6.72/2.33  Inference rules
% 6.72/2.33  ----------------------
% 6.72/2.33  #Ref     : 63
% 6.72/2.33  #Sup     : 2033
% 6.72/2.33  #Fact    : 0
% 6.72/2.33  #Define  : 0
% 6.72/2.33  #Split   : 31
% 6.72/2.33  #Chain   : 0
% 6.72/2.33  #Close   : 0
% 6.72/2.33  
% 6.72/2.33  Ordering : KBO
% 6.72/2.33  
% 6.72/2.33  Simplification rules
% 6.72/2.33  ----------------------
% 6.72/2.33  #Subsume      : 120
% 6.72/2.33  #Demod        : 1853
% 6.72/2.33  #Tautology    : 1374
% 6.72/2.33  #SimpNegUnit  : 81
% 6.72/2.33  #BackRed      : 523
% 6.72/2.33  
% 6.72/2.33  #Partial instantiations: 0
% 6.72/2.33  #Strategies tried      : 1
% 6.72/2.33  
% 6.72/2.33  Timing (in seconds)
% 6.72/2.33  ----------------------
% 6.72/2.34  Preprocessing        : 0.27
% 6.72/2.34  Parsing              : 0.14
% 6.72/2.34  CNF conversion       : 0.02
% 6.72/2.34  Main loop            : 1.21
% 6.72/2.34  Inferencing          : 0.38
% 6.72/2.34  Reduction            : 0.34
% 6.72/2.34  Demodulation         : 0.23
% 6.72/2.34  BG Simplification    : 0.05
% 6.72/2.34  Subsumption          : 0.34
% 6.72/2.34  Abstraction          : 0.05
% 6.72/2.34  MUC search           : 0.00
% 6.72/2.34  Cooper               : 0.00
% 6.72/2.34  Total                : 1.55
% 6.72/2.34  Index Insertion      : 0.00
% 6.72/2.34  Index Deletion       : 0.00
% 6.72/2.34  Index Matching       : 0.00
% 6.72/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
