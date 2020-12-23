%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:49 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :  153 (1687 expanded)
%              Number of leaves         :   16 ( 435 expanded)
%              Depth                    :   15
%              Number of atoms          :  282 (6288 expanded)
%              Number of equality atoms :  263 (6269 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_58,axiom,(
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

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(c_20,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_101,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_134,plain,(
    ! [D_29,G_31,C_33,H_35,F_30,B_32,E_36,A_34] :
      ( E_36 = A_34
      | k1_xboole_0 = D_29
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_34
      | k4_zfmisc_1(E_36,F_30,G_31,H_35) != k4_zfmisc_1(A_34,B_32,C_33,D_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_137,plain,(
    ! [A_34,D_29,C_33,B_32] :
      ( A_34 = '#skF_5'
      | k1_xboole_0 = D_29
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_34
      | k4_zfmisc_1(A_34,B_32,C_33,D_29) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_134])).

tff(c_482,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_137])).

tff(c_483,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_482])).

tff(c_505,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_10,plain,(
    ! [B_2,C_3,D_4] : k4_zfmisc_1(k1_xboole_0,B_2,C_3,D_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_518,plain,(
    ! [B_2,C_3,D_4] : k4_zfmisc_1('#skF_1',B_2,C_3,D_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_10])).

tff(c_22,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_519,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_22])).

tff(c_577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_519])).

tff(c_578,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_580,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3] : k4_zfmisc_1(A_1,B_2,C_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_593,plain,(
    ! [A_1,B_2,C_3] : k4_zfmisc_1(A_1,B_2,C_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_580,c_4])).

tff(c_595,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_22])).

tff(c_631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_595])).

tff(c_632,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_634,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_8,plain,(
    ! [A_1,C_3,D_4] : k4_zfmisc_1(A_1,k1_xboole_0,C_3,D_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_797,plain,(
    ! [A_1,C_3,D_4] : k4_zfmisc_1(A_1,'#skF_2',C_3,D_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_634,c_8])).

tff(c_800,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_22])).

tff(c_828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_800])).

tff(c_829,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_6,plain,(
    ! [A_1,B_2,D_4] : k4_zfmisc_1(A_1,B_2,k1_xboole_0,D_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_843,plain,(
    ! [A_1,B_2,D_4] : k4_zfmisc_1(A_1,B_2,'#skF_3',D_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_829,c_6])).

tff(c_847,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_22])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_847])).

tff(c_909,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_915,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_909])).

tff(c_910,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_916,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_24])).

tff(c_949,plain,(
    ! [B_140,D_137,F_138,H_143,E_144,C_141,A_142,G_139] :
      ( G_139 = C_141
      | k1_xboole_0 = D_137
      | k1_xboole_0 = C_141
      | k1_xboole_0 = B_140
      | k1_xboole_0 = A_142
      | k4_zfmisc_1(E_144,F_138,G_139,H_143) != k4_zfmisc_1(A_142,B_140,C_141,D_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_955,plain,(
    ! [G_139,E_144,F_138,H_143] :
      ( G_139 = '#skF_7'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_144,F_138,G_139,H_143) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_949])).

tff(c_1101,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_1110,plain,(
    ! [B_2,C_3,D_4] : k4_zfmisc_1('#skF_1',B_2,C_3,D_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_1101,c_10])).

tff(c_1111,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_22])).

tff(c_1164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1111])).

tff(c_1165,plain,(
    ! [G_139,E_144,F_138,H_143] :
      ( k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_8'
      | G_139 = '#skF_7'
      | k4_zfmisc_1(E_144,F_138,G_139,H_143) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_1167,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1165])).

tff(c_1178,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1167,c_22])).

tff(c_1176,plain,(
    ! [A_1,B_2,C_3] : k4_zfmisc_1(A_1,B_2,C_3,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1167,c_1167,c_4])).

tff(c_1192,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_916])).

tff(c_1194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1178,c_1192])).

tff(c_1195,plain,(
    ! [G_139,E_144,F_138,H_143] :
      ( k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | G_139 = '#skF_7'
      | k4_zfmisc_1(E_144,F_138,G_139,H_143) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1165])).

tff(c_1197,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1195])).

tff(c_1206,plain,(
    ! [A_1,C_3,D_4] : k4_zfmisc_1(A_1,'#skF_6',C_3,D_4) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1197,c_8])).

tff(c_1214,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_916])).

tff(c_1209,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_22])).

tff(c_1242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_1209])).

tff(c_1243,plain,(
    ! [G_139,E_144,F_138,H_143] :
      ( k1_xboole_0 = '#skF_7'
      | G_139 = '#skF_7'
      | k4_zfmisc_1(E_144,F_138,G_139,H_143) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1195])).

tff(c_1245,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1243])).

tff(c_1258,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_22])).

tff(c_1254,plain,(
    ! [A_1,B_2,D_4] : k4_zfmisc_1(A_1,B_2,'#skF_7',D_4) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1245,c_6])).

tff(c_1263,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_916])).

tff(c_1271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1258,c_1263])).

tff(c_1273,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1243])).

tff(c_1166,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_1244,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1195])).

tff(c_1196,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1165])).

tff(c_1066,plain,(
    ! [C_165,D_161,A_166,F_162,E_168,B_164,H_167,G_163] :
      ( H_167 = D_161
      | k1_xboole_0 = D_161
      | k1_xboole_0 = C_165
      | k1_xboole_0 = B_164
      | k1_xboole_0 = A_166
      | k4_zfmisc_1(E_168,F_162,G_163,H_167) != k4_zfmisc_1(A_166,B_164,C_165,D_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1072,plain,(
    ! [H_167,E_168,F_162,G_163] :
      ( H_167 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_168,F_162,G_163,H_167) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_1066])).

tff(c_1274,plain,(
    ! [H_167,E_168,F_162,G_163] :
      ( H_167 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k4_zfmisc_1(E_168,F_162,G_163,H_167) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1166,c_1244,c_1196,c_1072])).

tff(c_1275,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1274])).

tff(c_1276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1273,c_1275])).

tff(c_1277,plain,(
    ! [H_167,E_168,F_162,G_163] :
      ( H_167 = '#skF_8'
      | k4_zfmisc_1(E_168,F_162,G_163,H_167) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1274])).

tff(c_1281,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1277])).

tff(c_1283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_915,c_1281])).

tff(c_1284,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_909])).

tff(c_1290,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1284])).

tff(c_1285,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_909])).

tff(c_1291,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_910,c_24])).

tff(c_1402,plain,(
    ! [E_217,D_210,H_216,A_215,C_214,G_212,B_213,F_211] :
      ( F_211 = B_213
      | k1_xboole_0 = D_210
      | k1_xboole_0 = C_214
      | k1_xboole_0 = B_213
      | k1_xboole_0 = A_215
      | k4_zfmisc_1(E_217,F_211,G_212,H_216) != k4_zfmisc_1(A_215,B_213,C_214,D_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1408,plain,(
    ! [F_211,E_217,G_212,H_216] :
      ( F_211 = '#skF_6'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_217,F_211,G_212,H_216) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1291,c_1402])).

tff(c_1476,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1408])).

tff(c_1485,plain,(
    ! [B_2,C_3,D_4] : k4_zfmisc_1('#skF_1',B_2,C_3,D_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1476,c_1476,c_10])).

tff(c_1486,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1476,c_22])).

tff(c_1540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1485,c_1486])).

tff(c_1542,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_1541,plain,(
    ! [F_211,E_217,G_212,H_216] :
      ( k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_4'
      | F_211 = '#skF_6'
      | k4_zfmisc_1(E_217,F_211,G_212,H_216) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_1543,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1541])).

tff(c_1552,plain,(
    ! [A_1,B_2,C_3] : k4_zfmisc_1(A_1,B_2,C_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_1543,c_4])).

tff(c_1554,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_22])).

tff(c_1568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1554])).

tff(c_1570,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1541])).

tff(c_1441,plain,(
    ! [C_222,B_221,A_223,F_219,D_218,G_220,H_224,E_225] :
      ( E_225 = A_223
      | k1_xboole_0 = D_218
      | k1_xboole_0 = C_222
      | k1_xboole_0 = B_221
      | k1_xboole_0 = A_223
      | k4_zfmisc_1(E_225,F_219,G_220,H_224) != k4_zfmisc_1(A_223,B_221,C_222,D_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1447,plain,(
    ! [E_225,F_219,G_220,H_224] :
      ( E_225 = '#skF_1'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_225,F_219,G_220,H_224) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1291,c_1441])).

tff(c_1571,plain,(
    ! [E_225,F_219,G_220,H_224] :
      ( E_225 = '#skF_1'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k4_zfmisc_1(E_225,F_219,G_220,H_224) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1542,c_1570,c_1447])).

tff(c_1572,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1571])).

tff(c_1584,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_22])).

tff(c_1581,plain,(
    ! [A_1,C_3,D_4] : k4_zfmisc_1(A_1,'#skF_6',C_3,D_4) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_1572,c_8])).

tff(c_1611,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1291])).

tff(c_1613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1584,c_1611])).

tff(c_1615,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1571])).

tff(c_1614,plain,(
    ! [E_225,F_219,G_220,H_224] :
      ( k1_xboole_0 = '#skF_7'
      | E_225 = '#skF_1'
      | k4_zfmisc_1(E_225,F_219,G_220,H_224) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1571])).

tff(c_1616,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1614])).

tff(c_1631,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_22])).

tff(c_1627,plain,(
    ! [A_1,B_2,D_4] : k4_zfmisc_1(A_1,B_2,'#skF_7',D_4) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_1616,c_6])).

tff(c_1659,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1627,c_1291])).

tff(c_1683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1631,c_1659])).

tff(c_1685,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1614])).

tff(c_1569,plain,(
    ! [F_211,E_217,G_212,H_216] :
      ( k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | F_211 = '#skF_6'
      | k4_zfmisc_1(E_217,F_211,G_212,H_216) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1541])).

tff(c_1708,plain,(
    ! [F_211,E_217,G_212,H_216] :
      ( F_211 = '#skF_6'
      | k4_zfmisc_1(E_217,F_211,G_212,H_216) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_1685,c_1569])).

tff(c_1711,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1708])).

tff(c_1713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1290,c_1711])).

tff(c_1714,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1284])).

tff(c_1715,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1284])).

tff(c_1720,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1715,c_910,c_1285,c_24])).

tff(c_1792,plain,(
    ! [A_274,C_273,F_270,E_276,B_272,D_269,H_275,G_271] :
      ( G_271 = C_273
      | k1_xboole_0 = D_269
      | k1_xboole_0 = C_273
      | k1_xboole_0 = B_272
      | k1_xboole_0 = A_274
      | k4_zfmisc_1(E_276,F_270,G_271,H_275) != k4_zfmisc_1(A_274,B_272,C_273,D_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1795,plain,(
    ! [C_273,D_269,B_272,A_274] :
      ( C_273 = '#skF_7'
      | k1_xboole_0 = D_269
      | k1_xboole_0 = C_273
      | k1_xboole_0 = B_272
      | k1_xboole_0 = A_274
      | k4_zfmisc_1(A_274,B_272,C_273,D_269) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1720,c_1792])).

tff(c_1829,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1795])).

tff(c_1830,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1714,c_1829])).

tff(c_1849,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1830])).

tff(c_1857,plain,(
    ! [B_2,C_3,D_4] : k4_zfmisc_1('#skF_1',B_2,C_3,D_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1849,c_1849,c_10])).

tff(c_1858,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1849,c_22])).

tff(c_1982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_1858])).

tff(c_1984,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1830])).

tff(c_1753,plain,(
    ! [G_263,A_266,D_261,H_267,F_262,B_264,C_265,E_268] :
      ( F_262 = B_264
      | k1_xboole_0 = D_261
      | k1_xboole_0 = C_265
      | k1_xboole_0 = B_264
      | k1_xboole_0 = A_266
      | k4_zfmisc_1(E_268,F_262,G_263,H_267) != k4_zfmisc_1(A_266,B_264,C_265,D_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1759,plain,(
    ! [F_262,E_268,G_263,H_267] :
      ( F_262 = '#skF_2'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_268,F_262,G_263,H_267) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1720,c_1753])).

tff(c_1985,plain,(
    ! [F_262,E_268,G_263,H_267] :
      ( F_262 = '#skF_2'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(E_268,F_262,G_263,H_267) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1984,c_1759])).

tff(c_1986,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1985])).

tff(c_1993,plain,(
    ! [A_1,C_3,D_4] : k4_zfmisc_1(A_1,'#skF_2',C_3,D_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1986,c_1986,c_8])).

tff(c_1996,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1986,c_22])).

tff(c_2113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1993,c_1996])).

tff(c_2115,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1985])).

tff(c_1983,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1830])).

tff(c_2259,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2115,c_1983])).

tff(c_2260,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2259])).

tff(c_2270,plain,(
    ! [A_1,B_2,C_3] : k4_zfmisc_1(A_1,B_2,C_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2260,c_2260,c_4])).

tff(c_2272,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2260,c_22])).

tff(c_2329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2270,c_2272])).

tff(c_2330,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2259])).

tff(c_2339,plain,(
    ! [A_1,B_2,D_4] : k4_zfmisc_1(A_1,B_2,'#skF_3',D_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_2330,c_6])).

tff(c_2343,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_22])).

tff(c_2401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2339,c_2343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.72  
% 4.44/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.73  %$ k4_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.44/1.73  
% 4.44/1.73  %Foreground sorts:
% 4.44/1.73  
% 4.44/1.73  
% 4.44/1.73  %Background operators:
% 4.44/1.73  
% 4.44/1.73  
% 4.44/1.73  %Foreground operators:
% 4.44/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.44/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.44/1.73  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.44/1.73  tff('#skF_7', type, '#skF_7': $i).
% 4.44/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.44/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.44/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.44/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.44/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.44/1.73  tff('#skF_8', type, '#skF_8': $i).
% 4.44/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.44/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.44/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.44/1.73  
% 4.44/1.75  tff(f_71, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 4.44/1.75  tff(f_58, axiom, (![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 4.44/1.75  tff(f_40, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 4.44/1.75  tff(c_20, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.44/1.75  tff(c_101, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_20])).
% 4.44/1.75  tff(c_24, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.44/1.75  tff(c_134, plain, (![D_29, G_31, C_33, H_35, F_30, B_32, E_36, A_34]: (E_36=A_34 | k1_xboole_0=D_29 | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_34 | k4_zfmisc_1(E_36, F_30, G_31, H_35)!=k4_zfmisc_1(A_34, B_32, C_33, D_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.75  tff(c_137, plain, (![A_34, D_29, C_33, B_32]: (A_34='#skF_5' | k1_xboole_0=D_29 | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_34 | k4_zfmisc_1(A_34, B_32, C_33, D_29)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_134])).
% 4.44/1.75  tff(c_482, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_137])).
% 4.44/1.75  tff(c_483, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_101, c_482])).
% 4.44/1.75  tff(c_505, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_483])).
% 4.44/1.75  tff(c_10, plain, (![B_2, C_3, D_4]: (k4_zfmisc_1(k1_xboole_0, B_2, C_3, D_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.44/1.75  tff(c_518, plain, (![B_2, C_3, D_4]: (k4_zfmisc_1('#skF_1', B_2, C_3, D_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_10])).
% 4.44/1.75  tff(c_22, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.44/1.75  tff(c_519, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_22])).
% 4.44/1.75  tff(c_577, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_518, c_519])).
% 4.44/1.75  tff(c_578, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_483])).
% 4.44/1.75  tff(c_580, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_578])).
% 4.44/1.75  tff(c_4, plain, (![A_1, B_2, C_3]: (k4_zfmisc_1(A_1, B_2, C_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.44/1.75  tff(c_593, plain, (![A_1, B_2, C_3]: (k4_zfmisc_1(A_1, B_2, C_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_580, c_4])).
% 4.44/1.75  tff(c_595, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_580, c_22])).
% 4.44/1.75  tff(c_631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_593, c_595])).
% 4.44/1.75  tff(c_632, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_578])).
% 4.44/1.75  tff(c_634, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_632])).
% 4.44/1.75  tff(c_8, plain, (![A_1, C_3, D_4]: (k4_zfmisc_1(A_1, k1_xboole_0, C_3, D_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.44/1.75  tff(c_797, plain, (![A_1, C_3, D_4]: (k4_zfmisc_1(A_1, '#skF_2', C_3, D_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_634, c_634, c_8])).
% 4.44/1.75  tff(c_800, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_634, c_22])).
% 4.44/1.75  tff(c_828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_797, c_800])).
% 4.44/1.75  tff(c_829, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_632])).
% 4.44/1.75  tff(c_6, plain, (![A_1, B_2, D_4]: (k4_zfmisc_1(A_1, B_2, k1_xboole_0, D_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.44/1.75  tff(c_843, plain, (![A_1, B_2, D_4]: (k4_zfmisc_1(A_1, B_2, '#skF_3', D_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_829, c_829, c_6])).
% 4.44/1.75  tff(c_847, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_829, c_22])).
% 4.44/1.75  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_843, c_847])).
% 4.44/1.75  tff(c_909, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_20])).
% 4.44/1.75  tff(c_915, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_909])).
% 4.44/1.75  tff(c_910, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 4.44/1.75  tff(c_916, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_910, c_24])).
% 4.44/1.75  tff(c_949, plain, (![B_140, D_137, F_138, H_143, E_144, C_141, A_142, G_139]: (G_139=C_141 | k1_xboole_0=D_137 | k1_xboole_0=C_141 | k1_xboole_0=B_140 | k1_xboole_0=A_142 | k4_zfmisc_1(E_144, F_138, G_139, H_143)!=k4_zfmisc_1(A_142, B_140, C_141, D_137))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.75  tff(c_955, plain, (![G_139, E_144, F_138, H_143]: (G_139='#skF_7' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_144, F_138, G_139, H_143)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_916, c_949])).
% 4.44/1.75  tff(c_1101, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_955])).
% 4.44/1.75  tff(c_1110, plain, (![B_2, C_3, D_4]: (k4_zfmisc_1('#skF_1', B_2, C_3, D_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_1101, c_10])).
% 4.44/1.75  tff(c_1111, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_22])).
% 4.44/1.75  tff(c_1164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1111])).
% 4.44/1.75  tff(c_1165, plain, (![G_139, E_144, F_138, H_143]: (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8' | G_139='#skF_7' | k4_zfmisc_1(E_144, F_138, G_139, H_143)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_955])).
% 4.44/1.75  tff(c_1167, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_1165])).
% 4.44/1.75  tff(c_1178, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1167, c_22])).
% 4.44/1.75  tff(c_1176, plain, (![A_1, B_2, C_3]: (k4_zfmisc_1(A_1, B_2, C_3, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1167, c_1167, c_4])).
% 4.44/1.75  tff(c_1192, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1176, c_916])).
% 4.44/1.75  tff(c_1194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1178, c_1192])).
% 4.44/1.75  tff(c_1195, plain, (![G_139, E_144, F_138, H_143]: (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | G_139='#skF_7' | k4_zfmisc_1(E_144, F_138, G_139, H_143)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1165])).
% 4.44/1.75  tff(c_1197, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1195])).
% 4.44/1.75  tff(c_1206, plain, (![A_1, C_3, D_4]: (k4_zfmisc_1(A_1, '#skF_6', C_3, D_4)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1197, c_8])).
% 4.44/1.75  tff(c_1214, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_916])).
% 4.44/1.75  tff(c_1209, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_22])).
% 4.44/1.75  tff(c_1242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1214, c_1209])).
% 4.44/1.75  tff(c_1243, plain, (![G_139, E_144, F_138, H_143]: (k1_xboole_0='#skF_7' | G_139='#skF_7' | k4_zfmisc_1(E_144, F_138, G_139, H_143)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1195])).
% 4.44/1.75  tff(c_1245, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_1243])).
% 4.44/1.75  tff(c_1258, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_22])).
% 4.44/1.75  tff(c_1254, plain, (![A_1, B_2, D_4]: (k4_zfmisc_1(A_1, B_2, '#skF_7', D_4)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1245, c_6])).
% 4.44/1.75  tff(c_1263, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_916])).
% 4.44/1.75  tff(c_1271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1258, c_1263])).
% 4.44/1.75  tff(c_1273, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_1243])).
% 4.44/1.75  tff(c_1166, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_955])).
% 4.44/1.75  tff(c_1244, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_1195])).
% 4.44/1.75  tff(c_1196, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_1165])).
% 4.44/1.75  tff(c_1066, plain, (![C_165, D_161, A_166, F_162, E_168, B_164, H_167, G_163]: (H_167=D_161 | k1_xboole_0=D_161 | k1_xboole_0=C_165 | k1_xboole_0=B_164 | k1_xboole_0=A_166 | k4_zfmisc_1(E_168, F_162, G_163, H_167)!=k4_zfmisc_1(A_166, B_164, C_165, D_161))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.75  tff(c_1072, plain, (![H_167, E_168, F_162, G_163]: (H_167='#skF_8' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_168, F_162, G_163, H_167)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_916, c_1066])).
% 4.44/1.75  tff(c_1274, plain, (![H_167, E_168, F_162, G_163]: (H_167='#skF_8' | k1_xboole_0='#skF_7' | k4_zfmisc_1(E_168, F_162, G_163, H_167)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1166, c_1244, c_1196, c_1072])).
% 4.44/1.75  tff(c_1275, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_1274])).
% 4.44/1.75  tff(c_1276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1273, c_1275])).
% 4.44/1.75  tff(c_1277, plain, (![H_167, E_168, F_162, G_163]: (H_167='#skF_8' | k4_zfmisc_1(E_168, F_162, G_163, H_167)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1274])).
% 4.44/1.75  tff(c_1281, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_1277])).
% 4.44/1.75  tff(c_1283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_915, c_1281])).
% 4.44/1.75  tff(c_1284, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_909])).
% 4.44/1.75  tff(c_1290, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_1284])).
% 4.44/1.75  tff(c_1285, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_909])).
% 4.44/1.75  tff(c_1291, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_910, c_24])).
% 4.44/1.75  tff(c_1402, plain, (![E_217, D_210, H_216, A_215, C_214, G_212, B_213, F_211]: (F_211=B_213 | k1_xboole_0=D_210 | k1_xboole_0=C_214 | k1_xboole_0=B_213 | k1_xboole_0=A_215 | k4_zfmisc_1(E_217, F_211, G_212, H_216)!=k4_zfmisc_1(A_215, B_213, C_214, D_210))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.75  tff(c_1408, plain, (![F_211, E_217, G_212, H_216]: (F_211='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_217, F_211, G_212, H_216)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1291, c_1402])).
% 4.44/1.75  tff(c_1476, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1408])).
% 4.44/1.75  tff(c_1485, plain, (![B_2, C_3, D_4]: (k4_zfmisc_1('#skF_1', B_2, C_3, D_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1476, c_1476, c_10])).
% 4.44/1.75  tff(c_1486, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1476, c_22])).
% 4.44/1.75  tff(c_1540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1485, c_1486])).
% 4.44/1.75  tff(c_1542, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1408])).
% 4.44/1.75  tff(c_1541, plain, (![F_211, E_217, G_212, H_216]: (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_4' | F_211='#skF_6' | k4_zfmisc_1(E_217, F_211, G_212, H_216)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1408])).
% 4.44/1.75  tff(c_1543, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1541])).
% 4.44/1.75  tff(c_1552, plain, (![A_1, B_2, C_3]: (k4_zfmisc_1(A_1, B_2, C_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_1543, c_4])).
% 4.44/1.75  tff(c_1554, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_22])).
% 4.44/1.75  tff(c_1568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1552, c_1554])).
% 4.44/1.75  tff(c_1570, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1541])).
% 4.44/1.75  tff(c_1441, plain, (![C_222, B_221, A_223, F_219, D_218, G_220, H_224, E_225]: (E_225=A_223 | k1_xboole_0=D_218 | k1_xboole_0=C_222 | k1_xboole_0=B_221 | k1_xboole_0=A_223 | k4_zfmisc_1(E_225, F_219, G_220, H_224)!=k4_zfmisc_1(A_223, B_221, C_222, D_218))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.75  tff(c_1447, plain, (![E_225, F_219, G_220, H_224]: (E_225='#skF_1' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_225, F_219, G_220, H_224)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1291, c_1441])).
% 4.44/1.75  tff(c_1571, plain, (![E_225, F_219, G_220, H_224]: (E_225='#skF_1' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k4_zfmisc_1(E_225, F_219, G_220, H_224)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1542, c_1570, c_1447])).
% 4.44/1.75  tff(c_1572, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1571])).
% 4.44/1.75  tff(c_1584, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_22])).
% 4.44/1.75  tff(c_1581, plain, (![A_1, C_3, D_4]: (k4_zfmisc_1(A_1, '#skF_6', C_3, D_4)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_1572, c_8])).
% 4.44/1.75  tff(c_1611, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1291])).
% 4.44/1.75  tff(c_1613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1584, c_1611])).
% 4.44/1.75  tff(c_1615, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_1571])).
% 4.44/1.75  tff(c_1614, plain, (![E_225, F_219, G_220, H_224]: (k1_xboole_0='#skF_7' | E_225='#skF_1' | k4_zfmisc_1(E_225, F_219, G_220, H_224)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1571])).
% 4.44/1.75  tff(c_1616, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_1614])).
% 4.44/1.75  tff(c_1631, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_22])).
% 4.44/1.75  tff(c_1627, plain, (![A_1, B_2, D_4]: (k4_zfmisc_1(A_1, B_2, '#skF_7', D_4)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_1616, c_6])).
% 4.44/1.75  tff(c_1659, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1627, c_1291])).
% 4.44/1.75  tff(c_1683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1631, c_1659])).
% 4.44/1.75  tff(c_1685, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_1614])).
% 4.44/1.75  tff(c_1569, plain, (![F_211, E_217, G_212, H_216]: (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | F_211='#skF_6' | k4_zfmisc_1(E_217, F_211, G_212, H_216)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1541])).
% 4.44/1.75  tff(c_1708, plain, (![F_211, E_217, G_212, H_216]: (F_211='#skF_6' | k4_zfmisc_1(E_217, F_211, G_212, H_216)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1615, c_1685, c_1569])).
% 4.44/1.75  tff(c_1711, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_1708])).
% 4.44/1.75  tff(c_1713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1290, c_1711])).
% 4.44/1.75  tff(c_1714, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_1284])).
% 4.44/1.75  tff(c_1715, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_1284])).
% 4.44/1.75  tff(c_1720, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1715, c_910, c_1285, c_24])).
% 4.44/1.75  tff(c_1792, plain, (![A_274, C_273, F_270, E_276, B_272, D_269, H_275, G_271]: (G_271=C_273 | k1_xboole_0=D_269 | k1_xboole_0=C_273 | k1_xboole_0=B_272 | k1_xboole_0=A_274 | k4_zfmisc_1(E_276, F_270, G_271, H_275)!=k4_zfmisc_1(A_274, B_272, C_273, D_269))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.75  tff(c_1795, plain, (![C_273, D_269, B_272, A_274]: (C_273='#skF_7' | k1_xboole_0=D_269 | k1_xboole_0=C_273 | k1_xboole_0=B_272 | k1_xboole_0=A_274 | k4_zfmisc_1(A_274, B_272, C_273, D_269)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1720, c_1792])).
% 4.44/1.75  tff(c_1829, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1795])).
% 4.44/1.75  tff(c_1830, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1714, c_1829])).
% 4.44/1.75  tff(c_1849, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1830])).
% 4.44/1.75  tff(c_1857, plain, (![B_2, C_3, D_4]: (k4_zfmisc_1('#skF_1', B_2, C_3, D_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1849, c_1849, c_10])).
% 4.44/1.75  tff(c_1858, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1849, c_22])).
% 4.44/1.75  tff(c_1982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1857, c_1858])).
% 4.44/1.75  tff(c_1984, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1830])).
% 4.44/1.75  tff(c_1753, plain, (![G_263, A_266, D_261, H_267, F_262, B_264, C_265, E_268]: (F_262=B_264 | k1_xboole_0=D_261 | k1_xboole_0=C_265 | k1_xboole_0=B_264 | k1_xboole_0=A_266 | k4_zfmisc_1(E_268, F_262, G_263, H_267)!=k4_zfmisc_1(A_266, B_264, C_265, D_261))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.75  tff(c_1759, plain, (![F_262, E_268, G_263, H_267]: (F_262='#skF_2' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_268, F_262, G_263, H_267)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1720, c_1753])).
% 4.44/1.75  tff(c_1985, plain, (![F_262, E_268, G_263, H_267]: (F_262='#skF_2' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k4_zfmisc_1(E_268, F_262, G_263, H_267)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1984, c_1759])).
% 4.44/1.75  tff(c_1986, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1985])).
% 4.44/1.75  tff(c_1993, plain, (![A_1, C_3, D_4]: (k4_zfmisc_1(A_1, '#skF_2', C_3, D_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1986, c_1986, c_8])).
% 4.44/1.75  tff(c_1996, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1986, c_22])).
% 4.44/1.75  tff(c_2113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1993, c_1996])).
% 4.44/1.75  tff(c_2115, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1985])).
% 4.44/1.75  tff(c_1983, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1830])).
% 4.44/1.75  tff(c_2259, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2115, c_1983])).
% 4.44/1.75  tff(c_2260, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2259])).
% 4.44/1.75  tff(c_2270, plain, (![A_1, B_2, C_3]: (k4_zfmisc_1(A_1, B_2, C_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2260, c_2260, c_4])).
% 4.44/1.75  tff(c_2272, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2260, c_22])).
% 4.44/1.75  tff(c_2329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2270, c_2272])).
% 4.44/1.75  tff(c_2330, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2259])).
% 4.44/1.75  tff(c_2339, plain, (![A_1, B_2, D_4]: (k4_zfmisc_1(A_1, B_2, '#skF_3', D_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2330, c_2330, c_6])).
% 4.44/1.75  tff(c_2343, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2330, c_22])).
% 4.44/1.75  tff(c_2401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2339, c_2343])).
% 4.44/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.75  
% 4.44/1.75  Inference rules
% 4.44/1.75  ----------------------
% 4.44/1.75  #Ref     : 25
% 4.44/1.75  #Sup     : 528
% 4.44/1.75  #Fact    : 0
% 4.44/1.75  #Define  : 0
% 4.44/1.75  #Split   : 27
% 4.44/1.75  #Chain   : 0
% 4.44/1.75  #Close   : 0
% 4.44/1.75  
% 4.44/1.75  Ordering : KBO
% 4.44/1.75  
% 4.44/1.75  Simplification rules
% 4.44/1.75  ----------------------
% 4.44/1.75  #Subsume      : 83
% 4.44/1.75  #Demod        : 790
% 4.44/1.75  #Tautology    : 436
% 4.44/1.75  #SimpNegUnit  : 26
% 4.44/1.75  #BackRed      : 289
% 4.44/1.75  
% 4.44/1.75  #Partial instantiations: 0
% 4.44/1.75  #Strategies tried      : 1
% 4.44/1.75  
% 4.44/1.75  Timing (in seconds)
% 4.44/1.75  ----------------------
% 4.44/1.75  Preprocessing        : 0.28
% 4.44/1.75  Parsing              : 0.14
% 4.44/1.75  CNF conversion       : 0.02
% 4.44/1.75  Main loop            : 0.70
% 4.44/1.75  Inferencing          : 0.19
% 4.44/1.75  Reduction            : 0.18
% 4.44/1.75  Demodulation         : 0.13
% 4.44/1.75  BG Simplification    : 0.03
% 4.44/1.75  Subsumption          : 0.24
% 4.44/1.75  Abstraction          : 0.03
% 4.44/1.75  MUC search           : 0.00
% 4.44/1.75  Cooper               : 0.00
% 4.44/1.75  Total                : 1.02
% 4.44/1.75  Index Insertion      : 0.00
% 4.44/1.75  Index Deletion       : 0.00
% 4.44/1.75  Index Matching       : 0.00
% 4.44/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
