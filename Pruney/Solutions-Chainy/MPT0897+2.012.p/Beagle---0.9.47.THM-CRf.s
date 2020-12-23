%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:49 EST 2020

% Result     : Theorem 5.62s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  246 (3342 expanded)
%              Number of leaves         :   23 ( 892 expanded)
%              Depth                    :   14
%              Number of atoms          :  374 (10650 expanded)
%              Number of equality atoms :  348 (10624 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_75,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_30,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_102,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_34,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_293,plain,(
    ! [G_53,A_56,E_57,F_59,H_55,C_60,B_54,D_58] :
      ( E_57 = A_56
      | k1_xboole_0 = D_58
      | k1_xboole_0 = C_60
      | k1_xboole_0 = B_54
      | k1_xboole_0 = A_56
      | k4_zfmisc_1(E_57,F_59,G_53,H_55) != k4_zfmisc_1(A_56,B_54,C_60,D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_320,plain,(
    ! [A_56,D_58,C_60,B_54] :
      ( A_56 = '#skF_5'
      | k1_xboole_0 = D_58
      | k1_xboole_0 = C_60
      | k1_xboole_0 = B_54
      | k1_xboole_0 = A_56
      | k4_zfmisc_1(A_56,B_54,C_60,D_58) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_293])).

tff(c_982,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_320])).

tff(c_983,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_982])).

tff(c_1002,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_983])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [B_10,C_11] : k3_zfmisc_1(k1_xboole_0,B_10,C_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [A_34,B_35,C_36,D_37] : k2_zfmisc_1(k3_zfmisc_1(A_34,B_35,C_36),D_37) = k4_zfmisc_1(A_34,B_35,C_36,D_37) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_180,plain,(
    ! [B_10,C_11,D_37] : k4_zfmisc_1(k1_xboole_0,B_10,C_11,D_37) = k2_zfmisc_1(k1_xboole_0,D_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_158])).

tff(c_193,plain,(
    ! [B_10,C_11,D_37] : k4_zfmisc_1(k1_xboole_0,B_10,C_11,D_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_180])).

tff(c_1012,plain,(
    ! [B_10,C_11,D_37] : k4_zfmisc_1('#skF_1',B_10,C_11,D_37) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_1002,c_193])).

tff(c_32,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1017,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_32])).

tff(c_1145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_1017])).

tff(c_1146,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_983])).

tff(c_1148,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1146])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [A_34,B_35,C_36] : k4_zfmisc_1(A_34,B_35,C_36,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_1160,plain,(
    ! [A_34,B_35,C_36] : k4_zfmisc_1(A_34,B_35,C_36,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_1148,c_174])).

tff(c_1164,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_32])).

tff(c_1277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1160,c_1164])).

tff(c_1278,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1146])).

tff(c_1319,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1278])).

tff(c_18,plain,(
    ! [A_9,C_11] : k3_zfmisc_1(A_9,k1_xboole_0,C_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_186,plain,(
    ! [A_9,C_11,D_37] : k4_zfmisc_1(A_9,k1_xboole_0,C_11,D_37) = k2_zfmisc_1(k1_xboole_0,D_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_158])).

tff(c_195,plain,(
    ! [A_9,C_11,D_37] : k4_zfmisc_1(A_9,k1_xboole_0,C_11,D_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_186])).

tff(c_1329,plain,(
    ! [A_9,C_11,D_37] : k4_zfmisc_1(A_9,'#skF_2',C_11,D_37) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_1319,c_195])).

tff(c_1337,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_32])).

tff(c_1553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_1337])).

tff(c_1554,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1278])).

tff(c_16,plain,(
    ! [A_9,B_10] : k3_zfmisc_1(A_9,B_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_183,plain,(
    ! [A_9,B_10,D_37] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_37) = k2_zfmisc_1(k1_xboole_0,D_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_158])).

tff(c_194,plain,(
    ! [A_9,B_10,D_37] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_183])).

tff(c_1567,plain,(
    ! [A_9,B_10,D_37] : k4_zfmisc_1(A_9,B_10,'#skF_3',D_37) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1554,c_1554,c_194])).

tff(c_1574,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1554,c_32])).

tff(c_1756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_1574])).

tff(c_1757,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1763,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1757])).

tff(c_1758,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1764,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1758,c_34])).

tff(c_1820,plain,(
    ! [A_254,B_255,C_256,D_257] : k2_zfmisc_1(k3_zfmisc_1(A_254,B_255,C_256),D_257) = k4_zfmisc_1(A_254,B_255,C_256,D_257) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_relat_1(k2_zfmisc_1(A_3,B_4)) = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2017,plain,(
    ! [A_285,B_286,C_287,D_288] :
      ( k2_relat_1(k4_zfmisc_1(A_285,B_286,C_287,D_288)) = D_288
      | k1_xboole_0 = D_288
      | k3_zfmisc_1(A_285,B_286,C_287) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_8])).

tff(c_2038,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8'
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1764,c_2017])).

tff(c_2045,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2038])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k3_zfmisc_1(A_9,B_10,C_11) != k1_xboole_0
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2094,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2045,c_14])).

tff(c_2097,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2094])).

tff(c_2111,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2097,c_32])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_zfmisc_1(k3_zfmisc_1(A_5,B_6,C_7),D_8) = k4_zfmisc_1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2091,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_8) = k2_zfmisc_1(k1_xboole_0,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_2045,c_12])).

tff(c_2095,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2091])).

tff(c_2275,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2097,c_2095])).

tff(c_2276,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2275,c_1764])).

tff(c_2278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2111,c_2276])).

tff(c_2279,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2094])).

tff(c_2281,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2279])).

tff(c_2296,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_32])).

tff(c_2408,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_8) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_2095])).

tff(c_2409,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_1764])).

tff(c_2411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2296,c_2409])).

tff(c_2412,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2279])).

tff(c_2428,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_32])).

tff(c_2562,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_8) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_2095])).

tff(c_2563,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_1764])).

tff(c_2565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2428,c_2563])).

tff(c_2566,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2038])).

tff(c_2568,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2566])).

tff(c_1829,plain,(
    ! [A_254,B_255,C_256,D_257] :
      ( k2_relat_1(k4_zfmisc_1(A_254,B_255,C_256,D_257)) = D_257
      | k1_xboole_0 = D_257
      | k3_zfmisc_1(A_254,B_255,C_256) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_8])).

tff(c_2593,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2568,c_1829])).

tff(c_2599,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1763,c_2593])).

tff(c_2602,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2599])).

tff(c_2612,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2602,c_14])).

tff(c_2615,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2612])).

tff(c_2631,plain,(
    ! [B_10,C_11] : k3_zfmisc_1('#skF_1',B_10,C_11) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_2615,c_20])).

tff(c_2567,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2038])).

tff(c_2618,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_2567])).

tff(c_2696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2631,c_2618])).

tff(c_2697,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2612])).

tff(c_2699,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2697])).

tff(c_1845,plain,(
    ! [A_9,B_10,D_257] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_257) = k2_zfmisc_1(k1_xboole_0,D_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1820])).

tff(c_1856,plain,(
    ! [A_9,B_10,D_257] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_257) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1845])).

tff(c_2707,plain,(
    ! [A_9,B_10,D_257] : k4_zfmisc_1(A_9,B_10,'#skF_3',D_257) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_2699,c_1856])).

tff(c_2715,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_32])).

tff(c_2842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2707,c_2715])).

tff(c_2843,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2697])).

tff(c_2609,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_8) = k2_zfmisc_1(k1_xboole_0,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_2602,c_12])).

tff(c_2613,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2609])).

tff(c_3026,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_2613])).

tff(c_2861,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_32])).

tff(c_3031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3026,c_2861])).

tff(c_3032,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2599])).

tff(c_1836,plain,(
    ! [A_254,B_255,C_256] : k4_zfmisc_1(A_254,B_255,C_256,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_4])).

tff(c_3042,plain,(
    ! [A_254,B_255,C_256] : k4_zfmisc_1(A_254,B_255,C_256,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3032,c_3032,c_1836])).

tff(c_3047,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3032,c_32])).

tff(c_3212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3042,c_3047])).

tff(c_3213,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2566])).

tff(c_3227,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3213,c_32])).

tff(c_3222,plain,(
    ! [A_254,B_255,C_256] : k4_zfmisc_1(A_254,B_255,C_256,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3213,c_3213,c_1836])).

tff(c_3351,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3222,c_1764])).

tff(c_3353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3227,c_3351])).

tff(c_3355,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1757])).

tff(c_3392,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3355,c_1758,c_34])).

tff(c_3576,plain,(
    ! [C_507,B_501,D_505,H_502,G_500,A_503,E_504,F_506] :
      ( H_502 = D_505
      | k1_xboole_0 = D_505
      | k1_xboole_0 = C_507
      | k1_xboole_0 = B_501
      | k1_xboole_0 = A_503
      | k4_zfmisc_1(E_504,F_506,G_500,H_502) != k4_zfmisc_1(A_503,B_501,C_507,D_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3606,plain,(
    ! [H_502,E_504,F_506,G_500] :
      ( H_502 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_504,F_506,G_500,H_502) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3392,c_3576])).

tff(c_4150,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3606])).

tff(c_4164,plain,(
    ! [B_10,C_11] : k3_zfmisc_1('#skF_1',B_10,C_11) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4150,c_4150,c_20])).

tff(c_3417,plain,(
    ! [A_477,B_478,C_479,D_480] : k2_zfmisc_1(k3_zfmisc_1(A_477,B_478,C_479),D_480) = k4_zfmisc_1(A_477,B_478,C_479,D_480) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3614,plain,(
    ! [A_508,B_509,C_510,D_511] :
      ( k2_relat_1(k4_zfmisc_1(A_508,B_509,C_510,D_511)) = D_511
      | k1_xboole_0 = D_511
      | k3_zfmisc_1(A_508,B_509,C_510) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3417,c_8])).

tff(c_3635,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3392,c_3614])).

tff(c_3642,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3635])).

tff(c_3652,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3642,c_14])).

tff(c_3655,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3652])).

tff(c_3439,plain,(
    ! [B_10,C_11,D_480] : k4_zfmisc_1(k1_xboole_0,B_10,C_11,D_480) = k2_zfmisc_1(k1_xboole_0,D_480) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3417])).

tff(c_3452,plain,(
    ! [B_10,C_11,D_480] : k4_zfmisc_1(k1_xboole_0,B_10,C_11,D_480) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3439])).

tff(c_3663,plain,(
    ! [B_10,C_11,D_480] : k4_zfmisc_1('#skF_1',B_10,C_11,D_480) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3655,c_3655,c_3452])).

tff(c_3668,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3655,c_32])).

tff(c_3782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3663,c_3668])).

tff(c_3784,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3652])).

tff(c_3971,plain,(
    ! [H_502,E_504,F_506,G_500] :
      ( H_502 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k4_zfmisc_1(E_504,F_506,G_500,H_502) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3784,c_3606])).

tff(c_3972,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3971])).

tff(c_3987,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_32])).

tff(c_3445,plain,(
    ! [A_9,C_11,D_480] : k4_zfmisc_1(A_9,k1_xboole_0,C_11,D_480) = k2_zfmisc_1(k1_xboole_0,D_480) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3417])).

tff(c_3454,plain,(
    ! [A_9,C_11,D_480] : k4_zfmisc_1(A_9,k1_xboole_0,C_11,D_480) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3445])).

tff(c_3979,plain,(
    ! [A_9,C_11,D_480] : k4_zfmisc_1(A_9,'#skF_6',C_11,D_480) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_3972,c_3454])).

tff(c_4101,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3979,c_3392])).

tff(c_4103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3987,c_4101])).

tff(c_4105,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3971])).

tff(c_3783,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3652])).

tff(c_3825,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3783])).

tff(c_3840,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_32])).

tff(c_3442,plain,(
    ! [A_9,B_10,D_480] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_480) = k2_zfmisc_1(k1_xboole_0,D_480) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3417])).

tff(c_3453,plain,(
    ! [A_9,B_10,D_480] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_480) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3442])).

tff(c_3834,plain,(
    ! [A_9,B_10,D_480] : k4_zfmisc_1(A_9,B_10,'#skF_7',D_480) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3825,c_3453])).

tff(c_3966,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3834,c_3392])).

tff(c_3968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3840,c_3966])).

tff(c_3969,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3783])).

tff(c_4146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4105,c_3969])).

tff(c_4148,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3635])).

tff(c_4151,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4150,c_4148])).

tff(c_4274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4164,c_4151])).

tff(c_4276,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3606])).

tff(c_4275,plain,(
    ! [H_502,E_504,F_506,G_500] :
      ( k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_4'
      | H_502 = '#skF_4'
      | k4_zfmisc_1(E_504,F_506,G_500,H_502) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_3606])).

tff(c_4277,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4275])).

tff(c_3433,plain,(
    ! [A_477,B_478,C_479] : k4_zfmisc_1(A_477,B_478,C_479,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3417,c_4])).

tff(c_4287,plain,(
    ! [A_477,B_478,C_479] : k4_zfmisc_1(A_477,B_478,C_479,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4277,c_4277,c_3433])).

tff(c_4291,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4277,c_32])).

tff(c_4441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4287,c_4291])).

tff(c_4443,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4275])).

tff(c_3354,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1757])).

tff(c_3360,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3354])).

tff(c_4462,plain,(
    ! [D_622,G_617,C_624,A_620,F_623,E_621,H_619,B_618] :
      ( F_623 = B_618
      | k1_xboole_0 = D_622
      | k1_xboole_0 = C_624
      | k1_xboole_0 = B_618
      | k1_xboole_0 = A_620
      | k4_zfmisc_1(E_621,F_623,G_617,H_619) != k4_zfmisc_1(A_620,B_618,C_624,D_622) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4489,plain,(
    ! [B_618,D_622,C_624,A_620] :
      ( B_618 = '#skF_6'
      | k1_xboole_0 = D_622
      | k1_xboole_0 = C_624
      | k1_xboole_0 = B_618
      | k1_xboole_0 = A_620
      | k4_zfmisc_1(A_620,B_618,C_624,D_622) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3392,c_4462])).

tff(c_4631,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4489])).

tff(c_4632,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4276,c_4443,c_3360,c_4631])).

tff(c_4654,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4632])).

tff(c_4664,plain,(
    ! [A_9,C_11,D_480] : k4_zfmisc_1(A_9,'#skF_2',C_11,D_480) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4654,c_4654,c_3454])).

tff(c_4672,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4654,c_32])).

tff(c_4800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4664,c_4672])).

tff(c_4801,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4632])).

tff(c_4856,plain,(
    ! [A_9,B_10,D_480] : k4_zfmisc_1(A_9,B_10,'#skF_3',D_480) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4801,c_4801,c_3453])).

tff(c_4862,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4801,c_32])).

tff(c_5065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4856,c_4862])).

tff(c_5067,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3354])).

tff(c_5123,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5067,c_1758,c_3355,c_34])).

tff(c_5231,plain,(
    ! [A_726,B_724,F_729,C_730,G_723,H_725,D_728,E_727] :
      ( G_723 = C_730
      | k1_xboole_0 = D_728
      | k1_xboole_0 = C_730
      | k1_xboole_0 = B_724
      | k1_xboole_0 = A_726
      | k4_zfmisc_1(E_727,F_729,G_723,H_725) != k4_zfmisc_1(A_726,B_724,C_730,D_728) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5255,plain,(
    ! [G_723,E_727,F_729,H_725] :
      ( G_723 = '#skF_7'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k4_zfmisc_1(E_727,F_729,G_723,H_725) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5123,c_5231])).

tff(c_5322,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5255])).

tff(c_5144,plain,(
    ! [A_710,B_711,C_712,D_713] : k2_zfmisc_1(k3_zfmisc_1(A_710,B_711,C_712),D_713) = k4_zfmisc_1(A_710,B_711,C_712,D_713) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5166,plain,(
    ! [B_10,C_11,D_713] : k4_zfmisc_1(k1_xboole_0,B_10,C_11,D_713) = k2_zfmisc_1(k1_xboole_0,D_713) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5144])).

tff(c_5179,plain,(
    ! [B_10,C_11,D_713] : k4_zfmisc_1(k1_xboole_0,B_10,C_11,D_713) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5166])).

tff(c_5327,plain,(
    ! [B_10,C_11,D_713] : k4_zfmisc_1('#skF_1',B_10,C_11,D_713) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5322,c_5322,c_5179])).

tff(c_5333,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5322,c_32])).

tff(c_5481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5327,c_5333])).

tff(c_5483,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5255])).

tff(c_5066,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3354])).

tff(c_5252,plain,(
    ! [C_730,D_728,B_724,A_726] :
      ( C_730 = '#skF_7'
      | k1_xboole_0 = D_728
      | k1_xboole_0 = C_730
      | k1_xboole_0 = B_724
      | k1_xboole_0 = A_726
      | k4_zfmisc_1(A_726,B_724,C_730,D_728) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5123,c_5231])).

tff(c_6096,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5252])).

tff(c_6097,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5483,c_5066,c_6096])).

tff(c_6118,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6097])).

tff(c_6136,plain,(
    ! [A_9,C_11] : k3_zfmisc_1(A_9,'#skF_2',C_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6118,c_6118,c_18])).

tff(c_5487,plain,(
    ! [A_760,B_761,C_762,D_763] :
      ( k2_relat_1(k4_zfmisc_1(A_760,B_761,C_762,D_763)) = D_763
      | k1_xboole_0 = D_763
      | k3_zfmisc_1(A_760,B_761,C_762) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5144,c_8])).

tff(c_5508,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5123,c_5487])).

tff(c_5515,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5508])).

tff(c_5522,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5515,c_14])).

tff(c_5528,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5483,c_5522])).

tff(c_5530,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5528])).

tff(c_5585,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5530,c_32])).

tff(c_5519,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_8) = k2_zfmisc_1(k1_xboole_0,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_5515,c_12])).

tff(c_5525,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5519])).

tff(c_5733,plain,(
    ! [D_8] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5530,c_5525])).

tff(c_5734,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5733,c_5123])).

tff(c_5736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5585,c_5734])).

tff(c_5737,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5528])).

tff(c_5738,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5528])).

tff(c_5787,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5737,c_5738])).

tff(c_5741,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5252])).

tff(c_5742,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5483,c_5066,c_5741])).

tff(c_5890,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5737,c_5737,c_5737,c_5742])).

tff(c_5891,plain,(
    '#skF_7' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5787,c_5066,c_5890])).

tff(c_5160,plain,(
    ! [A_710,B_711,C_712] : k4_zfmisc_1(A_710,B_711,C_712,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5144,c_4])).

tff(c_5772,plain,(
    ! [A_710,B_711,C_712] : k4_zfmisc_1(A_710,B_711,C_712,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5737,c_5737,c_5160])).

tff(c_6088,plain,(
    ! [A_710,B_711,C_712] : k4_zfmisc_1(A_710,B_711,C_712,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5891,c_5891,c_5772])).

tff(c_5777,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5737,c_32])).

tff(c_5892,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5891,c_5777])).

tff(c_6091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6088,c_5892])).

tff(c_6093,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5508])).

tff(c_6120,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6118,c_6093])).

tff(c_6200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6136,c_6120])).

tff(c_6201,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6097])).

tff(c_6204,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6201])).

tff(c_6215,plain,(
    ! [A_710,B_711,C_712] : k4_zfmisc_1(A_710,B_711,C_712,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6204,c_6204,c_5160])).

tff(c_6220,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6204,c_32])).

tff(c_6398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6215,c_6220])).

tff(c_6399,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6201])).

tff(c_5169,plain,(
    ! [A_9,B_10,D_713] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_713) = k2_zfmisc_1(k1_xboole_0,D_713) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_5144])).

tff(c_5180,plain,(
    ! [A_9,B_10,D_713] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_713) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5169])).

tff(c_6409,plain,(
    ! [A_9,B_10,D_713] : k4_zfmisc_1(A_9,B_10,'#skF_3',D_713) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6399,c_6399,c_5180])).

tff(c_6416,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6399,c_32])).

tff(c_6616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6409,c_6416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:19:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.62/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.07  
% 5.62/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.07  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.62/2.07  
% 5.62/2.07  %Foreground sorts:
% 5.62/2.07  
% 5.62/2.07  
% 5.62/2.07  %Background operators:
% 5.62/2.07  
% 5.62/2.07  
% 5.62/2.07  %Foreground operators:
% 5.62/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.62/2.07  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 5.62/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.62/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.62/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.62/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.62/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.62/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.62/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.62/2.07  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.62/2.07  tff('#skF_8', type, '#skF_8': $i).
% 5.62/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.62/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.62/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.62/2.07  
% 5.99/2.11  tff(f_88, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 5.99/2.11  tff(f_75, axiom, (![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 5.99/2.11  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.99/2.11  tff(f_57, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 5.99/2.11  tff(f_45, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 5.99/2.11  tff(f_43, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 5.99/2.11  tff(c_30, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.99/2.11  tff(c_102, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_30])).
% 5.99/2.11  tff(c_34, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.99/2.11  tff(c_293, plain, (![G_53, A_56, E_57, F_59, H_55, C_60, B_54, D_58]: (E_57=A_56 | k1_xboole_0=D_58 | k1_xboole_0=C_60 | k1_xboole_0=B_54 | k1_xboole_0=A_56 | k4_zfmisc_1(E_57, F_59, G_53, H_55)!=k4_zfmisc_1(A_56, B_54, C_60, D_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.11  tff(c_320, plain, (![A_56, D_58, C_60, B_54]: (A_56='#skF_5' | k1_xboole_0=D_58 | k1_xboole_0=C_60 | k1_xboole_0=B_54 | k1_xboole_0=A_56 | k4_zfmisc_1(A_56, B_54, C_60, D_58)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_293])).
% 5.99/2.11  tff(c_982, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_320])).
% 5.99/2.11  tff(c_983, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_102, c_982])).
% 5.99/2.11  tff(c_1002, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_983])).
% 5.99/2.11  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.99/2.11  tff(c_20, plain, (![B_10, C_11]: (k3_zfmisc_1(k1_xboole_0, B_10, C_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.99/2.11  tff(c_158, plain, (![A_34, B_35, C_36, D_37]: (k2_zfmisc_1(k3_zfmisc_1(A_34, B_35, C_36), D_37)=k4_zfmisc_1(A_34, B_35, C_36, D_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.99/2.11  tff(c_180, plain, (![B_10, C_11, D_37]: (k4_zfmisc_1(k1_xboole_0, B_10, C_11, D_37)=k2_zfmisc_1(k1_xboole_0, D_37))), inference(superposition, [status(thm), theory('equality')], [c_20, c_158])).
% 5.99/2.11  tff(c_193, plain, (![B_10, C_11, D_37]: (k4_zfmisc_1(k1_xboole_0, B_10, C_11, D_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_180])).
% 5.99/2.11  tff(c_1012, plain, (![B_10, C_11, D_37]: (k4_zfmisc_1('#skF_1', B_10, C_11, D_37)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1002, c_1002, c_193])).
% 5.99/2.11  tff(c_32, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.99/2.11  tff(c_1017, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1002, c_32])).
% 5.99/2.11  tff(c_1145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1012, c_1017])).
% 5.99/2.11  tff(c_1146, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_983])).
% 5.99/2.11  tff(c_1148, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1146])).
% 5.99/2.11  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.99/2.11  tff(c_174, plain, (![A_34, B_35, C_36]: (k4_zfmisc_1(A_34, B_35, C_36, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_158, c_4])).
% 5.99/2.11  tff(c_1160, plain, (![A_34, B_35, C_36]: (k4_zfmisc_1(A_34, B_35, C_36, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_1148, c_174])).
% 5.99/2.11  tff(c_1164, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_32])).
% 5.99/2.11  tff(c_1277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1160, c_1164])).
% 5.99/2.11  tff(c_1278, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1146])).
% 5.99/2.11  tff(c_1319, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1278])).
% 5.99/2.11  tff(c_18, plain, (![A_9, C_11]: (k3_zfmisc_1(A_9, k1_xboole_0, C_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.99/2.11  tff(c_186, plain, (![A_9, C_11, D_37]: (k4_zfmisc_1(A_9, k1_xboole_0, C_11, D_37)=k2_zfmisc_1(k1_xboole_0, D_37))), inference(superposition, [status(thm), theory('equality')], [c_18, c_158])).
% 5.99/2.11  tff(c_195, plain, (![A_9, C_11, D_37]: (k4_zfmisc_1(A_9, k1_xboole_0, C_11, D_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_186])).
% 5.99/2.11  tff(c_1329, plain, (![A_9, C_11, D_37]: (k4_zfmisc_1(A_9, '#skF_2', C_11, D_37)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_1319, c_195])).
% 5.99/2.11  tff(c_1337, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_32])).
% 5.99/2.11  tff(c_1553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1329, c_1337])).
% 5.99/2.11  tff(c_1554, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1278])).
% 5.99/2.11  tff(c_16, plain, (![A_9, B_10]: (k3_zfmisc_1(A_9, B_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.99/2.11  tff(c_183, plain, (![A_9, B_10, D_37]: (k4_zfmisc_1(A_9, B_10, k1_xboole_0, D_37)=k2_zfmisc_1(k1_xboole_0, D_37))), inference(superposition, [status(thm), theory('equality')], [c_16, c_158])).
% 5.99/2.11  tff(c_194, plain, (![A_9, B_10, D_37]: (k4_zfmisc_1(A_9, B_10, k1_xboole_0, D_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_183])).
% 5.99/2.11  tff(c_1567, plain, (![A_9, B_10, D_37]: (k4_zfmisc_1(A_9, B_10, '#skF_3', D_37)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1554, c_1554, c_194])).
% 5.99/2.11  tff(c_1574, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1554, c_32])).
% 5.99/2.11  tff(c_1756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1567, c_1574])).
% 5.99/2.11  tff(c_1757, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 5.99/2.11  tff(c_1763, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_1757])).
% 5.99/2.11  tff(c_1758, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 5.99/2.11  tff(c_1764, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1758, c_34])).
% 5.99/2.11  tff(c_1820, plain, (![A_254, B_255, C_256, D_257]: (k2_zfmisc_1(k3_zfmisc_1(A_254, B_255, C_256), D_257)=k4_zfmisc_1(A_254, B_255, C_256, D_257))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.99/2.11  tff(c_8, plain, (![A_3, B_4]: (k2_relat_1(k2_zfmisc_1(A_3, B_4))=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.99/2.11  tff(c_2017, plain, (![A_285, B_286, C_287, D_288]: (k2_relat_1(k4_zfmisc_1(A_285, B_286, C_287, D_288))=D_288 | k1_xboole_0=D_288 | k3_zfmisc_1(A_285, B_286, C_287)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1820, c_8])).
% 5.99/2.11  tff(c_2038, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1764, c_2017])).
% 5.99/2.11  tff(c_2045, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2038])).
% 5.99/2.11  tff(c_14, plain, (![A_9, B_10, C_11]: (k3_zfmisc_1(A_9, B_10, C_11)!=k1_xboole_0 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.99/2.11  tff(c_2094, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2045, c_14])).
% 5.99/2.11  tff(c_2097, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2094])).
% 5.99/2.11  tff(c_2111, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2097, c_32])).
% 5.99/2.11  tff(c_12, plain, (![A_5, B_6, C_7, D_8]: (k2_zfmisc_1(k3_zfmisc_1(A_5, B_6, C_7), D_8)=k4_zfmisc_1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.99/2.11  tff(c_2091, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_8)=k2_zfmisc_1(k1_xboole_0, D_8))), inference(superposition, [status(thm), theory('equality')], [c_2045, c_12])).
% 5.99/2.11  tff(c_2095, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2091])).
% 5.99/2.11  tff(c_2275, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2097, c_2095])).
% 5.99/2.11  tff(c_2276, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2275, c_1764])).
% 5.99/2.11  tff(c_2278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2111, c_2276])).
% 5.99/2.11  tff(c_2279, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2094])).
% 5.99/2.11  tff(c_2281, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_2279])).
% 5.99/2.11  tff(c_2296, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_32])).
% 5.99/2.11  tff(c_2408, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_8)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_2095])).
% 5.99/2.11  tff(c_2409, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_1764])).
% 5.99/2.11  tff(c_2411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2296, c_2409])).
% 5.99/2.11  tff(c_2412, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2279])).
% 5.99/2.11  tff(c_2428, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_32])).
% 5.99/2.11  tff(c_2562, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_8)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_2095])).
% 5.99/2.11  tff(c_2563, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_1764])).
% 5.99/2.11  tff(c_2565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2428, c_2563])).
% 5.99/2.11  tff(c_2566, plain, (k1_xboole_0='#skF_8' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitRight, [status(thm)], [c_2038])).
% 5.99/2.11  tff(c_2568, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitLeft, [status(thm)], [c_2566])).
% 5.99/2.11  tff(c_1829, plain, (![A_254, B_255, C_256, D_257]: (k2_relat_1(k4_zfmisc_1(A_254, B_255, C_256, D_257))=D_257 | k1_xboole_0=D_257 | k3_zfmisc_1(A_254, B_255, C_256)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1820, c_8])).
% 5.99/2.11  tff(c_2593, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2568, c_1829])).
% 5.99/2.11  tff(c_2599, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1763, c_2593])).
% 5.99/2.11  tff(c_2602, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2599])).
% 5.99/2.11  tff(c_2612, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2602, c_14])).
% 5.99/2.11  tff(c_2615, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2612])).
% 5.99/2.11  tff(c_2631, plain, (![B_10, C_11]: (k3_zfmisc_1('#skF_1', B_10, C_11)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_2615, c_20])).
% 5.99/2.11  tff(c_2567, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2038])).
% 5.99/2.11  tff(c_2618, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_2567])).
% 5.99/2.11  tff(c_2696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2631, c_2618])).
% 5.99/2.11  tff(c_2697, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2612])).
% 5.99/2.11  tff(c_2699, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2697])).
% 5.99/2.11  tff(c_1845, plain, (![A_9, B_10, D_257]: (k4_zfmisc_1(A_9, B_10, k1_xboole_0, D_257)=k2_zfmisc_1(k1_xboole_0, D_257))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1820])).
% 5.99/2.11  tff(c_1856, plain, (![A_9, B_10, D_257]: (k4_zfmisc_1(A_9, B_10, k1_xboole_0, D_257)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1845])).
% 5.99/2.11  tff(c_2707, plain, (![A_9, B_10, D_257]: (k4_zfmisc_1(A_9, B_10, '#skF_3', D_257)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_2699, c_1856])).
% 5.99/2.11  tff(c_2715, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_32])).
% 5.99/2.11  tff(c_2842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2707, c_2715])).
% 5.99/2.11  tff(c_2843, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2697])).
% 5.99/2.11  tff(c_2609, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_8)=k2_zfmisc_1(k1_xboole_0, D_8))), inference(superposition, [status(thm), theory('equality')], [c_2602, c_12])).
% 5.99/2.11  tff(c_2613, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2609])).
% 5.99/2.11  tff(c_3026, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_2613])).
% 5.99/2.11  tff(c_2861, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_32])).
% 5.99/2.11  tff(c_3031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3026, c_2861])).
% 5.99/2.11  tff(c_3032, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2599])).
% 5.99/2.11  tff(c_1836, plain, (![A_254, B_255, C_256]: (k4_zfmisc_1(A_254, B_255, C_256, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1820, c_4])).
% 5.99/2.11  tff(c_3042, plain, (![A_254, B_255, C_256]: (k4_zfmisc_1(A_254, B_255, C_256, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3032, c_3032, c_1836])).
% 5.99/2.11  tff(c_3047, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3032, c_32])).
% 5.99/2.11  tff(c_3212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3042, c_3047])).
% 5.99/2.11  tff(c_3213, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_2566])).
% 5.99/2.11  tff(c_3227, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3213, c_32])).
% 5.99/2.11  tff(c_3222, plain, (![A_254, B_255, C_256]: (k4_zfmisc_1(A_254, B_255, C_256, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3213, c_3213, c_1836])).
% 5.99/2.11  tff(c_3351, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3222, c_1764])).
% 5.99/2.11  tff(c_3353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3227, c_3351])).
% 5.99/2.11  tff(c_3355, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_1757])).
% 5.99/2.11  tff(c_3392, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3355, c_1758, c_34])).
% 5.99/2.11  tff(c_3576, plain, (![C_507, B_501, D_505, H_502, G_500, A_503, E_504, F_506]: (H_502=D_505 | k1_xboole_0=D_505 | k1_xboole_0=C_507 | k1_xboole_0=B_501 | k1_xboole_0=A_503 | k4_zfmisc_1(E_504, F_506, G_500, H_502)!=k4_zfmisc_1(A_503, B_501, C_507, D_505))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.11  tff(c_3606, plain, (![H_502, E_504, F_506, G_500]: (H_502='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_504, F_506, G_500, H_502)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3392, c_3576])).
% 5.99/2.11  tff(c_4150, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3606])).
% 5.99/2.11  tff(c_4164, plain, (![B_10, C_11]: (k3_zfmisc_1('#skF_1', B_10, C_11)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4150, c_4150, c_20])).
% 5.99/2.11  tff(c_3417, plain, (![A_477, B_478, C_479, D_480]: (k2_zfmisc_1(k3_zfmisc_1(A_477, B_478, C_479), D_480)=k4_zfmisc_1(A_477, B_478, C_479, D_480))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.99/2.11  tff(c_3614, plain, (![A_508, B_509, C_510, D_511]: (k2_relat_1(k4_zfmisc_1(A_508, B_509, C_510, D_511))=D_511 | k1_xboole_0=D_511 | k3_zfmisc_1(A_508, B_509, C_510)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3417, c_8])).
% 5.99/2.11  tff(c_3635, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3392, c_3614])).
% 5.99/2.11  tff(c_3642, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3635])).
% 5.99/2.11  tff(c_3652, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3642, c_14])).
% 5.99/2.11  tff(c_3655, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3652])).
% 5.99/2.11  tff(c_3439, plain, (![B_10, C_11, D_480]: (k4_zfmisc_1(k1_xboole_0, B_10, C_11, D_480)=k2_zfmisc_1(k1_xboole_0, D_480))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3417])).
% 5.99/2.11  tff(c_3452, plain, (![B_10, C_11, D_480]: (k4_zfmisc_1(k1_xboole_0, B_10, C_11, D_480)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3439])).
% 5.99/2.11  tff(c_3663, plain, (![B_10, C_11, D_480]: (k4_zfmisc_1('#skF_1', B_10, C_11, D_480)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3655, c_3655, c_3452])).
% 5.99/2.11  tff(c_3668, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3655, c_32])).
% 5.99/2.11  tff(c_3782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3663, c_3668])).
% 5.99/2.11  tff(c_3784, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_3652])).
% 5.99/2.11  tff(c_3971, plain, (![H_502, E_504, F_506, G_500]: (H_502='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k4_zfmisc_1(E_504, F_506, G_500, H_502)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3784, c_3606])).
% 5.99/2.11  tff(c_3972, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_3971])).
% 5.99/2.11  tff(c_3987, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_32])).
% 5.99/2.11  tff(c_3445, plain, (![A_9, C_11, D_480]: (k4_zfmisc_1(A_9, k1_xboole_0, C_11, D_480)=k2_zfmisc_1(k1_xboole_0, D_480))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3417])).
% 5.99/2.11  tff(c_3454, plain, (![A_9, C_11, D_480]: (k4_zfmisc_1(A_9, k1_xboole_0, C_11, D_480)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3445])).
% 5.99/2.11  tff(c_3979, plain, (![A_9, C_11, D_480]: (k4_zfmisc_1(A_9, '#skF_6', C_11, D_480)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_3972, c_3454])).
% 5.99/2.11  tff(c_4101, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3979, c_3392])).
% 5.99/2.11  tff(c_4103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3987, c_4101])).
% 5.99/2.11  tff(c_4105, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_3971])).
% 5.99/2.11  tff(c_3783, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3652])).
% 5.99/2.11  tff(c_3825, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_3783])).
% 5.99/2.11  tff(c_3840, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_32])).
% 5.99/2.11  tff(c_3442, plain, (![A_9, B_10, D_480]: (k4_zfmisc_1(A_9, B_10, k1_xboole_0, D_480)=k2_zfmisc_1(k1_xboole_0, D_480))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3417])).
% 5.99/2.11  tff(c_3453, plain, (![A_9, B_10, D_480]: (k4_zfmisc_1(A_9, B_10, k1_xboole_0, D_480)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3442])).
% 5.99/2.11  tff(c_3834, plain, (![A_9, B_10, D_480]: (k4_zfmisc_1(A_9, B_10, '#skF_7', D_480)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3825, c_3453])).
% 5.99/2.11  tff(c_3966, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3834, c_3392])).
% 5.99/2.11  tff(c_3968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3840, c_3966])).
% 5.99/2.11  tff(c_3969, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3783])).
% 5.99/2.11  tff(c_4146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4105, c_3969])).
% 5.99/2.11  tff(c_4148, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3635])).
% 5.99/2.11  tff(c_4151, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4150, c_4148])).
% 5.99/2.11  tff(c_4274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4164, c_4151])).
% 5.99/2.11  tff(c_4276, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_3606])).
% 5.99/2.11  tff(c_4275, plain, (![H_502, E_504, F_506, G_500]: (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_4' | H_502='#skF_4' | k4_zfmisc_1(E_504, F_506, G_500, H_502)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_3606])).
% 5.99/2.11  tff(c_4277, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_4275])).
% 5.99/2.11  tff(c_3433, plain, (![A_477, B_478, C_479]: (k4_zfmisc_1(A_477, B_478, C_479, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3417, c_4])).
% 5.99/2.11  tff(c_4287, plain, (![A_477, B_478, C_479]: (k4_zfmisc_1(A_477, B_478, C_479, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4277, c_4277, c_3433])).
% 5.99/2.11  tff(c_4291, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4277, c_32])).
% 5.99/2.11  tff(c_4441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4287, c_4291])).
% 5.99/2.11  tff(c_4443, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_4275])).
% 5.99/2.11  tff(c_3354, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_1757])).
% 5.99/2.11  tff(c_3360, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_3354])).
% 5.99/2.11  tff(c_4462, plain, (![D_622, G_617, C_624, A_620, F_623, E_621, H_619, B_618]: (F_623=B_618 | k1_xboole_0=D_622 | k1_xboole_0=C_624 | k1_xboole_0=B_618 | k1_xboole_0=A_620 | k4_zfmisc_1(E_621, F_623, G_617, H_619)!=k4_zfmisc_1(A_620, B_618, C_624, D_622))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.11  tff(c_4489, plain, (![B_618, D_622, C_624, A_620]: (B_618='#skF_6' | k1_xboole_0=D_622 | k1_xboole_0=C_624 | k1_xboole_0=B_618 | k1_xboole_0=A_620 | k4_zfmisc_1(A_620, B_618, C_624, D_622)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3392, c_4462])).
% 5.99/2.11  tff(c_4631, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_4489])).
% 5.99/2.11  tff(c_4632, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4276, c_4443, c_3360, c_4631])).
% 5.99/2.11  tff(c_4654, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4632])).
% 5.99/2.11  tff(c_4664, plain, (![A_9, C_11, D_480]: (k4_zfmisc_1(A_9, '#skF_2', C_11, D_480)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4654, c_4654, c_3454])).
% 5.99/2.11  tff(c_4672, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4654, c_32])).
% 5.99/2.11  tff(c_4800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4664, c_4672])).
% 5.99/2.11  tff(c_4801, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4632])).
% 5.99/2.11  tff(c_4856, plain, (![A_9, B_10, D_480]: (k4_zfmisc_1(A_9, B_10, '#skF_3', D_480)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4801, c_4801, c_3453])).
% 5.99/2.11  tff(c_4862, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4801, c_32])).
% 5.99/2.11  tff(c_5065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4856, c_4862])).
% 5.99/2.11  tff(c_5067, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_3354])).
% 5.99/2.11  tff(c_5123, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5067, c_1758, c_3355, c_34])).
% 5.99/2.11  tff(c_5231, plain, (![A_726, B_724, F_729, C_730, G_723, H_725, D_728, E_727]: (G_723=C_730 | k1_xboole_0=D_728 | k1_xboole_0=C_730 | k1_xboole_0=B_724 | k1_xboole_0=A_726 | k4_zfmisc_1(E_727, F_729, G_723, H_725)!=k4_zfmisc_1(A_726, B_724, C_730, D_728))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.11  tff(c_5255, plain, (![G_723, E_727, F_729, H_725]: (G_723='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k4_zfmisc_1(E_727, F_729, G_723, H_725)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5123, c_5231])).
% 5.99/2.11  tff(c_5322, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_5255])).
% 5.99/2.11  tff(c_5144, plain, (![A_710, B_711, C_712, D_713]: (k2_zfmisc_1(k3_zfmisc_1(A_710, B_711, C_712), D_713)=k4_zfmisc_1(A_710, B_711, C_712, D_713))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.99/2.11  tff(c_5166, plain, (![B_10, C_11, D_713]: (k4_zfmisc_1(k1_xboole_0, B_10, C_11, D_713)=k2_zfmisc_1(k1_xboole_0, D_713))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5144])).
% 5.99/2.11  tff(c_5179, plain, (![B_10, C_11, D_713]: (k4_zfmisc_1(k1_xboole_0, B_10, C_11, D_713)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5166])).
% 5.99/2.11  tff(c_5327, plain, (![B_10, C_11, D_713]: (k4_zfmisc_1('#skF_1', B_10, C_11, D_713)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5322, c_5322, c_5179])).
% 5.99/2.11  tff(c_5333, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5322, c_32])).
% 5.99/2.11  tff(c_5481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5327, c_5333])).
% 5.99/2.11  tff(c_5483, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_5255])).
% 5.99/2.11  tff(c_5066, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_3354])).
% 5.99/2.11  tff(c_5252, plain, (![C_730, D_728, B_724, A_726]: (C_730='#skF_7' | k1_xboole_0=D_728 | k1_xboole_0=C_730 | k1_xboole_0=B_724 | k1_xboole_0=A_726 | k4_zfmisc_1(A_726, B_724, C_730, D_728)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5123, c_5231])).
% 5.99/2.11  tff(c_6096, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_5252])).
% 5.99/2.11  tff(c_6097, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5483, c_5066, c_6096])).
% 5.99/2.11  tff(c_6118, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6097])).
% 5.99/2.11  tff(c_6136, plain, (![A_9, C_11]: (k3_zfmisc_1(A_9, '#skF_2', C_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6118, c_6118, c_18])).
% 5.99/2.11  tff(c_5487, plain, (![A_760, B_761, C_762, D_763]: (k2_relat_1(k4_zfmisc_1(A_760, B_761, C_762, D_763))=D_763 | k1_xboole_0=D_763 | k3_zfmisc_1(A_760, B_761, C_762)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5144, c_8])).
% 5.99/2.11  tff(c_5508, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5123, c_5487])).
% 5.99/2.11  tff(c_5515, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5508])).
% 5.99/2.11  tff(c_5522, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5515, c_14])).
% 5.99/2.11  tff(c_5528, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5483, c_5522])).
% 5.99/2.11  tff(c_5530, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_5528])).
% 5.99/2.11  tff(c_5585, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5530, c_32])).
% 5.99/2.11  tff(c_5519, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_8)=k2_zfmisc_1(k1_xboole_0, D_8))), inference(superposition, [status(thm), theory('equality')], [c_5515, c_12])).
% 5.99/2.11  tff(c_5525, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5519])).
% 5.99/2.11  tff(c_5733, plain, (![D_8]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5530, c_5525])).
% 5.99/2.11  tff(c_5734, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5733, c_5123])).
% 5.99/2.11  tff(c_5736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5585, c_5734])).
% 5.99/2.11  tff(c_5737, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_5528])).
% 5.99/2.11  tff(c_5738, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_5528])).
% 5.99/2.11  tff(c_5787, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5737, c_5738])).
% 5.99/2.11  tff(c_5741, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_5252])).
% 5.99/2.11  tff(c_5742, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5483, c_5066, c_5741])).
% 5.99/2.11  tff(c_5890, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3' | '#skF_7'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5737, c_5737, c_5737, c_5742])).
% 5.99/2.11  tff(c_5891, plain, ('#skF_7'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5787, c_5066, c_5890])).
% 5.99/2.11  tff(c_5160, plain, (![A_710, B_711, C_712]: (k4_zfmisc_1(A_710, B_711, C_712, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5144, c_4])).
% 5.99/2.11  tff(c_5772, plain, (![A_710, B_711, C_712]: (k4_zfmisc_1(A_710, B_711, C_712, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5737, c_5737, c_5160])).
% 5.99/2.11  tff(c_6088, plain, (![A_710, B_711, C_712]: (k4_zfmisc_1(A_710, B_711, C_712, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5891, c_5891, c_5772])).
% 5.99/2.11  tff(c_5777, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5737, c_32])).
% 5.99/2.11  tff(c_5892, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5891, c_5777])).
% 5.99/2.11  tff(c_6091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6088, c_5892])).
% 5.99/2.11  tff(c_6093, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_5508])).
% 5.99/2.11  tff(c_6120, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6118, c_6093])).
% 5.99/2.11  tff(c_6200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6136, c_6120])).
% 5.99/2.11  tff(c_6201, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_6097])).
% 5.99/2.11  tff(c_6204, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_6201])).
% 5.99/2.11  tff(c_6215, plain, (![A_710, B_711, C_712]: (k4_zfmisc_1(A_710, B_711, C_712, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6204, c_6204, c_5160])).
% 5.99/2.11  tff(c_6220, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6204, c_32])).
% 5.99/2.11  tff(c_6398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6215, c_6220])).
% 5.99/2.11  tff(c_6399, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_6201])).
% 5.99/2.11  tff(c_5169, plain, (![A_9, B_10, D_713]: (k4_zfmisc_1(A_9, B_10, k1_xboole_0, D_713)=k2_zfmisc_1(k1_xboole_0, D_713))), inference(superposition, [status(thm), theory('equality')], [c_16, c_5144])).
% 5.99/2.11  tff(c_5180, plain, (![A_9, B_10, D_713]: (k4_zfmisc_1(A_9, B_10, k1_xboole_0, D_713)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5169])).
% 5.99/2.11  tff(c_6409, plain, (![A_9, B_10, D_713]: (k4_zfmisc_1(A_9, B_10, '#skF_3', D_713)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6399, c_6399, c_5180])).
% 5.99/2.11  tff(c_6416, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6399, c_32])).
% 5.99/2.11  tff(c_6616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6409, c_6416])).
% 5.99/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.11  
% 5.99/2.11  Inference rules
% 5.99/2.11  ----------------------
% 5.99/2.11  #Ref     : 57
% 5.99/2.11  #Sup     : 1460
% 5.99/2.11  #Fact    : 0
% 5.99/2.11  #Define  : 0
% 5.99/2.11  #Split   : 36
% 5.99/2.11  #Chain   : 0
% 5.99/2.11  #Close   : 0
% 5.99/2.11  
% 5.99/2.11  Ordering : KBO
% 5.99/2.11  
% 5.99/2.11  Simplification rules
% 5.99/2.11  ----------------------
% 5.99/2.11  #Subsume      : 52
% 5.99/2.11  #Demod        : 1772
% 5.99/2.11  #Tautology    : 1131
% 5.99/2.11  #SimpNegUnit  : 62
% 5.99/2.11  #BackRed      : 660
% 5.99/2.11  
% 5.99/2.11  #Partial instantiations: 0
% 5.99/2.11  #Strategies tried      : 1
% 5.99/2.11  
% 5.99/2.11  Timing (in seconds)
% 5.99/2.11  ----------------------
% 5.99/2.11  Preprocessing        : 0.29
% 5.99/2.11  Parsing              : 0.15
% 5.99/2.11  CNF conversion       : 0.02
% 5.99/2.11  Main loop            : 1.01
% 5.99/2.11  Inferencing          : 0.32
% 5.99/2.11  Reduction            : 0.30
% 5.99/2.11  Demodulation         : 0.20
% 5.99/2.11  BG Simplification    : 0.05
% 5.99/2.11  Subsumption          : 0.26
% 5.99/2.11  Abstraction          : 0.05
% 5.99/2.11  MUC search           : 0.00
% 5.99/2.11  Cooper               : 0.00
% 5.99/2.11  Total                : 1.38
% 5.99/2.11  Index Insertion      : 0.00
% 5.99/2.11  Index Deletion       : 0.00
% 5.99/2.11  Index Matching       : 0.00
% 5.99/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
