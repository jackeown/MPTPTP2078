%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:59 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 227 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 403 expanded)
%              Number of equality atoms :   54 ( 179 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ~ ( k2_tarski(A,B) = k2_tarski(C,D)
        & A != C
        & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(c_44,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_97,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_156,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_325,plain,(
    ! [B_52,D_53,A_54,C_55] :
      ( r2_hidden(B_52,D_53)
      | ~ r2_hidden(k4_tarski(A_54,B_52),k2_zfmisc_1(C_55,D_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_329,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_156,c_325])).

tff(c_121,plain,(
    ! [A_38,B_39] : k2_xboole_0(k1_tarski(A_38),k1_tarski(B_39)) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(k1_tarski(A_30),B_31) = B_31
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_330,plain,(
    ! [A_56,B_57] :
      ( k2_tarski(A_56,B_57) = k1_tarski(B_57)
      | ~ r2_hidden(A_56,k1_tarski(B_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_40])).

tff(c_334,plain,(
    k2_tarski('#skF_6','#skF_8') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_329,c_330])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_362,plain,(
    ! [D_58,A_59,C_60,B_61] :
      ( D_58 = A_59
      | C_60 = A_59
      | k2_tarski(C_60,D_58) != k2_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_393,plain,(
    ! [A_63,A_62,B_64] :
      ( A_63 = A_62
      | A_63 = A_62
      | k2_tarski(A_63,B_64) != k1_tarski(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_362])).

tff(c_399,plain,(
    ! [A_62] :
      ( A_62 = '#skF_6'
      | A_62 = '#skF_6'
      | k1_tarski(A_62) != k1_tarski('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_393])).

tff(c_416,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_6' = '#skF_8' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_399])).

tff(c_419,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_424,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_156])).

tff(c_441,plain,(
    ! [A_68,C_69,B_70,D_71] :
      ( r2_hidden(A_68,C_69)
      | ~ r2_hidden(k4_tarski(A_68,B_70),k2_zfmisc_1(C_69,D_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_444,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_424,c_441])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_444])).

tff(c_449,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_450,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_450])).

tff(c_465,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_470,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_470])).

tff(c_472,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_474,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_72),B_73),B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_766,plain,(
    ! [A_118,B_119] :
      ( r2_hidden(A_118,k1_tarski(B_119))
      | ~ r1_tarski(k2_tarski(A_118,B_119),k1_tarski(B_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_474])).

tff(c_775,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,k1_tarski(A_7))
      | ~ r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_766])).

tff(c_777,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_775])).

tff(c_1056,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( r2_hidden(k4_tarski(A_130,B_131),k2_zfmisc_1(C_132,D_133))
      | ~ r2_hidden(B_131,D_133)
      | ~ r2_hidden(A_130,C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_464,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_620,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_48])).

tff(c_621,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_620])).

tff(c_1062,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_1056,c_621])).

tff(c_1085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_777,c_1062])).

tff(c_1087,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1086,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1088,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1086])).

tff(c_1220,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1319,plain,(
    ! [B_152,D_153,A_154,C_155] :
      ( r2_hidden(B_152,D_153)
      | ~ r2_hidden(k4_tarski(A_154,B_152),k2_zfmisc_1(C_155,D_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1323,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1220,c_1319])).

tff(c_1119,plain,(
    ! [A_138,B_139] :
      ( k2_xboole_0(k1_tarski(A_138),B_139) = B_139
      | ~ r2_hidden(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1126,plain,(
    ! [A_138,B_6] :
      ( k2_tarski(A_138,B_6) = k1_tarski(B_6)
      | ~ r2_hidden(A_138,k1_tarski(B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_10])).

tff(c_1327,plain,(
    k2_tarski('#skF_6','#skF_8') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_1323,c_1126])).

tff(c_1363,plain,(
    ! [D_158,A_159,C_160,B_161] :
      ( D_158 = A_159
      | C_160 = A_159
      | k2_tarski(C_160,D_158) != k2_tarski(A_159,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1394,plain,(
    ! [A_163,A_162,B_164] :
      ( A_163 = A_162
      | A_163 = A_162
      | k2_tarski(A_163,B_164) != k1_tarski(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1363])).

tff(c_1400,plain,(
    ! [A_162] :
      ( A_162 = '#skF_6'
      | A_162 = '#skF_6'
      | k1_tarski(A_162) != k1_tarski('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1327,c_1394])).

tff(c_1417,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_6' = '#skF_8' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1400])).

tff(c_1419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_1088,c_1417])).

tff(c_1421,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1422,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1421,c_1422])).

tff(c_1428,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1483,plain,(
    ! [A_169,B_170] :
      ( r2_hidden(A_169,B_170)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_169),B_170),B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1627,plain,(
    ! [A_206,B_207] :
      ( r2_hidden(A_206,k1_tarski(B_207))
      | ~ r1_tarski(k2_tarski(A_206,B_207),k1_tarski(B_207)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1483])).

tff(c_1636,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,k1_tarski(A_7))
      | ~ r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1627])).

tff(c_1638,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1636])).

tff(c_1890,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( r2_hidden(k4_tarski(A_218,B_219),k2_zfmisc_1(C_220,D_221))
      | ~ r2_hidden(B_219,D_221)
      | ~ r2_hidden(A_218,C_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1420,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1509,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1420,c_48])).

tff(c_1510,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1421,c_1509])).

tff(c_1899,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_1890,c_1510])).

tff(c_1917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_1638,c_1899])).

tff(c_1919,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_46,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1929,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1919,c_46])).

tff(c_2108,plain,(
    ! [A_234,B_235] :
      ( r2_hidden(A_234,B_235)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_234),B_235),B_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2232,plain,(
    ! [A_268,B_269] :
      ( r2_hidden(A_268,k1_tarski(B_269))
      | ~ r1_tarski(k2_tarski(A_268,B_269),k1_tarski(B_269)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2108])).

tff(c_2241,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,k1_tarski(A_7))
      | ~ r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2232])).

tff(c_2243,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2241])).

tff(c_2866,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( r2_hidden(k4_tarski(A_297,B_298),k2_zfmisc_1(C_299,D_300))
      | ~ r2_hidden(B_298,D_300)
      | ~ r2_hidden(A_297,C_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1918,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_42,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2161,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1919,c_1918,c_42])).

tff(c_2872,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_2866,c_2161])).

tff(c_2901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1929,c_2243,c_2872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.85  
% 4.26/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.85  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.26/1.85  
% 4.26/1.85  %Foreground sorts:
% 4.26/1.85  
% 4.26/1.85  
% 4.26/1.85  %Background operators:
% 4.26/1.85  
% 4.26/1.85  
% 4.26/1.85  %Foreground operators:
% 4.26/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.26/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.26/1.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.26/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.26/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.26/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.26/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.26/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.26/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.26/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.26/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.26/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.26/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.26/1.85  
% 4.26/1.87  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 4.26/1.87  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 4.26/1.87  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.26/1.87  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.26/1.87  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.26/1.87  tff(f_62, axiom, (![A, B, C, D]: ~(((k2_tarski(A, B) = k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 4.26/1.87  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.26/1.87  tff(f_74, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 4.26/1.87  tff(c_44, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.26/1.87  tff(c_97, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 4.26/1.87  tff(c_50, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.26/1.87  tff(c_156, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_50])).
% 4.26/1.87  tff(c_325, plain, (![B_52, D_53, A_54, C_55]: (r2_hidden(B_52, D_53) | ~r2_hidden(k4_tarski(A_54, B_52), k2_zfmisc_1(C_55, D_53)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.26/1.87  tff(c_329, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_156, c_325])).
% 4.26/1.87  tff(c_121, plain, (![A_38, B_39]: (k2_xboole_0(k1_tarski(A_38), k1_tarski(B_39))=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.26/1.87  tff(c_40, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), B_31)=B_31 | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.26/1.87  tff(c_330, plain, (![A_56, B_57]: (k2_tarski(A_56, B_57)=k1_tarski(B_57) | ~r2_hidden(A_56, k1_tarski(B_57)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_40])).
% 4.26/1.87  tff(c_334, plain, (k2_tarski('#skF_6', '#skF_8')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_329, c_330])).
% 4.26/1.87  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.87  tff(c_362, plain, (![D_58, A_59, C_60, B_61]: (D_58=A_59 | C_60=A_59 | k2_tarski(C_60, D_58)!=k2_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.26/1.87  tff(c_393, plain, (![A_63, A_62, B_64]: (A_63=A_62 | A_63=A_62 | k2_tarski(A_63, B_64)!=k1_tarski(A_62))), inference(superposition, [status(thm), theory('equality')], [c_12, c_362])).
% 4.26/1.87  tff(c_399, plain, (![A_62]: (A_62='#skF_6' | A_62='#skF_6' | k1_tarski(A_62)!=k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_334, c_393])).
% 4.26/1.87  tff(c_416, plain, ('#skF_6'='#skF_8' | '#skF_6'='#skF_8'), inference(reflexivity, [status(thm), theory('equality')], [c_399])).
% 4.26/1.87  tff(c_419, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_416])).
% 4.26/1.87  tff(c_424, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_156])).
% 4.26/1.87  tff(c_441, plain, (![A_68, C_69, B_70, D_71]: (r2_hidden(A_68, C_69) | ~r2_hidden(k4_tarski(A_68, B_70), k2_zfmisc_1(C_69, D_71)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.26/1.87  tff(c_444, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_424, c_441])).
% 4.26/1.87  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_444])).
% 4.26/1.87  tff(c_449, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_416])).
% 4.26/1.87  tff(c_450, plain, ('#skF_6'!='#skF_8'), inference(splitRight, [status(thm)], [c_416])).
% 4.26/1.87  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_449, c_450])).
% 4.26/1.87  tff(c_465, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_50])).
% 4.26/1.87  tff(c_52, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.26/1.87  tff(c_470, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_52])).
% 4.26/1.87  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_465, c_470])).
% 4.26/1.87  tff(c_472, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 4.26/1.87  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.26/1.87  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.26/1.87  tff(c_474, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | ~r1_tarski(k2_xboole_0(k1_tarski(A_72), B_73), B_73))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.26/1.87  tff(c_766, plain, (![A_118, B_119]: (r2_hidden(A_118, k1_tarski(B_119)) | ~r1_tarski(k2_tarski(A_118, B_119), k1_tarski(B_119)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_474])).
% 4.26/1.87  tff(c_775, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)) | ~r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_766])).
% 4.26/1.87  tff(c_777, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_775])).
% 4.26/1.87  tff(c_1056, plain, (![A_130, B_131, C_132, D_133]: (r2_hidden(k4_tarski(A_130, B_131), k2_zfmisc_1(C_132, D_133)) | ~r2_hidden(B_131, D_133) | ~r2_hidden(A_130, C_132))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.26/1.87  tff(c_464, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 4.26/1.87  tff(c_48, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.26/1.87  tff(c_620, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_48])).
% 4.26/1.87  tff(c_621, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_465, c_620])).
% 4.26/1.87  tff(c_1062, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_1056, c_621])).
% 4.26/1.87  tff(c_1085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_472, c_777, c_1062])).
% 4.26/1.87  tff(c_1087, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 4.26/1.87  tff(c_1086, plain, ('#skF_6'!='#skF_8' | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 4.26/1.87  tff(c_1088, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_1086])).
% 4.26/1.87  tff(c_1220, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_50])).
% 4.26/1.87  tff(c_1319, plain, (![B_152, D_153, A_154, C_155]: (r2_hidden(B_152, D_153) | ~r2_hidden(k4_tarski(A_154, B_152), k2_zfmisc_1(C_155, D_153)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.26/1.87  tff(c_1323, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_1220, c_1319])).
% 4.26/1.87  tff(c_1119, plain, (![A_138, B_139]: (k2_xboole_0(k1_tarski(A_138), B_139)=B_139 | ~r2_hidden(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.26/1.87  tff(c_1126, plain, (![A_138, B_6]: (k2_tarski(A_138, B_6)=k1_tarski(B_6) | ~r2_hidden(A_138, k1_tarski(B_6)))), inference(superposition, [status(thm), theory('equality')], [c_1119, c_10])).
% 4.26/1.87  tff(c_1327, plain, (k2_tarski('#skF_6', '#skF_8')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_1323, c_1126])).
% 4.26/1.87  tff(c_1363, plain, (![D_158, A_159, C_160, B_161]: (D_158=A_159 | C_160=A_159 | k2_tarski(C_160, D_158)!=k2_tarski(A_159, B_161))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.26/1.87  tff(c_1394, plain, (![A_163, A_162, B_164]: (A_163=A_162 | A_163=A_162 | k2_tarski(A_163, B_164)!=k1_tarski(A_162))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1363])).
% 4.26/1.87  tff(c_1400, plain, (![A_162]: (A_162='#skF_6' | A_162='#skF_6' | k1_tarski(A_162)!=k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1327, c_1394])).
% 4.26/1.87  tff(c_1417, plain, ('#skF_6'='#skF_8' | '#skF_6'='#skF_8'), inference(reflexivity, [status(thm), theory('equality')], [c_1400])).
% 4.26/1.87  tff(c_1419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1088, c_1088, c_1417])).
% 4.26/1.87  tff(c_1421, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_50])).
% 4.26/1.87  tff(c_1422, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_52])).
% 4.26/1.87  tff(c_1427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1421, c_1422])).
% 4.26/1.87  tff(c_1428, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 4.26/1.87  tff(c_1483, plain, (![A_169, B_170]: (r2_hidden(A_169, B_170) | ~r1_tarski(k2_xboole_0(k1_tarski(A_169), B_170), B_170))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.26/1.87  tff(c_1627, plain, (![A_206, B_207]: (r2_hidden(A_206, k1_tarski(B_207)) | ~r1_tarski(k2_tarski(A_206, B_207), k1_tarski(B_207)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1483])).
% 4.26/1.87  tff(c_1636, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)) | ~r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1627])).
% 4.26/1.87  tff(c_1638, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1636])).
% 4.26/1.87  tff(c_1890, plain, (![A_218, B_219, C_220, D_221]: (r2_hidden(k4_tarski(A_218, B_219), k2_zfmisc_1(C_220, D_221)) | ~r2_hidden(B_219, D_221) | ~r2_hidden(A_218, C_220))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.26/1.87  tff(c_1420, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 4.26/1.87  tff(c_1509, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1420, c_48])).
% 4.26/1.87  tff(c_1510, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1421, c_1509])).
% 4.26/1.87  tff(c_1899, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_1890, c_1510])).
% 4.26/1.87  tff(c_1917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1428, c_1638, c_1899])).
% 4.26/1.87  tff(c_1919, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_1086])).
% 4.26/1.87  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_3') | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.26/1.87  tff(c_1929, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1919, c_46])).
% 4.26/1.87  tff(c_2108, plain, (![A_234, B_235]: (r2_hidden(A_234, B_235) | ~r1_tarski(k2_xboole_0(k1_tarski(A_234), B_235), B_235))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.26/1.87  tff(c_2232, plain, (![A_268, B_269]: (r2_hidden(A_268, k1_tarski(B_269)) | ~r1_tarski(k2_tarski(A_268, B_269), k1_tarski(B_269)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2108])).
% 4.26/1.87  tff(c_2241, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)) | ~r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2232])).
% 4.26/1.87  tff(c_2243, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2241])).
% 4.26/1.87  tff(c_2866, plain, (![A_297, B_298, C_299, D_300]: (r2_hidden(k4_tarski(A_297, B_298), k2_zfmisc_1(C_299, D_300)) | ~r2_hidden(B_298, D_300) | ~r2_hidden(A_297, C_299))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.26/1.87  tff(c_1918, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_1086])).
% 4.26/1.87  tff(c_42, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.26/1.87  tff(c_2161, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1919, c_1918, c_42])).
% 4.26/1.87  tff(c_2872, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_2866, c_2161])).
% 4.26/1.87  tff(c_2901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1929, c_2243, c_2872])).
% 4.26/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.87  
% 4.26/1.87  Inference rules
% 4.26/1.87  ----------------------
% 4.26/1.87  #Ref     : 13
% 4.26/1.87  #Sup     : 721
% 4.26/1.87  #Fact    : 0
% 4.26/1.87  #Define  : 0
% 4.26/1.87  #Split   : 7
% 4.26/1.87  #Chain   : 0
% 4.26/1.87  #Close   : 0
% 4.26/1.87  
% 4.26/1.87  Ordering : KBO
% 4.26/1.87  
% 4.26/1.87  Simplification rules
% 4.26/1.87  ----------------------
% 4.26/1.87  #Subsume      : 141
% 4.26/1.87  #Demod        : 193
% 4.26/1.87  #Tautology    : 260
% 4.26/1.87  #SimpNegUnit  : 6
% 4.26/1.87  #BackRed      : 10
% 4.26/1.87  
% 4.26/1.87  #Partial instantiations: 0
% 4.26/1.87  #Strategies tried      : 1
% 4.26/1.87  
% 4.26/1.87  Timing (in seconds)
% 4.26/1.87  ----------------------
% 4.26/1.87  Preprocessing        : 0.31
% 4.26/1.87  Parsing              : 0.16
% 4.26/1.87  CNF conversion       : 0.02
% 4.26/1.87  Main loop            : 0.74
% 4.26/1.87  Inferencing          : 0.28
% 4.26/1.87  Reduction            : 0.25
% 4.26/1.87  Demodulation         : 0.20
% 4.26/1.87  BG Simplification    : 0.04
% 4.26/1.87  Subsumption          : 0.12
% 4.26/1.87  Abstraction          : 0.04
% 4.26/1.87  MUC search           : 0.00
% 4.26/1.87  Cooper               : 0.00
% 4.26/1.87  Total                : 1.09
% 4.26/1.87  Index Insertion      : 0.00
% 4.26/1.87  Index Deletion       : 0.00
% 4.26/1.87  Index Matching       : 0.00
% 4.26/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
