%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:43 EST 2020

% Result     : Theorem 5.55s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  229 ( 917 expanded)
%              Number of leaves         :   28 ( 282 expanded)
%              Depth                    :   17
%              Number of atoms          :  404 (2203 expanded)
%              Number of equality atoms :  160 (1052 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_14,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1424,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1479,plain,(
    ! [A_370,B_371,C_372,D_373] :
      ( r2_hidden(k4_tarski(A_370,B_371),k2_zfmisc_1(C_372,D_373))
      | ~ r2_hidden(B_371,D_373)
      | ~ r2_hidden(A_370,C_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1493,plain,(
    ! [A_370,B_371] :
      ( r2_hidden(k4_tarski(A_370,B_371),k1_xboole_0)
      | ~ r2_hidden(B_371,'#skF_12')
      | ~ r2_hidden(A_370,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_1479])).

tff(c_1497,plain,(
    ! [A_374,B_375] :
      ( r2_hidden(k4_tarski(A_374,B_375),k1_xboole_0)
      | ~ r2_hidden(B_375,'#skF_12')
      | ~ r2_hidden(A_374,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_1479])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1441,plain,(
    ! [A_346,B_347,C_348] :
      ( ~ r1_xboole_0(A_346,B_347)
      | ~ r2_hidden(C_348,B_347)
      | ~ r2_hidden(C_348,A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1444,plain,(
    ! [C_348,B_2,A_1] :
      ( ~ r2_hidden(C_348,B_2)
      | ~ r2_hidden(C_348,A_1)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1441])).

tff(c_3492,plain,(
    ! [A_546,B_547,A_548] :
      ( ~ r2_hidden(k4_tarski(A_546,B_547),A_548)
      | k3_xboole_0(A_548,k1_xboole_0) != k1_xboole_0
      | ~ r2_hidden(B_547,'#skF_12')
      | ~ r2_hidden(A_546,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_1497,c_1444])).

tff(c_3506,plain,(
    ! [B_371,A_370] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
      | ~ r2_hidden(B_371,'#skF_12')
      | ~ r2_hidden(A_370,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_1493,c_3492])).

tff(c_3517,plain,(
    ! [B_371,A_370] :
      ( ~ r2_hidden(B_371,'#skF_12')
      | ~ r2_hidden(A_370,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3506])).

tff(c_3523,plain,(
    ! [A_549] : ~ r2_hidden(A_549,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_3517])).

tff(c_3555,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_14,c_3523])).

tff(c_3565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3555])).

tff(c_3566,plain,(
    ! [B_371] : ~ r2_hidden(B_371,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_3517])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_78,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_132,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( r2_hidden(k4_tarski(A_85,B_86),k2_zfmisc_1(C_87,D_88))
      | ~ r2_hidden(B_86,D_88)
      | ~ r2_hidden(A_85,C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_143,plain,(
    ! [A_85,B_86] :
      ( r2_hidden(k4_tarski(A_85,B_86),k1_xboole_0)
      | ~ r2_hidden(B_86,'#skF_12')
      | ~ r2_hidden(A_85,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_132])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,B_61)
      | ~ r2_hidden(C_62,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [C_75,B_76,A_77] :
      ( ~ r2_hidden(C_75,B_76)
      | ~ r2_hidden(C_75,A_77)
      | k3_xboole_0(A_77,B_76) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_113,plain,(
    ! [A_80,B_81,A_82] :
      ( ~ r2_hidden('#skF_1'(A_80,B_81),A_82)
      | k3_xboole_0(A_82,A_80) != k1_xboole_0
      | r1_xboole_0(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_12,c_97])).

tff(c_116,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,A_5) != k1_xboole_0
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_113])).

tff(c_124,plain,(
    ! [A_83,B_84] :
      ( k1_xboole_0 != A_83
      | r1_xboole_0(A_83,B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [C_93,B_94,A_95] :
      ( ~ r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | k1_xboole_0 != A_95 ) ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_261,plain,(
    ! [A_107,B_108,A_109] :
      ( ~ r2_hidden('#skF_1'(A_107,B_108),A_109)
      | k1_xboole_0 != A_109
      | r1_xboole_0(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_10,c_173])).

tff(c_285,plain,(
    ! [B_113,A_114] :
      ( k1_xboole_0 != B_113
      | r1_xboole_0(A_114,B_113) ) ),
    inference(resolution,[status(thm)],[c_10,c_261])).

tff(c_294,plain,(
    ! [C_115,B_116,A_117] :
      ( ~ r2_hidden(C_115,B_116)
      | ~ r2_hidden(C_115,A_117)
      | k1_xboole_0 != B_116 ) ),
    inference(resolution,[status(thm)],[c_285,c_8])).

tff(c_326,plain,(
    ! [A_119,B_120,A_121] :
      ( ~ r2_hidden(k4_tarski(A_119,B_120),A_121)
      | ~ r2_hidden(B_120,'#skF_12')
      | ~ r2_hidden(A_119,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_143,c_294])).

tff(c_333,plain,(
    ! [B_86,A_85] :
      ( ~ r2_hidden(B_86,'#skF_12')
      | ~ r2_hidden(A_85,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_143,c_326])).

tff(c_337,plain,(
    ! [A_122] : ~ r2_hidden(A_122,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_353,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_14,c_337])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_353])).

tff(c_364,plain,(
    ! [B_123] : ~ r2_hidden(B_123,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_380,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_14,c_364])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_380])).

tff(c_388,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_390,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_395,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_14])).

tff(c_20,plain,(
    ! [A_12,B_13,D_39] :
      ( r2_hidden('#skF_8'(A_12,B_13,k2_zfmisc_1(A_12,B_13),D_39),B_13)
      | ~ r2_hidden(D_39,k2_zfmisc_1(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_12,B_13,D_39] :
      ( r2_hidden('#skF_7'(A_12,B_13,k2_zfmisc_1(A_12,B_13),D_39),A_12)
      | ~ r2_hidden(D_39,k2_zfmisc_1(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_515,plain,(
    ! [A_166,B_167,D_168] :
      ( r2_hidden('#skF_7'(A_166,B_167,k2_zfmisc_1(A_166,B_167),D_168),A_166)
      | ~ r2_hidden(D_168,k2_zfmisc_1(A_166,B_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_404,plain,(
    ! [A_128,B_129] :
      ( r1_xboole_0(A_128,B_129)
      | k3_xboole_0(A_128,B_129) != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_4])).

tff(c_424,plain,(
    ! [C_144,B_145,A_146] :
      ( ~ r2_hidden(C_144,B_145)
      | ~ r2_hidden(C_144,A_146)
      | k3_xboole_0(A_146,B_145) != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_404,c_8])).

tff(c_443,plain,(
    ! [A_149,B_150,A_151] :
      ( ~ r2_hidden('#skF_1'(A_149,B_150),A_151)
      | k3_xboole_0(A_151,A_149) != '#skF_10'
      | r1_xboole_0(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_12,c_424])).

tff(c_446,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,A_5) != '#skF_10'
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_443])).

tff(c_458,plain,(
    ! [A_155,B_156] :
      ( A_155 != '#skF_10'
      | r1_xboole_0(A_155,B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_446])).

tff(c_465,plain,(
    ! [C_9,B_156,A_155] :
      ( ~ r2_hidden(C_9,B_156)
      | ~ r2_hidden(C_9,A_155)
      | A_155 != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_458,c_8])).

tff(c_723,plain,(
    ! [A_214,B_215,D_216,A_217] :
      ( ~ r2_hidden('#skF_7'(A_214,B_215,k2_zfmisc_1(A_214,B_215),D_216),A_217)
      | A_217 != '#skF_10'
      | ~ r2_hidden(D_216,k2_zfmisc_1(A_214,B_215)) ) ),
    inference(resolution,[status(thm)],[c_515,c_465])).

tff(c_729,plain,(
    ! [A_218,D_219,B_220] :
      ( A_218 != '#skF_10'
      | ~ r2_hidden(D_219,k2_zfmisc_1(A_218,B_220)) ) ),
    inference(resolution,[status(thm)],[c_22,c_723])).

tff(c_785,plain,(
    ! [A_221,B_222] :
      ( A_221 != '#skF_10'
      | k2_zfmisc_1(A_221,B_222) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_395,c_729])).

tff(c_727,plain,(
    ! [A_12,D_39,B_13] :
      ( A_12 != '#skF_10'
      | ~ r2_hidden(D_39,k2_zfmisc_1(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_22,c_723])).

tff(c_791,plain,(
    ! [A_221,D_39] :
      ( A_221 != '#skF_10'
      | ~ r2_hidden(D_39,'#skF_10')
      | A_221 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_727])).

tff(c_880,plain,(
    ! [A_221] :
      ( A_221 != '#skF_10'
      | A_221 != '#skF_10' ) ),
    inference(splitLeft,[status(thm)],[c_791])).

tff(c_886,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_880])).

tff(c_888,plain,(
    ! [D_237] : ~ r2_hidden(D_237,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_937,plain,(
    ! [D_238,A_239] : ~ r2_hidden(D_238,k2_zfmisc_1(A_239,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_20,c_888])).

tff(c_993,plain,(
    ! [A_239] : k2_zfmisc_1(A_239,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_395,c_937])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_70,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_392,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_70])).

tff(c_999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_392])).

tff(c_1000,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_1007,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_14])).

tff(c_1155,plain,(
    ! [A_284,B_285,D_286] :
      ( r2_hidden('#skF_7'(A_284,B_285,k2_zfmisc_1(A_284,B_285),D_286),A_284)
      | ~ r2_hidden(D_286,k2_zfmisc_1(A_284,B_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1003,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_4])).

tff(c_1021,plain,(
    ! [A_245,B_246,C_247] :
      ( ~ r1_xboole_0(A_245,B_246)
      | ~ r2_hidden(C_247,B_246)
      | ~ r2_hidden(C_247,A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1027,plain,(
    ! [C_256,B_257,A_258] :
      ( ~ r2_hidden(C_256,B_257)
      | ~ r2_hidden(C_256,A_258)
      | k3_xboole_0(A_258,B_257) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1003,c_1021])).

tff(c_1055,plain,(
    ! [A_265,B_266,A_267] :
      ( ~ r2_hidden('#skF_1'(A_265,B_266),A_267)
      | k3_xboole_0(A_267,A_265) != '#skF_9'
      | r1_xboole_0(A_265,B_266) ) ),
    inference(resolution,[status(thm)],[c_12,c_1027])).

tff(c_1058,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,A_5) != '#skF_9'
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_1055])).

tff(c_1066,plain,(
    ! [A_268,B_269] :
      ( A_268 != '#skF_9'
      | r1_xboole_0(A_268,B_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1058])).

tff(c_1072,plain,(
    ! [C_9,B_269,A_268] :
      ( ~ r2_hidden(C_9,B_269)
      | ~ r2_hidden(C_9,A_268)
      | A_268 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1066,c_8])).

tff(c_1357,plain,(
    ! [A_333,B_334,D_335,A_336] :
      ( ~ r2_hidden('#skF_7'(A_333,B_334,k2_zfmisc_1(A_333,B_334),D_335),A_336)
      | A_336 != '#skF_9'
      | ~ r2_hidden(D_335,k2_zfmisc_1(A_333,B_334)) ) ),
    inference(resolution,[status(thm)],[c_1155,c_1072])).

tff(c_1363,plain,(
    ! [A_337,D_338,B_339] :
      ( A_337 != '#skF_9'
      | ~ r2_hidden(D_338,k2_zfmisc_1(A_337,B_339)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1357])).

tff(c_1418,plain,(
    ! [B_339] : k2_zfmisc_1('#skF_9',B_339) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1007,c_1363])).

tff(c_1004,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_70])).

tff(c_1421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1418,c_1004])).

tff(c_1423,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1539,plain,(
    ! [A_377,B_378] :
      ( r2_hidden(k4_tarski(A_377,B_378),k1_xboole_0)
      | ~ r2_hidden(B_378,'#skF_10')
      | ~ r2_hidden(A_377,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_1479])).

tff(c_1445,plain,(
    ! [B_349,D_350,A_351,C_352] :
      ( r2_hidden(B_349,D_350)
      | ~ r2_hidden(k4_tarski(A_351,B_349),k2_zfmisc_1(C_352,D_350)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1451,plain,(
    ! [B_349,A_351] :
      ( r2_hidden(B_349,'#skF_12')
      | ~ r2_hidden(k4_tarski(A_351,B_349),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_1445])).

tff(c_1558,plain,(
    ! [B_378,A_377] :
      ( r2_hidden(B_378,'#skF_12')
      | ~ r2_hidden(B_378,'#skF_10')
      | ~ r2_hidden(A_377,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1539,c_1451])).

tff(c_2363,plain,(
    ! [A_377] : ~ r2_hidden(A_377,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1558])).

tff(c_1454,plain,(
    ! [A_357,C_358,B_359,D_360] :
      ( r2_hidden(A_357,C_358)
      | ~ r2_hidden(k4_tarski(A_357,B_359),k2_zfmisc_1(C_358,D_360)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1457,plain,(
    ! [A_357,B_359] :
      ( r2_hidden(A_357,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_357,B_359),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_1454])).

tff(c_1513,plain,(
    ! [A_374,B_375] :
      ( r2_hidden(A_374,'#skF_9')
      | ~ r2_hidden(B_375,'#skF_12')
      | ~ r2_hidden(A_374,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_1497,c_1457])).

tff(c_1519,plain,(
    ! [B_376] : ~ r2_hidden(B_376,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_1513])).

tff(c_1531,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_14,c_1519])).

tff(c_1537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1531])).

tff(c_1559,plain,(
    ! [A_379] :
      ( r2_hidden(A_379,'#skF_9')
      | ~ r2_hidden(A_379,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_1513])).

tff(c_1571,plain,
    ( r2_hidden('#skF_2'('#skF_11'),'#skF_9')
    | k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_14,c_1559])).

tff(c_1576,plain,(
    r2_hidden('#skF_2'('#skF_11'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1571])).

tff(c_2370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2363,c_1576])).

tff(c_2372,plain,(
    ! [B_451] :
      ( r2_hidden(B_451,'#skF_12')
      | ~ r2_hidden(B_451,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_1558])).

tff(c_2392,plain,
    ( r2_hidden('#skF_2'('#skF_10'),'#skF_12')
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_14,c_2372])).

tff(c_2393,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_2392])).

tff(c_2410,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2393,c_68])).

tff(c_2411,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2393,c_14])).

tff(c_2412,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2393,c_66])).

tff(c_1448,plain,(
    ! [B_349,A_351] :
      ( r2_hidden(B_349,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_351,B_349),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_1445])).

tff(c_1515,plain,(
    ! [B_375,A_374] :
      ( r2_hidden(B_375,'#skF_10')
      | ~ r2_hidden(B_375,'#skF_12')
      | ~ r2_hidden(A_374,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_1497,c_1448])).

tff(c_2558,plain,(
    ! [A_478] : ~ r2_hidden(A_478,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1515])).

tff(c_2574,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2411,c_2558])).

tff(c_2596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2412,c_2574])).

tff(c_2597,plain,(
    ! [B_375] :
      ( r2_hidden(B_375,'#skF_10')
      | ~ r2_hidden(B_375,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_1515])).

tff(c_2648,plain,(
    ! [C_493,B_494,A_495] :
      ( ~ r2_hidden(C_493,B_494)
      | ~ r2_hidden(C_493,A_495)
      | k3_xboole_0(A_495,B_494) != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2393,c_1444])).

tff(c_2976,plain,(
    ! [B_517,A_518] :
      ( ~ r2_hidden(B_517,A_518)
      | k3_xboole_0(A_518,'#skF_10') != '#skF_10'
      | ~ r2_hidden(B_517,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_2597,c_2648])).

tff(c_2992,plain,(
    ! [B_375] :
      ( k3_xboole_0('#skF_10','#skF_10') != '#skF_10'
      | ~ r2_hidden(B_375,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_2597,c_2976])).

tff(c_3063,plain,(
    ! [B_519] : ~ r2_hidden(B_519,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2992])).

tff(c_3083,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2411,c_3063])).

tff(c_3106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2410,c_3083])).

tff(c_3107,plain,(
    r2_hidden('#skF_2'('#skF_10'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_2392])).

tff(c_3574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3566,c_3107])).

tff(c_3575,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3585,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_3575])).

tff(c_3576,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3596,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3585,c_3576])).

tff(c_1422,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3587,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3585,c_1422])).

tff(c_3597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3596,c_3587])).

tff(c_3598,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3575])).

tff(c_3611,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3598,c_3576])).

tff(c_3601,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3598,c_1422])).

tff(c_3612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3611,c_3601])).

tff(c_3614,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3615,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_14])).

tff(c_4200,plain,(
    ! [A_704,B_705,D_706] :
      ( r2_hidden('#skF_7'(A_704,B_705,k2_zfmisc_1(A_704,B_705),D_706),A_704)
      | ~ r2_hidden(D_706,k2_zfmisc_1(A_704,B_705)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4031,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_4])).

tff(c_4044,plain,(
    ! [A_660,B_661,C_662] :
      ( ~ r1_xboole_0(A_660,B_661)
      | ~ r2_hidden(C_662,B_661)
      | ~ r2_hidden(C_662,A_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4050,plain,(
    ! [C_671,B_672,A_673] :
      ( ~ r2_hidden(C_671,B_672)
      | ~ r2_hidden(C_671,A_673)
      | k3_xboole_0(A_673,B_672) != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_4031,c_4044])).

tff(c_4066,plain,(
    ! [A_676,B_677,A_678] :
      ( ~ r2_hidden('#skF_1'(A_676,B_677),A_678)
      | k3_xboole_0(A_678,A_676) != '#skF_12'
      | r1_xboole_0(A_676,B_677) ) ),
    inference(resolution,[status(thm)],[c_12,c_4050])).

tff(c_4069,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,A_5) != '#skF_12'
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_4066])).

tff(c_4089,plain,(
    ! [A_683,B_684] :
      ( A_683 != '#skF_12'
      | r1_xboole_0(A_683,B_684) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4069])).

tff(c_4095,plain,(
    ! [C_9,B_684,A_683] :
      ( ~ r2_hidden(C_9,B_684)
      | ~ r2_hidden(C_9,A_683)
      | A_683 != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_4089,c_8])).

tff(c_4358,plain,(
    ! [A_745,B_746,D_747,A_748] :
      ( ~ r2_hidden('#skF_7'(A_745,B_746,k2_zfmisc_1(A_745,B_746),D_747),A_748)
      | A_748 != '#skF_12'
      | ~ r2_hidden(D_747,k2_zfmisc_1(A_745,B_746)) ) ),
    inference(resolution,[status(thm)],[c_4200,c_4095])).

tff(c_4364,plain,(
    ! [A_749,D_750,B_751] :
      ( A_749 != '#skF_12'
      | ~ r2_hidden(D_750,k2_zfmisc_1(A_749,B_751)) ) ),
    inference(resolution,[status(thm)],[c_22,c_4358])).

tff(c_4441,plain,(
    ! [B_751] : k2_zfmisc_1('#skF_12',B_751) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3615,c_4364])).

tff(c_3633,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_4])).

tff(c_3643,plain,(
    ! [A_559,B_560,C_561] :
      ( ~ r1_xboole_0(A_559,B_560)
      | ~ r2_hidden(C_561,B_560)
      | ~ r2_hidden(C_561,A_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3649,plain,(
    ! [C_570,B_571,A_572] :
      ( ~ r2_hidden(C_570,B_571)
      | ~ r2_hidden(C_570,A_572)
      | k3_xboole_0(A_572,B_571) != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_3633,c_3643])).

tff(c_3677,plain,(
    ! [A_579,B_580,A_581] :
      ( ~ r2_hidden('#skF_1'(A_579,B_580),A_581)
      | k3_xboole_0(A_581,A_579) != '#skF_12'
      | r1_xboole_0(A_579,B_580) ) ),
    inference(resolution,[status(thm)],[c_12,c_3649])).

tff(c_3680,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,A_5) != '#skF_12'
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_3677])).

tff(c_3688,plain,(
    ! [A_582,B_583] :
      ( A_582 != '#skF_12'
      | r1_xboole_0(A_582,B_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3680])).

tff(c_3726,plain,(
    ! [C_591,B_592,A_593] :
      ( ~ r2_hidden(C_591,B_592)
      | ~ r2_hidden(C_591,A_593)
      | A_593 != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_3688,c_8])).

tff(c_3957,plain,(
    ! [A_644,B_645,D_646,A_647] :
      ( ~ r2_hidden('#skF_8'(A_644,B_645,k2_zfmisc_1(A_644,B_645),D_646),A_647)
      | A_647 != '#skF_12'
      | ~ r2_hidden(D_646,k2_zfmisc_1(A_644,B_645)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3726])).

tff(c_3963,plain,(
    ! [B_648,D_649,A_650] :
      ( B_648 != '#skF_12'
      | ~ r2_hidden(D_649,k2_zfmisc_1(A_650,B_648)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3957])).

tff(c_4018,plain,(
    ! [A_650] : k2_zfmisc_1(A_650,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3615,c_3963])).

tff(c_3613,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3622,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_3614,c_3613])).

tff(c_3623,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_3622])).

tff(c_46,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3629,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_3623,c_3614,c_46])).

tff(c_4021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_3629])).

tff(c_4022,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_3622])).

tff(c_4029,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3614,c_4022,c_3614,c_46])).

tff(c_4444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4441,c_4029])).

tff(c_4446,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4454,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4446,c_4446,c_4446,c_52])).

tff(c_4455,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4454])).

tff(c_4457,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_4446])).

tff(c_4467,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4457,c_14])).

tff(c_4587,plain,(
    ! [A_801,B_802,D_803] :
      ( r2_hidden('#skF_7'(A_801,B_802,k2_zfmisc_1(A_801,B_802),D_803),A_801)
      | ~ r2_hidden(D_803,k2_zfmisc_1(A_801,B_802)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4469,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4457,c_4])).

tff(c_4481,plain,(
    ! [A_764,B_765,C_766] :
      ( ~ r1_xboole_0(A_764,B_765)
      | ~ r2_hidden(C_766,B_765)
      | ~ r2_hidden(C_766,A_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4496,plain,(
    ! [C_779,B_780,A_781] :
      ( ~ r2_hidden(C_779,B_780)
      | ~ r2_hidden(C_779,A_781)
      | k3_xboole_0(A_781,B_780) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_4469,c_4481])).

tff(c_4515,plain,(
    ! [A_784,B_785,A_786] :
      ( ~ r2_hidden('#skF_1'(A_784,B_785),A_786)
      | k3_xboole_0(A_786,A_784) != '#skF_9'
      | r1_xboole_0(A_784,B_785) ) ),
    inference(resolution,[status(thm)],[c_12,c_4496])).

tff(c_4518,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,A_5) != '#skF_9'
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_4515])).

tff(c_4530,plain,(
    ! [A_790,B_791] :
      ( A_790 != '#skF_9'
      | r1_xboole_0(A_790,B_791) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4518])).

tff(c_4536,plain,(
    ! [C_9,B_791,A_790] :
      ( ~ r2_hidden(C_9,B_791)
      | ~ r2_hidden(C_9,A_790)
      | A_790 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_4530,c_8])).

tff(c_4795,plain,(
    ! [A_849,B_850,D_851,A_852] :
      ( ~ r2_hidden('#skF_7'(A_849,B_850,k2_zfmisc_1(A_849,B_850),D_851),A_852)
      | A_852 != '#skF_9'
      | ~ r2_hidden(D_851,k2_zfmisc_1(A_849,B_850)) ) ),
    inference(resolution,[status(thm)],[c_4587,c_4536])).

tff(c_4801,plain,(
    ! [A_853,D_854,B_855] :
      ( A_853 != '#skF_9'
      | ~ r2_hidden(D_854,k2_zfmisc_1(A_853,B_855)) ) ),
    inference(resolution,[status(thm)],[c_22,c_4795])).

tff(c_4856,plain,(
    ! [B_855] : k2_zfmisc_1('#skF_9',B_855) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4467,c_4801])).

tff(c_4445,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4451,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4446,c_4445])).

tff(c_4456,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_4451])).

tff(c_4859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4856,c_4456])).

tff(c_4860,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_4454])).

tff(c_4863,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4860,c_4446])).

tff(c_4875,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4863,c_14])).

tff(c_4993,plain,(
    ! [A_900,B_901,D_902] :
      ( r2_hidden('#skF_8'(A_900,B_901,k2_zfmisc_1(A_900,B_901),D_902),B_901)
      | ~ r2_hidden(D_902,k2_zfmisc_1(A_900,B_901)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4879,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4863,c_4])).

tff(c_4890,plain,(
    ! [A_865,B_866,C_867] :
      ( ~ r1_xboole_0(A_865,B_866)
      | ~ r2_hidden(C_867,B_866)
      | ~ r2_hidden(C_867,A_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4896,plain,(
    ! [C_876,B_877,A_878] :
      ( ~ r2_hidden(C_876,B_877)
      | ~ r2_hidden(C_876,A_878)
      | k3_xboole_0(A_878,B_877) != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_4879,c_4890])).

tff(c_4912,plain,(
    ! [A_881,B_882,A_883] :
      ( ~ r2_hidden('#skF_1'(A_881,B_882),A_883)
      | k3_xboole_0(A_883,B_882) != '#skF_10'
      | r1_xboole_0(A_881,B_882) ) ),
    inference(resolution,[status(thm)],[c_10,c_4896])).

tff(c_4915,plain,(
    ! [B_6,A_5] :
      ( k3_xboole_0(B_6,B_6) != '#skF_10'
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_4912])).

tff(c_4923,plain,(
    ! [B_884,A_885] :
      ( B_884 != '#skF_10'
      | r1_xboole_0(A_885,B_884) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4915])).

tff(c_4929,plain,(
    ! [C_9,B_884,A_885] :
      ( ~ r2_hidden(C_9,B_884)
      | ~ r2_hidden(C_9,A_885)
      | B_884 != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_4923,c_8])).

tff(c_5236,plain,(
    ! [A_956,B_957,D_958,A_959] :
      ( ~ r2_hidden('#skF_8'(A_956,B_957,k2_zfmisc_1(A_956,B_957),D_958),A_959)
      | B_957 != '#skF_10'
      | ~ r2_hidden(D_958,k2_zfmisc_1(A_956,B_957)) ) ),
    inference(resolution,[status(thm)],[c_4993,c_4929])).

tff(c_5242,plain,(
    ! [B_960,D_961,A_962] :
      ( B_960 != '#skF_10'
      | ~ r2_hidden(D_961,k2_zfmisc_1(A_962,B_960)) ) ),
    inference(resolution,[status(thm)],[c_20,c_5236])).

tff(c_5297,plain,(
    ! [A_962] : k2_zfmisc_1(A_962,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_4875,c_5242])).

tff(c_4862,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4860,c_4451])).

tff(c_5300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5297,c_4862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.55/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.14  
% 5.55/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.14  %$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 5.55/2.14  
% 5.55/2.14  %Foreground sorts:
% 5.55/2.14  
% 5.55/2.14  
% 5.55/2.14  %Background operators:
% 5.55/2.14  
% 5.55/2.14  
% 5.55/2.14  %Foreground operators:
% 5.55/2.14  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.55/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.55/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.55/2.14  tff('#skF_11', type, '#skF_11': $i).
% 5.55/2.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.55/2.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.55/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.55/2.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.55/2.14  tff('#skF_10', type, '#skF_10': $i).
% 5.55/2.14  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.55/2.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.55/2.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.55/2.14  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 5.55/2.14  tff('#skF_9', type, '#skF_9': $i).
% 5.55/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.55/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.55/2.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.55/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.55/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.55/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.55/2.14  tff('#skF_12', type, '#skF_12': $i).
% 5.55/2.14  
% 5.71/2.17  tff(f_82, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.71/2.17  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.71/2.17  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.71/2.17  tff(f_75, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.71/2.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.71/2.17  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.71/2.17  tff(f_69, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.71/2.17  tff(c_50, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.17  tff(c_66, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_50])).
% 5.71/2.17  tff(c_14, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.71/2.17  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.71/2.17  tff(c_56, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.17  tff(c_1424, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 5.71/2.17  tff(c_1479, plain, (![A_370, B_371, C_372, D_373]: (r2_hidden(k4_tarski(A_370, B_371), k2_zfmisc_1(C_372, D_373)) | ~r2_hidden(B_371, D_373) | ~r2_hidden(A_370, C_372))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.71/2.17  tff(c_1493, plain, (![A_370, B_371]: (r2_hidden(k4_tarski(A_370, B_371), k1_xboole_0) | ~r2_hidden(B_371, '#skF_12') | ~r2_hidden(A_370, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1424, c_1479])).
% 5.71/2.17  tff(c_1497, plain, (![A_374, B_375]: (r2_hidden(k4_tarski(A_374, B_375), k1_xboole_0) | ~r2_hidden(B_375, '#skF_12') | ~r2_hidden(A_374, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1424, c_1479])).
% 5.71/2.17  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.71/2.17  tff(c_1441, plain, (![A_346, B_347, C_348]: (~r1_xboole_0(A_346, B_347) | ~r2_hidden(C_348, B_347) | ~r2_hidden(C_348, A_346))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_1444, plain, (![C_348, B_2, A_1]: (~r2_hidden(C_348, B_2) | ~r2_hidden(C_348, A_1) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1441])).
% 5.71/2.17  tff(c_3492, plain, (![A_546, B_547, A_548]: (~r2_hidden(k4_tarski(A_546, B_547), A_548) | k3_xboole_0(A_548, k1_xboole_0)!=k1_xboole_0 | ~r2_hidden(B_547, '#skF_12') | ~r2_hidden(A_546, '#skF_11'))), inference(resolution, [status(thm)], [c_1497, c_1444])).
% 5.71/2.17  tff(c_3506, plain, (![B_371, A_370]: (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0 | ~r2_hidden(B_371, '#skF_12') | ~r2_hidden(A_370, '#skF_11'))), inference(resolution, [status(thm)], [c_1493, c_3492])).
% 5.71/2.17  tff(c_3517, plain, (![B_371, A_370]: (~r2_hidden(B_371, '#skF_12') | ~r2_hidden(A_370, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3506])).
% 5.71/2.17  tff(c_3523, plain, (![A_549]: (~r2_hidden(A_549, '#skF_11'))), inference(splitLeft, [status(thm)], [c_3517])).
% 5.71/2.17  tff(c_3555, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_14, c_3523])).
% 5.71/2.17  tff(c_3565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_3555])).
% 5.71/2.17  tff(c_3566, plain, (![B_371]: (~r2_hidden(B_371, '#skF_12'))), inference(splitRight, [status(thm)], [c_3517])).
% 5.71/2.17  tff(c_48, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.17  tff(c_68, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_48])).
% 5.71/2.17  tff(c_78, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 5.71/2.17  tff(c_132, plain, (![A_85, B_86, C_87, D_88]: (r2_hidden(k4_tarski(A_85, B_86), k2_zfmisc_1(C_87, D_88)) | ~r2_hidden(B_86, D_88) | ~r2_hidden(A_85, C_87))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.71/2.17  tff(c_143, plain, (![A_85, B_86]: (r2_hidden(k4_tarski(A_85, B_86), k1_xboole_0) | ~r2_hidden(B_86, '#skF_12') | ~r2_hidden(A_85, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_132])).
% 5.71/2.17  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_83, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, B_61) | ~r2_hidden(C_62, A_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_97, plain, (![C_75, B_76, A_77]: (~r2_hidden(C_75, B_76) | ~r2_hidden(C_75, A_77) | k3_xboole_0(A_77, B_76)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_83])).
% 5.71/2.17  tff(c_113, plain, (![A_80, B_81, A_82]: (~r2_hidden('#skF_1'(A_80, B_81), A_82) | k3_xboole_0(A_82, A_80)!=k1_xboole_0 | r1_xboole_0(A_80, B_81))), inference(resolution, [status(thm)], [c_12, c_97])).
% 5.71/2.17  tff(c_116, plain, (![A_5, B_6]: (k3_xboole_0(A_5, A_5)!=k1_xboole_0 | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_113])).
% 5.71/2.17  tff(c_124, plain, (![A_83, B_84]: (k1_xboole_0!=A_83 | r1_xboole_0(A_83, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_116])).
% 5.71/2.17  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_173, plain, (![C_93, B_94, A_95]: (~r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | k1_xboole_0!=A_95)), inference(resolution, [status(thm)], [c_124, c_8])).
% 5.71/2.17  tff(c_261, plain, (![A_107, B_108, A_109]: (~r2_hidden('#skF_1'(A_107, B_108), A_109) | k1_xboole_0!=A_109 | r1_xboole_0(A_107, B_108))), inference(resolution, [status(thm)], [c_10, c_173])).
% 5.71/2.17  tff(c_285, plain, (![B_113, A_114]: (k1_xboole_0!=B_113 | r1_xboole_0(A_114, B_113))), inference(resolution, [status(thm)], [c_10, c_261])).
% 5.71/2.17  tff(c_294, plain, (![C_115, B_116, A_117]: (~r2_hidden(C_115, B_116) | ~r2_hidden(C_115, A_117) | k1_xboole_0!=B_116)), inference(resolution, [status(thm)], [c_285, c_8])).
% 5.71/2.17  tff(c_326, plain, (![A_119, B_120, A_121]: (~r2_hidden(k4_tarski(A_119, B_120), A_121) | ~r2_hidden(B_120, '#skF_12') | ~r2_hidden(A_119, '#skF_11'))), inference(resolution, [status(thm)], [c_143, c_294])).
% 5.71/2.17  tff(c_333, plain, (![B_86, A_85]: (~r2_hidden(B_86, '#skF_12') | ~r2_hidden(A_85, '#skF_11'))), inference(resolution, [status(thm)], [c_143, c_326])).
% 5.71/2.17  tff(c_337, plain, (![A_122]: (~r2_hidden(A_122, '#skF_11'))), inference(splitLeft, [status(thm)], [c_333])).
% 5.71/2.17  tff(c_353, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_14, c_337])).
% 5.71/2.17  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_353])).
% 5.71/2.17  tff(c_364, plain, (![B_123]: (~r2_hidden(B_123, '#skF_12'))), inference(splitRight, [status(thm)], [c_333])).
% 5.71/2.17  tff(c_380, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_14, c_364])).
% 5.71/2.17  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_380])).
% 5.71/2.17  tff(c_388, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_56])).
% 5.71/2.17  tff(c_390, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_388])).
% 5.71/2.17  tff(c_395, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_14])).
% 5.71/2.17  tff(c_20, plain, (![A_12, B_13, D_39]: (r2_hidden('#skF_8'(A_12, B_13, k2_zfmisc_1(A_12, B_13), D_39), B_13) | ~r2_hidden(D_39, k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.17  tff(c_22, plain, (![A_12, B_13, D_39]: (r2_hidden('#skF_7'(A_12, B_13, k2_zfmisc_1(A_12, B_13), D_39), A_12) | ~r2_hidden(D_39, k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.17  tff(c_515, plain, (![A_166, B_167, D_168]: (r2_hidden('#skF_7'(A_166, B_167, k2_zfmisc_1(A_166, B_167), D_168), A_166) | ~r2_hidden(D_168, k2_zfmisc_1(A_166, B_167)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.17  tff(c_404, plain, (![A_128, B_129]: (r1_xboole_0(A_128, B_129) | k3_xboole_0(A_128, B_129)!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_4])).
% 5.71/2.17  tff(c_424, plain, (![C_144, B_145, A_146]: (~r2_hidden(C_144, B_145) | ~r2_hidden(C_144, A_146) | k3_xboole_0(A_146, B_145)!='#skF_10')), inference(resolution, [status(thm)], [c_404, c_8])).
% 5.71/2.17  tff(c_443, plain, (![A_149, B_150, A_151]: (~r2_hidden('#skF_1'(A_149, B_150), A_151) | k3_xboole_0(A_151, A_149)!='#skF_10' | r1_xboole_0(A_149, B_150))), inference(resolution, [status(thm)], [c_12, c_424])).
% 5.71/2.17  tff(c_446, plain, (![A_5, B_6]: (k3_xboole_0(A_5, A_5)!='#skF_10' | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_443])).
% 5.71/2.17  tff(c_458, plain, (![A_155, B_156]: (A_155!='#skF_10' | r1_xboole_0(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_446])).
% 5.71/2.17  tff(c_465, plain, (![C_9, B_156, A_155]: (~r2_hidden(C_9, B_156) | ~r2_hidden(C_9, A_155) | A_155!='#skF_10')), inference(resolution, [status(thm)], [c_458, c_8])).
% 5.71/2.17  tff(c_723, plain, (![A_214, B_215, D_216, A_217]: (~r2_hidden('#skF_7'(A_214, B_215, k2_zfmisc_1(A_214, B_215), D_216), A_217) | A_217!='#skF_10' | ~r2_hidden(D_216, k2_zfmisc_1(A_214, B_215)))), inference(resolution, [status(thm)], [c_515, c_465])).
% 5.71/2.17  tff(c_729, plain, (![A_218, D_219, B_220]: (A_218!='#skF_10' | ~r2_hidden(D_219, k2_zfmisc_1(A_218, B_220)))), inference(resolution, [status(thm)], [c_22, c_723])).
% 5.71/2.17  tff(c_785, plain, (![A_221, B_222]: (A_221!='#skF_10' | k2_zfmisc_1(A_221, B_222)='#skF_10')), inference(resolution, [status(thm)], [c_395, c_729])).
% 5.71/2.17  tff(c_727, plain, (![A_12, D_39, B_13]: (A_12!='#skF_10' | ~r2_hidden(D_39, k2_zfmisc_1(A_12, B_13)))), inference(resolution, [status(thm)], [c_22, c_723])).
% 5.71/2.17  tff(c_791, plain, (![A_221, D_39]: (A_221!='#skF_10' | ~r2_hidden(D_39, '#skF_10') | A_221!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_785, c_727])).
% 5.71/2.17  tff(c_880, plain, (![A_221]: (A_221!='#skF_10' | A_221!='#skF_10')), inference(splitLeft, [status(thm)], [c_791])).
% 5.71/2.17  tff(c_886, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_880])).
% 5.71/2.17  tff(c_888, plain, (![D_237]: (~r2_hidden(D_237, '#skF_10'))), inference(splitRight, [status(thm)], [c_791])).
% 5.71/2.17  tff(c_937, plain, (![D_238, A_239]: (~r2_hidden(D_238, k2_zfmisc_1(A_239, '#skF_10')))), inference(resolution, [status(thm)], [c_20, c_888])).
% 5.71/2.17  tff(c_993, plain, (![A_239]: (k2_zfmisc_1(A_239, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_395, c_937])).
% 5.71/2.17  tff(c_54, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.17  tff(c_70, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 5.71/2.17  tff(c_392, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_390, c_70])).
% 5.71/2.17  tff(c_999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_993, c_392])).
% 5.71/2.17  tff(c_1000, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_388])).
% 5.71/2.17  tff(c_1007, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_14])).
% 5.71/2.17  tff(c_1155, plain, (![A_284, B_285, D_286]: (r2_hidden('#skF_7'(A_284, B_285, k2_zfmisc_1(A_284, B_285), D_286), A_284) | ~r2_hidden(D_286, k2_zfmisc_1(A_284, B_285)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.17  tff(c_1003, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_4])).
% 5.71/2.17  tff(c_1021, plain, (![A_245, B_246, C_247]: (~r1_xboole_0(A_245, B_246) | ~r2_hidden(C_247, B_246) | ~r2_hidden(C_247, A_245))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_1027, plain, (![C_256, B_257, A_258]: (~r2_hidden(C_256, B_257) | ~r2_hidden(C_256, A_258) | k3_xboole_0(A_258, B_257)!='#skF_9')), inference(resolution, [status(thm)], [c_1003, c_1021])).
% 5.71/2.17  tff(c_1055, plain, (![A_265, B_266, A_267]: (~r2_hidden('#skF_1'(A_265, B_266), A_267) | k3_xboole_0(A_267, A_265)!='#skF_9' | r1_xboole_0(A_265, B_266))), inference(resolution, [status(thm)], [c_12, c_1027])).
% 5.71/2.17  tff(c_1058, plain, (![A_5, B_6]: (k3_xboole_0(A_5, A_5)!='#skF_9' | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_1055])).
% 5.71/2.17  tff(c_1066, plain, (![A_268, B_269]: (A_268!='#skF_9' | r1_xboole_0(A_268, B_269))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1058])).
% 5.71/2.17  tff(c_1072, plain, (![C_9, B_269, A_268]: (~r2_hidden(C_9, B_269) | ~r2_hidden(C_9, A_268) | A_268!='#skF_9')), inference(resolution, [status(thm)], [c_1066, c_8])).
% 5.71/2.17  tff(c_1357, plain, (![A_333, B_334, D_335, A_336]: (~r2_hidden('#skF_7'(A_333, B_334, k2_zfmisc_1(A_333, B_334), D_335), A_336) | A_336!='#skF_9' | ~r2_hidden(D_335, k2_zfmisc_1(A_333, B_334)))), inference(resolution, [status(thm)], [c_1155, c_1072])).
% 5.71/2.17  tff(c_1363, plain, (![A_337, D_338, B_339]: (A_337!='#skF_9' | ~r2_hidden(D_338, k2_zfmisc_1(A_337, B_339)))), inference(resolution, [status(thm)], [c_22, c_1357])).
% 5.71/2.17  tff(c_1418, plain, (![B_339]: (k2_zfmisc_1('#skF_9', B_339)='#skF_9')), inference(resolution, [status(thm)], [c_1007, c_1363])).
% 5.71/2.17  tff(c_1004, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_70])).
% 5.71/2.17  tff(c_1421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1418, c_1004])).
% 5.71/2.17  tff(c_1423, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 5.71/2.17  tff(c_1539, plain, (![A_377, B_378]: (r2_hidden(k4_tarski(A_377, B_378), k1_xboole_0) | ~r2_hidden(B_378, '#skF_10') | ~r2_hidden(A_377, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1423, c_1479])).
% 5.71/2.17  tff(c_1445, plain, (![B_349, D_350, A_351, C_352]: (r2_hidden(B_349, D_350) | ~r2_hidden(k4_tarski(A_351, B_349), k2_zfmisc_1(C_352, D_350)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.71/2.17  tff(c_1451, plain, (![B_349, A_351]: (r2_hidden(B_349, '#skF_12') | ~r2_hidden(k4_tarski(A_351, B_349), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1424, c_1445])).
% 5.71/2.17  tff(c_1558, plain, (![B_378, A_377]: (r2_hidden(B_378, '#skF_12') | ~r2_hidden(B_378, '#skF_10') | ~r2_hidden(A_377, '#skF_9'))), inference(resolution, [status(thm)], [c_1539, c_1451])).
% 5.71/2.17  tff(c_2363, plain, (![A_377]: (~r2_hidden(A_377, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1558])).
% 5.71/2.17  tff(c_1454, plain, (![A_357, C_358, B_359, D_360]: (r2_hidden(A_357, C_358) | ~r2_hidden(k4_tarski(A_357, B_359), k2_zfmisc_1(C_358, D_360)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.71/2.17  tff(c_1457, plain, (![A_357, B_359]: (r2_hidden(A_357, '#skF_9') | ~r2_hidden(k4_tarski(A_357, B_359), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1423, c_1454])).
% 5.71/2.17  tff(c_1513, plain, (![A_374, B_375]: (r2_hidden(A_374, '#skF_9') | ~r2_hidden(B_375, '#skF_12') | ~r2_hidden(A_374, '#skF_11'))), inference(resolution, [status(thm)], [c_1497, c_1457])).
% 5.71/2.17  tff(c_1519, plain, (![B_376]: (~r2_hidden(B_376, '#skF_12'))), inference(splitLeft, [status(thm)], [c_1513])).
% 5.71/2.17  tff(c_1531, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_14, c_1519])).
% 5.71/2.17  tff(c_1537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1531])).
% 5.71/2.17  tff(c_1559, plain, (![A_379]: (r2_hidden(A_379, '#skF_9') | ~r2_hidden(A_379, '#skF_11'))), inference(splitRight, [status(thm)], [c_1513])).
% 5.71/2.17  tff(c_1571, plain, (r2_hidden('#skF_2'('#skF_11'), '#skF_9') | k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_14, c_1559])).
% 5.71/2.17  tff(c_1576, plain, (r2_hidden('#skF_2'('#skF_11'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_66, c_1571])).
% 5.71/2.17  tff(c_2370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2363, c_1576])).
% 5.71/2.17  tff(c_2372, plain, (![B_451]: (r2_hidden(B_451, '#skF_12') | ~r2_hidden(B_451, '#skF_10'))), inference(splitRight, [status(thm)], [c_1558])).
% 5.71/2.17  tff(c_2392, plain, (r2_hidden('#skF_2'('#skF_10'), '#skF_12') | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_14, c_2372])).
% 5.71/2.17  tff(c_2393, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_2392])).
% 5.71/2.17  tff(c_2410, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2393, c_68])).
% 5.71/2.17  tff(c_2411, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2393, c_14])).
% 5.71/2.17  tff(c_2412, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2393, c_66])).
% 5.71/2.17  tff(c_1448, plain, (![B_349, A_351]: (r2_hidden(B_349, '#skF_10') | ~r2_hidden(k4_tarski(A_351, B_349), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1423, c_1445])).
% 5.71/2.17  tff(c_1515, plain, (![B_375, A_374]: (r2_hidden(B_375, '#skF_10') | ~r2_hidden(B_375, '#skF_12') | ~r2_hidden(A_374, '#skF_11'))), inference(resolution, [status(thm)], [c_1497, c_1448])).
% 5.71/2.17  tff(c_2558, plain, (![A_478]: (~r2_hidden(A_478, '#skF_11'))), inference(splitLeft, [status(thm)], [c_1515])).
% 5.71/2.17  tff(c_2574, plain, ('#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_2411, c_2558])).
% 5.71/2.17  tff(c_2596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2412, c_2574])).
% 5.71/2.17  tff(c_2597, plain, (![B_375]: (r2_hidden(B_375, '#skF_10') | ~r2_hidden(B_375, '#skF_12'))), inference(splitRight, [status(thm)], [c_1515])).
% 5.71/2.17  tff(c_2648, plain, (![C_493, B_494, A_495]: (~r2_hidden(C_493, B_494) | ~r2_hidden(C_493, A_495) | k3_xboole_0(A_495, B_494)!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2393, c_1444])).
% 5.71/2.17  tff(c_2976, plain, (![B_517, A_518]: (~r2_hidden(B_517, A_518) | k3_xboole_0(A_518, '#skF_10')!='#skF_10' | ~r2_hidden(B_517, '#skF_12'))), inference(resolution, [status(thm)], [c_2597, c_2648])).
% 5.71/2.17  tff(c_2992, plain, (![B_375]: (k3_xboole_0('#skF_10', '#skF_10')!='#skF_10' | ~r2_hidden(B_375, '#skF_12'))), inference(resolution, [status(thm)], [c_2597, c_2976])).
% 5.71/2.17  tff(c_3063, plain, (![B_519]: (~r2_hidden(B_519, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2992])).
% 5.71/2.17  tff(c_3083, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_2411, c_3063])).
% 5.71/2.17  tff(c_3106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2410, c_3083])).
% 5.71/2.17  tff(c_3107, plain, (r2_hidden('#skF_2'('#skF_10'), '#skF_12')), inference(splitRight, [status(thm)], [c_2392])).
% 5.71/2.17  tff(c_3574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3566, c_3107])).
% 5.71/2.17  tff(c_3575, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_56])).
% 5.71/2.17  tff(c_3585, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_3575])).
% 5.71/2.17  tff(c_3576, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 5.71/2.17  tff(c_3596, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_3585, c_3576])).
% 5.71/2.17  tff(c_1422, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 5.71/2.17  tff(c_3587, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_3585, c_1422])).
% 5.71/2.17  tff(c_3597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3596, c_3587])).
% 5.71/2.17  tff(c_3598, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_3575])).
% 5.71/2.17  tff(c_3611, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3598, c_3576])).
% 5.71/2.17  tff(c_3601, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3598, c_1422])).
% 5.71/2.17  tff(c_3612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3611, c_3601])).
% 5.71/2.17  tff(c_3614, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_48])).
% 5.71/2.17  tff(c_3615, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_14])).
% 5.71/2.17  tff(c_4200, plain, (![A_704, B_705, D_706]: (r2_hidden('#skF_7'(A_704, B_705, k2_zfmisc_1(A_704, B_705), D_706), A_704) | ~r2_hidden(D_706, k2_zfmisc_1(A_704, B_705)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.17  tff(c_4031, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_4])).
% 5.71/2.17  tff(c_4044, plain, (![A_660, B_661, C_662]: (~r1_xboole_0(A_660, B_661) | ~r2_hidden(C_662, B_661) | ~r2_hidden(C_662, A_660))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_4050, plain, (![C_671, B_672, A_673]: (~r2_hidden(C_671, B_672) | ~r2_hidden(C_671, A_673) | k3_xboole_0(A_673, B_672)!='#skF_12')), inference(resolution, [status(thm)], [c_4031, c_4044])).
% 5.71/2.17  tff(c_4066, plain, (![A_676, B_677, A_678]: (~r2_hidden('#skF_1'(A_676, B_677), A_678) | k3_xboole_0(A_678, A_676)!='#skF_12' | r1_xboole_0(A_676, B_677))), inference(resolution, [status(thm)], [c_12, c_4050])).
% 5.71/2.17  tff(c_4069, plain, (![A_5, B_6]: (k3_xboole_0(A_5, A_5)!='#skF_12' | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_4066])).
% 5.71/2.17  tff(c_4089, plain, (![A_683, B_684]: (A_683!='#skF_12' | r1_xboole_0(A_683, B_684))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4069])).
% 5.71/2.17  tff(c_4095, plain, (![C_9, B_684, A_683]: (~r2_hidden(C_9, B_684) | ~r2_hidden(C_9, A_683) | A_683!='#skF_12')), inference(resolution, [status(thm)], [c_4089, c_8])).
% 5.71/2.17  tff(c_4358, plain, (![A_745, B_746, D_747, A_748]: (~r2_hidden('#skF_7'(A_745, B_746, k2_zfmisc_1(A_745, B_746), D_747), A_748) | A_748!='#skF_12' | ~r2_hidden(D_747, k2_zfmisc_1(A_745, B_746)))), inference(resolution, [status(thm)], [c_4200, c_4095])).
% 5.71/2.17  tff(c_4364, plain, (![A_749, D_750, B_751]: (A_749!='#skF_12' | ~r2_hidden(D_750, k2_zfmisc_1(A_749, B_751)))), inference(resolution, [status(thm)], [c_22, c_4358])).
% 5.71/2.17  tff(c_4441, plain, (![B_751]: (k2_zfmisc_1('#skF_12', B_751)='#skF_12')), inference(resolution, [status(thm)], [c_3615, c_4364])).
% 5.71/2.17  tff(c_3633, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_4])).
% 5.71/2.17  tff(c_3643, plain, (![A_559, B_560, C_561]: (~r1_xboole_0(A_559, B_560) | ~r2_hidden(C_561, B_560) | ~r2_hidden(C_561, A_559))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_3649, plain, (![C_570, B_571, A_572]: (~r2_hidden(C_570, B_571) | ~r2_hidden(C_570, A_572) | k3_xboole_0(A_572, B_571)!='#skF_12')), inference(resolution, [status(thm)], [c_3633, c_3643])).
% 5.71/2.17  tff(c_3677, plain, (![A_579, B_580, A_581]: (~r2_hidden('#skF_1'(A_579, B_580), A_581) | k3_xboole_0(A_581, A_579)!='#skF_12' | r1_xboole_0(A_579, B_580))), inference(resolution, [status(thm)], [c_12, c_3649])).
% 5.71/2.17  tff(c_3680, plain, (![A_5, B_6]: (k3_xboole_0(A_5, A_5)!='#skF_12' | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_3677])).
% 5.71/2.17  tff(c_3688, plain, (![A_582, B_583]: (A_582!='#skF_12' | r1_xboole_0(A_582, B_583))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3680])).
% 5.71/2.17  tff(c_3726, plain, (![C_591, B_592, A_593]: (~r2_hidden(C_591, B_592) | ~r2_hidden(C_591, A_593) | A_593!='#skF_12')), inference(resolution, [status(thm)], [c_3688, c_8])).
% 5.71/2.17  tff(c_3957, plain, (![A_644, B_645, D_646, A_647]: (~r2_hidden('#skF_8'(A_644, B_645, k2_zfmisc_1(A_644, B_645), D_646), A_647) | A_647!='#skF_12' | ~r2_hidden(D_646, k2_zfmisc_1(A_644, B_645)))), inference(resolution, [status(thm)], [c_20, c_3726])).
% 5.71/2.17  tff(c_3963, plain, (![B_648, D_649, A_650]: (B_648!='#skF_12' | ~r2_hidden(D_649, k2_zfmisc_1(A_650, B_648)))), inference(resolution, [status(thm)], [c_20, c_3957])).
% 5.71/2.17  tff(c_4018, plain, (![A_650]: (k2_zfmisc_1(A_650, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_3615, c_3963])).
% 5.71/2.17  tff(c_3613, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_48])).
% 5.71/2.17  tff(c_3622, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_3614, c_3613])).
% 5.71/2.17  tff(c_3623, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_3622])).
% 5.71/2.17  tff(c_46, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.17  tff(c_3629, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_3623, c_3614, c_46])).
% 5.71/2.17  tff(c_4021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4018, c_3629])).
% 5.71/2.17  tff(c_4022, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_3622])).
% 5.71/2.17  tff(c_4029, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3614, c_4022, c_3614, c_46])).
% 5.71/2.17  tff(c_4444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4441, c_4029])).
% 5.71/2.17  tff(c_4446, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_50])).
% 5.71/2.17  tff(c_52, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.17  tff(c_4454, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4446, c_4446, c_4446, c_52])).
% 5.71/2.17  tff(c_4455, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_4454])).
% 5.71/2.17  tff(c_4457, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4455, c_4446])).
% 5.71/2.17  tff(c_4467, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4457, c_14])).
% 5.71/2.17  tff(c_4587, plain, (![A_801, B_802, D_803]: (r2_hidden('#skF_7'(A_801, B_802, k2_zfmisc_1(A_801, B_802), D_803), A_801) | ~r2_hidden(D_803, k2_zfmisc_1(A_801, B_802)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.17  tff(c_4469, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4457, c_4])).
% 5.71/2.17  tff(c_4481, plain, (![A_764, B_765, C_766]: (~r1_xboole_0(A_764, B_765) | ~r2_hidden(C_766, B_765) | ~r2_hidden(C_766, A_764))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_4496, plain, (![C_779, B_780, A_781]: (~r2_hidden(C_779, B_780) | ~r2_hidden(C_779, A_781) | k3_xboole_0(A_781, B_780)!='#skF_9')), inference(resolution, [status(thm)], [c_4469, c_4481])).
% 5.71/2.17  tff(c_4515, plain, (![A_784, B_785, A_786]: (~r2_hidden('#skF_1'(A_784, B_785), A_786) | k3_xboole_0(A_786, A_784)!='#skF_9' | r1_xboole_0(A_784, B_785))), inference(resolution, [status(thm)], [c_12, c_4496])).
% 5.71/2.17  tff(c_4518, plain, (![A_5, B_6]: (k3_xboole_0(A_5, A_5)!='#skF_9' | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_4515])).
% 5.71/2.17  tff(c_4530, plain, (![A_790, B_791]: (A_790!='#skF_9' | r1_xboole_0(A_790, B_791))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4518])).
% 5.71/2.17  tff(c_4536, plain, (![C_9, B_791, A_790]: (~r2_hidden(C_9, B_791) | ~r2_hidden(C_9, A_790) | A_790!='#skF_9')), inference(resolution, [status(thm)], [c_4530, c_8])).
% 5.71/2.17  tff(c_4795, plain, (![A_849, B_850, D_851, A_852]: (~r2_hidden('#skF_7'(A_849, B_850, k2_zfmisc_1(A_849, B_850), D_851), A_852) | A_852!='#skF_9' | ~r2_hidden(D_851, k2_zfmisc_1(A_849, B_850)))), inference(resolution, [status(thm)], [c_4587, c_4536])).
% 5.71/2.17  tff(c_4801, plain, (![A_853, D_854, B_855]: (A_853!='#skF_9' | ~r2_hidden(D_854, k2_zfmisc_1(A_853, B_855)))), inference(resolution, [status(thm)], [c_22, c_4795])).
% 5.71/2.17  tff(c_4856, plain, (![B_855]: (k2_zfmisc_1('#skF_9', B_855)='#skF_9')), inference(resolution, [status(thm)], [c_4467, c_4801])).
% 5.71/2.17  tff(c_4445, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 5.71/2.17  tff(c_4451, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_4446, c_4445])).
% 5.71/2.17  tff(c_4456, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4455, c_4451])).
% 5.71/2.17  tff(c_4859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4856, c_4456])).
% 5.71/2.17  tff(c_4860, plain, ('#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_4454])).
% 5.71/2.17  tff(c_4863, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_4860, c_4446])).
% 5.71/2.17  tff(c_4875, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4863, c_14])).
% 5.71/2.17  tff(c_4993, plain, (![A_900, B_901, D_902]: (r2_hidden('#skF_8'(A_900, B_901, k2_zfmisc_1(A_900, B_901), D_902), B_901) | ~r2_hidden(D_902, k2_zfmisc_1(A_900, B_901)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.17  tff(c_4879, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4863, c_4])).
% 5.71/2.17  tff(c_4890, plain, (![A_865, B_866, C_867]: (~r1_xboole_0(A_865, B_866) | ~r2_hidden(C_867, B_866) | ~r2_hidden(C_867, A_865))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.17  tff(c_4896, plain, (![C_876, B_877, A_878]: (~r2_hidden(C_876, B_877) | ~r2_hidden(C_876, A_878) | k3_xboole_0(A_878, B_877)!='#skF_10')), inference(resolution, [status(thm)], [c_4879, c_4890])).
% 5.71/2.17  tff(c_4912, plain, (![A_881, B_882, A_883]: (~r2_hidden('#skF_1'(A_881, B_882), A_883) | k3_xboole_0(A_883, B_882)!='#skF_10' | r1_xboole_0(A_881, B_882))), inference(resolution, [status(thm)], [c_10, c_4896])).
% 5.71/2.17  tff(c_4915, plain, (![B_6, A_5]: (k3_xboole_0(B_6, B_6)!='#skF_10' | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_10, c_4912])).
% 5.71/2.17  tff(c_4923, plain, (![B_884, A_885]: (B_884!='#skF_10' | r1_xboole_0(A_885, B_884))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4915])).
% 5.71/2.17  tff(c_4929, plain, (![C_9, B_884, A_885]: (~r2_hidden(C_9, B_884) | ~r2_hidden(C_9, A_885) | B_884!='#skF_10')), inference(resolution, [status(thm)], [c_4923, c_8])).
% 5.71/2.17  tff(c_5236, plain, (![A_956, B_957, D_958, A_959]: (~r2_hidden('#skF_8'(A_956, B_957, k2_zfmisc_1(A_956, B_957), D_958), A_959) | B_957!='#skF_10' | ~r2_hidden(D_958, k2_zfmisc_1(A_956, B_957)))), inference(resolution, [status(thm)], [c_4993, c_4929])).
% 5.71/2.17  tff(c_5242, plain, (![B_960, D_961, A_962]: (B_960!='#skF_10' | ~r2_hidden(D_961, k2_zfmisc_1(A_962, B_960)))), inference(resolution, [status(thm)], [c_20, c_5236])).
% 5.71/2.17  tff(c_5297, plain, (![A_962]: (k2_zfmisc_1(A_962, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_4875, c_5242])).
% 5.71/2.17  tff(c_4862, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_4860, c_4451])).
% 5.71/2.17  tff(c_5300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5297, c_4862])).
% 5.71/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.17  
% 5.71/2.17  Inference rules
% 5.71/2.17  ----------------------
% 5.71/2.17  #Ref     : 1
% 5.71/2.17  #Sup     : 1211
% 5.71/2.17  #Fact    : 0
% 5.71/2.17  #Define  : 0
% 5.71/2.17  #Split   : 23
% 5.71/2.17  #Chain   : 0
% 5.71/2.17  #Close   : 0
% 5.71/2.17  
% 5.71/2.17  Ordering : KBO
% 5.71/2.17  
% 5.71/2.17  Simplification rules
% 5.71/2.17  ----------------------
% 5.71/2.17  #Subsume      : 247
% 5.71/2.17  #Demod        : 263
% 5.71/2.17  #Tautology    : 227
% 5.71/2.17  #SimpNegUnit  : 69
% 5.71/2.17  #BackRed      : 104
% 5.71/2.17  
% 5.71/2.17  #Partial instantiations: 0
% 5.71/2.17  #Strategies tried      : 1
% 5.71/2.17  
% 5.71/2.17  Timing (in seconds)
% 5.71/2.17  ----------------------
% 5.71/2.17  Preprocessing        : 0.32
% 5.71/2.17  Parsing              : 0.16
% 5.71/2.17  CNF conversion       : 0.03
% 5.71/2.17  Main loop            : 0.95
% 5.71/2.17  Inferencing          : 0.37
% 5.71/2.18  Reduction            : 0.24
% 5.71/2.18  Demodulation         : 0.16
% 5.71/2.18  BG Simplification    : 0.04
% 5.71/2.18  Subsumption          : 0.21
% 5.71/2.18  Abstraction          : 0.04
% 5.71/2.18  MUC search           : 0.00
% 5.71/2.18  Cooper               : 0.00
% 5.71/2.18  Total                : 1.35
% 5.71/2.18  Index Insertion      : 0.00
% 5.71/2.18  Index Deletion       : 0.00
% 5.71/2.18  Index Matching       : 0.00
% 5.71/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
