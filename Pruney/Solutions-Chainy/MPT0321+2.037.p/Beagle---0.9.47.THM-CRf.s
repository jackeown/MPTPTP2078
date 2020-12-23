%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:18 EST 2020

% Result     : Theorem 4.99s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 333 expanded)
%              Number of leaves         :   22 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 793 expanded)
%              Number of equality atoms :   38 ( 332 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_38,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_88,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(k2_zfmisc_1(A_34,C_35),k2_zfmisc_1(B_36,C_35))
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_93,plain,(
    ! [B_36] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_36,'#skF_7'))
      | ~ r1_tarski('#skF_6',B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_88])).

tff(c_164,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_tarski(k2_zfmisc_1(A_61,B_62),k2_zfmisc_1(A_61,C_63))
      | r1_tarski(B_62,C_63)
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_168,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_93,c_164])).

tff(c_192,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_168])).

tff(c_212,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_20,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_102,plain,(
    ! [C_41,A_42,B_43] :
      ( r1_tarski(k2_zfmisc_1(C_41,A_42),k2_zfmisc_1(C_41,B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_110,plain,(
    ! [A_42] :
      ( r1_tarski(k2_zfmisc_1('#skF_6',A_42),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_42,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_102])).

tff(c_254,plain,(
    ! [B_69,A_70,C_71] :
      ( ~ r1_tarski(k2_zfmisc_1(B_69,A_70),k2_zfmisc_1(C_71,A_70))
      | r1_tarski(B_69,C_71)
      | k1_xboole_0 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_262,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_110,c_254])).

tff(c_285,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_212,c_262])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_421,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( r2_hidden(k4_tarski(A_81,B_82),k2_zfmisc_1(C_83,D_84))
      | ~ r2_hidden(B_82,D_84)
      | ~ r2_hidden(A_81,C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_98,plain,(
    ! [B_37,D_38,A_39,C_40] :
      ( r2_hidden(B_37,D_38)
      | ~ r2_hidden(k4_tarski(A_39,B_37),k2_zfmisc_1(C_40,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    ! [B_37,A_39] :
      ( r2_hidden(B_37,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_39,B_37),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_98])).

tff(c_441,plain,(
    ! [B_82,A_81] :
      ( r2_hidden(B_82,'#skF_7')
      | ~ r2_hidden(B_82,'#skF_5')
      | ~ r2_hidden(A_81,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_421,c_101])).

tff(c_447,plain,(
    ! [A_85] : ~ r2_hidden(A_85,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_469,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_447])).

tff(c_96,plain,(
    ! [A_34] :
      ( r1_tarski(k2_zfmisc_1(A_34,'#skF_7'),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_34,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_88])).

tff(c_172,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_164])).

tff(c_195,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_172])).

tff(c_213,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_213])).

tff(c_496,plain,(
    ! [B_88] :
      ( r2_hidden(B_88,'#skF_7')
      | ~ r2_hidden(B_88,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_514,plain,(
    ! [A_89] :
      ( r1_tarski(A_89,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_89,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_496,c_4])).

tff(c_522,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_514])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_285,c_522])).

tff(c_528,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_549,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_528,c_16])).

tff(c_555,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_1334,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( r2_hidden(k4_tarski(A_145,B_146),k2_zfmisc_1(C_147,D_148))
      | ~ r2_hidden(B_146,D_148)
      | ~ r2_hidden(A_145,C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1354,plain,(
    ! [B_146,A_145] :
      ( r2_hidden(B_146,'#skF_7')
      | ~ r2_hidden(B_146,'#skF_5')
      | ~ r2_hidden(A_145,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1334,c_101])).

tff(c_1360,plain,(
    ! [A_149] : ~ r2_hidden(A_149,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1354])).

tff(c_1384,plain,(
    ! [B_150] : r1_tarski('#skF_4',B_150) ),
    inference(resolution,[status(thm)],[c_6,c_1360])).

tff(c_22,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_53,plain,(
    ! [B_24,A_25] :
      ( B_24 = A_25
      | ~ r1_tarski(B_24,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_1388,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1384,c_62])).

tff(c_1394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1388])).

tff(c_1396,plain,(
    ! [B_151] :
      ( r2_hidden(B_151,'#skF_7')
      | ~ r2_hidden(B_151,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1354])).

tff(c_1434,plain,(
    ! [A_154] :
      ( r1_tarski(A_154,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_154,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1396,c_4])).

tff(c_1442,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_1434])).

tff(c_1447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_555,c_1442])).

tff(c_1448,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_1453,plain,(
    ! [A_42] :
      ( r1_tarski(k2_zfmisc_1('#skF_6',A_42),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_42,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_110])).

tff(c_1608,plain,(
    ! [B_163,A_164,C_165] :
      ( ~ r1_tarski(k2_zfmisc_1(B_163,A_164),k2_zfmisc_1(C_165,A_164))
      | r1_tarski(B_163,C_165)
      | k1_xboole_0 = A_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1612,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_1453,c_1608])).

tff(c_1642,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1612])).

tff(c_1644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_212,c_1642])).

tff(c_1646,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_1664,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_1646,c_16])).

tff(c_1667,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1664])).

tff(c_2005,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( r2_hidden(k4_tarski(A_196,B_197),k2_zfmisc_1(C_198,D_199))
      | ~ r2_hidden(B_197,D_199)
      | ~ r2_hidden(A_196,C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r2_hidden(A_44,C_45)
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1(C_45,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [A_44,B_46] :
      ( r2_hidden(A_44,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_112])).

tff(c_2026,plain,(
    ! [A_196,B_197] :
      ( r2_hidden(A_196,'#skF_6')
      | ~ r2_hidden(B_197,'#skF_5')
      | ~ r2_hidden(A_196,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2005,c_115])).

tff(c_2150,plain,(
    ! [B_207] : ~ r2_hidden(B_207,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2026])).

tff(c_2199,plain,(
    ! [B_209] : r1_tarski('#skF_5',B_209) ),
    inference(resolution,[status(thm)],[c_6,c_2150])).

tff(c_2203,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2199,c_62])).

tff(c_2209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2203])).

tff(c_2211,plain,(
    ! [A_210] :
      ( r2_hidden(A_210,'#skF_6')
      | ~ r2_hidden(A_210,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_2026])).

tff(c_2229,plain,(
    ! [A_211] :
      ( r1_tarski(A_211,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_211,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2211,c_4])).

tff(c_2237,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_2229])).

tff(c_2242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1667,c_1667,c_2237])).

tff(c_2243,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2244,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2249,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_44])).

tff(c_2303,plain,(
    ! [C_229,A_230,B_231] :
      ( r1_tarski(k2_zfmisc_1(C_229,A_230),k2_zfmisc_1(C_229,B_231))
      | ~ r1_tarski(A_230,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2343,plain,(
    ! [A_239] :
      ( r1_tarski(k2_zfmisc_1('#skF_4',A_239),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_239,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2249,c_2303])).

tff(c_30,plain,(
    ! [A_16,B_17,C_18] :
      ( ~ r1_tarski(k2_zfmisc_1(A_16,B_17),k2_zfmisc_1(A_16,C_18))
      | r1_tarski(B_17,C_18)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2346,plain,(
    ! [A_239] :
      ( r1_tarski(A_239,'#skF_5')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(A_239,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2343,c_30])).

tff(c_2358,plain,(
    ! [A_240] :
      ( r1_tarski(A_240,'#skF_5')
      | ~ r1_tarski(A_240,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2346])).

tff(c_2367,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_2358])).

tff(c_36,plain,(
    ! [A_19,C_21,B_20] :
      ( r1_tarski(k2_zfmisc_1(A_19,C_21),k2_zfmisc_1(B_20,C_21))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2317,plain,(
    ! [A_236,B_237,C_238] :
      ( ~ r1_tarski(k2_zfmisc_1(A_236,B_237),k2_zfmisc_1(A_236,C_238))
      | r1_tarski(B_237,C_238)
      | k1_xboole_0 = A_236 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2330,plain,(
    ! [B_237] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_237),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_237,'#skF_7')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2249,c_2317])).

tff(c_2375,plain,(
    ! [B_241] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_241),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_241,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2330])).

tff(c_2386,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2375])).

tff(c_2398,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2386])).

tff(c_2406,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_2398,c_16])).

tff(c_2411,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2367,c_2406])).

tff(c_2413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2243,c_2411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.99/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/2.62  
% 4.99/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/2.62  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 4.99/2.62  
% 4.99/2.62  %Foreground sorts:
% 4.99/2.62  
% 4.99/2.62  
% 4.99/2.62  %Background operators:
% 4.99/2.62  
% 4.99/2.62  
% 4.99/2.62  %Foreground operators:
% 4.99/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.99/2.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.99/2.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.99/2.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.99/2.62  tff('#skF_7', type, '#skF_7': $i).
% 4.99/2.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.99/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.99/2.62  tff('#skF_5', type, '#skF_5': $i).
% 4.99/2.62  tff('#skF_6', type, '#skF_6': $i).
% 4.99/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.99/2.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.99/2.62  tff('#skF_4', type, '#skF_4': $i).
% 4.99/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.99/2.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.99/2.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.99/2.62  
% 4.99/2.68  tff(f_81, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 4.99/2.68  tff(f_70, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 4.99/2.68  tff(f_64, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 4.99/2.68  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.99/2.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.99/2.68  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.99/2.68  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.99/2.68  tff(c_38, plain, ('#skF_7'!='#skF_5' | '#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.99/2.68  tff(c_48, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 4.99/2.68  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.99/2.68  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.99/2.68  tff(c_44, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.99/2.68  tff(c_88, plain, (![A_34, C_35, B_36]: (r1_tarski(k2_zfmisc_1(A_34, C_35), k2_zfmisc_1(B_36, C_35)) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.99/2.68  tff(c_93, plain, (![B_36]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_36, '#skF_7')) | ~r1_tarski('#skF_6', B_36))), inference(superposition, [status(thm), theory('equality')], [c_44, c_88])).
% 4.99/2.68  tff(c_164, plain, (![A_61, B_62, C_63]: (~r1_tarski(k2_zfmisc_1(A_61, B_62), k2_zfmisc_1(A_61, C_63)) | r1_tarski(B_62, C_63) | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.99/2.68  tff(c_168, plain, (r1_tarski('#skF_5', '#skF_7') | k1_xboole_0='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_93, c_164])).
% 4.99/2.68  tff(c_192, plain, (r1_tarski('#skF_5', '#skF_7') | ~r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_168])).
% 4.99/2.68  tff(c_212, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_192])).
% 4.99/2.68  tff(c_20, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.99/2.68  tff(c_102, plain, (![C_41, A_42, B_43]: (r1_tarski(k2_zfmisc_1(C_41, A_42), k2_zfmisc_1(C_41, B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.99/2.68  tff(c_110, plain, (![A_42]: (r1_tarski(k2_zfmisc_1('#skF_6', A_42), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_42, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_102])).
% 4.99/2.68  tff(c_254, plain, (![B_69, A_70, C_71]: (~r1_tarski(k2_zfmisc_1(B_69, A_70), k2_zfmisc_1(C_71, A_70)) | r1_tarski(B_69, C_71) | k1_xboole_0=A_70)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.99/2.68  tff(c_262, plain, (r1_tarski('#skF_6', '#skF_4') | k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_110, c_254])).
% 4.99/2.68  tff(c_285, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_40, c_212, c_262])).
% 4.99/2.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.99/2.68  tff(c_421, plain, (![A_81, B_82, C_83, D_84]: (r2_hidden(k4_tarski(A_81, B_82), k2_zfmisc_1(C_83, D_84)) | ~r2_hidden(B_82, D_84) | ~r2_hidden(A_81, C_83))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.99/2.68  tff(c_98, plain, (![B_37, D_38, A_39, C_40]: (r2_hidden(B_37, D_38) | ~r2_hidden(k4_tarski(A_39, B_37), k2_zfmisc_1(C_40, D_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.99/2.68  tff(c_101, plain, (![B_37, A_39]: (r2_hidden(B_37, '#skF_7') | ~r2_hidden(k4_tarski(A_39, B_37), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_98])).
% 4.99/2.68  tff(c_441, plain, (![B_82, A_81]: (r2_hidden(B_82, '#skF_7') | ~r2_hidden(B_82, '#skF_5') | ~r2_hidden(A_81, '#skF_4'))), inference(resolution, [status(thm)], [c_421, c_101])).
% 4.99/2.68  tff(c_447, plain, (![A_85]: (~r2_hidden(A_85, '#skF_4'))), inference(splitLeft, [status(thm)], [c_441])).
% 4.99/2.68  tff(c_469, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_447])).
% 4.99/2.68  tff(c_96, plain, (![A_34]: (r1_tarski(k2_zfmisc_1(A_34, '#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_34, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_88])).
% 4.99/2.68  tff(c_172, plain, (r1_tarski('#skF_7', '#skF_5') | k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_96, c_164])).
% 4.99/2.68  tff(c_195, plain, (r1_tarski('#skF_7', '#skF_5') | ~r1_tarski('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_172])).
% 4.99/2.68  tff(c_213, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_195])).
% 4.99/2.68  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_469, c_213])).
% 4.99/2.68  tff(c_496, plain, (![B_88]: (r2_hidden(B_88, '#skF_7') | ~r2_hidden(B_88, '#skF_5'))), inference(splitRight, [status(thm)], [c_441])).
% 4.99/2.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.99/2.68  tff(c_514, plain, (![A_89]: (r1_tarski(A_89, '#skF_7') | ~r2_hidden('#skF_1'(A_89, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_496, c_4])).
% 4.99/2.68  tff(c_522, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_514])).
% 4.99/2.68  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_285, c_522])).
% 4.99/2.68  tff(c_528, plain, (r1_tarski('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_195])).
% 4.99/2.68  tff(c_16, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.99/2.68  tff(c_549, plain, ('#skF_7'='#skF_5' | ~r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_528, c_16])).
% 4.99/2.68  tff(c_555, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_549])).
% 4.99/2.68  tff(c_1334, plain, (![A_145, B_146, C_147, D_148]: (r2_hidden(k4_tarski(A_145, B_146), k2_zfmisc_1(C_147, D_148)) | ~r2_hidden(B_146, D_148) | ~r2_hidden(A_145, C_147))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.99/2.68  tff(c_1354, plain, (![B_146, A_145]: (r2_hidden(B_146, '#skF_7') | ~r2_hidden(B_146, '#skF_5') | ~r2_hidden(A_145, '#skF_4'))), inference(resolution, [status(thm)], [c_1334, c_101])).
% 4.99/2.68  tff(c_1360, plain, (![A_149]: (~r2_hidden(A_149, '#skF_4'))), inference(splitLeft, [status(thm)], [c_1354])).
% 4.99/2.68  tff(c_1384, plain, (![B_150]: (r1_tarski('#skF_4', B_150))), inference(resolution, [status(thm)], [c_6, c_1360])).
% 4.99/2.68  tff(c_22, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.99/2.68  tff(c_53, plain, (![B_24, A_25]: (B_24=A_25 | ~r1_tarski(B_24, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.99/2.68  tff(c_62, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_53])).
% 4.99/2.68  tff(c_1388, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1384, c_62])).
% 4.99/2.68  tff(c_1394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1388])).
% 4.99/2.68  tff(c_1396, plain, (![B_151]: (r2_hidden(B_151, '#skF_7') | ~r2_hidden(B_151, '#skF_5'))), inference(splitRight, [status(thm)], [c_1354])).
% 4.99/2.68  tff(c_1434, plain, (![A_154]: (r1_tarski(A_154, '#skF_7') | ~r2_hidden('#skF_1'(A_154, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_1396, c_4])).
% 4.99/2.68  tff(c_1442, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_1434])).
% 4.99/2.68  tff(c_1447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_555, c_555, c_1442])).
% 4.99/2.68  tff(c_1448, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_549])).
% 4.99/2.68  tff(c_1453, plain, (![A_42]: (r1_tarski(k2_zfmisc_1('#skF_6', A_42), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_42, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_110])).
% 4.99/2.68  tff(c_1608, plain, (![B_163, A_164, C_165]: (~r1_tarski(k2_zfmisc_1(B_163, A_164), k2_zfmisc_1(C_165, A_164)) | r1_tarski(B_163, C_165) | k1_xboole_0=A_164)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.99/2.68  tff(c_1612, plain, (r1_tarski('#skF_6', '#skF_4') | k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_1453, c_1608])).
% 4.99/2.68  tff(c_1642, plain, (r1_tarski('#skF_6', '#skF_4') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1612])).
% 4.99/2.68  tff(c_1644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_212, c_1642])).
% 4.99/2.68  tff(c_1646, plain, (r1_tarski('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_192])).
% 4.99/2.68  tff(c_1664, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_1646, c_16])).
% 4.99/2.68  tff(c_1667, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_1664])).
% 4.99/2.68  tff(c_2005, plain, (![A_196, B_197, C_198, D_199]: (r2_hidden(k4_tarski(A_196, B_197), k2_zfmisc_1(C_198, D_199)) | ~r2_hidden(B_197, D_199) | ~r2_hidden(A_196, C_198))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.99/2.68  tff(c_112, plain, (![A_44, C_45, B_46, D_47]: (r2_hidden(A_44, C_45) | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1(C_45, D_47)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.99/2.68  tff(c_115, plain, (![A_44, B_46]: (r2_hidden(A_44, '#skF_6') | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_112])).
% 4.99/2.68  tff(c_2026, plain, (![A_196, B_197]: (r2_hidden(A_196, '#skF_6') | ~r2_hidden(B_197, '#skF_5') | ~r2_hidden(A_196, '#skF_4'))), inference(resolution, [status(thm)], [c_2005, c_115])).
% 4.99/2.68  tff(c_2150, plain, (![B_207]: (~r2_hidden(B_207, '#skF_5'))), inference(splitLeft, [status(thm)], [c_2026])).
% 4.99/2.68  tff(c_2199, plain, (![B_209]: (r1_tarski('#skF_5', B_209))), inference(resolution, [status(thm)], [c_6, c_2150])).
% 4.99/2.68  tff(c_2203, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2199, c_62])).
% 4.99/2.68  tff(c_2209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2203])).
% 4.99/2.68  tff(c_2211, plain, (![A_210]: (r2_hidden(A_210, '#skF_6') | ~r2_hidden(A_210, '#skF_4'))), inference(splitRight, [status(thm)], [c_2026])).
% 4.99/2.68  tff(c_2229, plain, (![A_211]: (r1_tarski(A_211, '#skF_6') | ~r2_hidden('#skF_1'(A_211, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_2211, c_4])).
% 4.99/2.68  tff(c_2237, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_2229])).
% 4.99/2.68  tff(c_2242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1667, c_1667, c_2237])).
% 4.99/2.68  tff(c_2243, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 4.99/2.68  tff(c_2244, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 4.99/2.68  tff(c_2249, plain, (k2_zfmisc_1('#skF_4', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2244, c_44])).
% 4.99/2.68  tff(c_2303, plain, (![C_229, A_230, B_231]: (r1_tarski(k2_zfmisc_1(C_229, A_230), k2_zfmisc_1(C_229, B_231)) | ~r1_tarski(A_230, B_231))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.99/2.68  tff(c_2343, plain, (![A_239]: (r1_tarski(k2_zfmisc_1('#skF_4', A_239), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(A_239, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2249, c_2303])).
% 4.99/2.68  tff(c_30, plain, (![A_16, B_17, C_18]: (~r1_tarski(k2_zfmisc_1(A_16, B_17), k2_zfmisc_1(A_16, C_18)) | r1_tarski(B_17, C_18) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.99/2.68  tff(c_2346, plain, (![A_239]: (r1_tarski(A_239, '#skF_5') | k1_xboole_0='#skF_4' | ~r1_tarski(A_239, '#skF_7'))), inference(resolution, [status(thm)], [c_2343, c_30])).
% 4.99/2.68  tff(c_2358, plain, (![A_240]: (r1_tarski(A_240, '#skF_5') | ~r1_tarski(A_240, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_42, c_2346])).
% 4.99/2.68  tff(c_2367, plain, (r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_20, c_2358])).
% 4.99/2.68  tff(c_36, plain, (![A_19, C_21, B_20]: (r1_tarski(k2_zfmisc_1(A_19, C_21), k2_zfmisc_1(B_20, C_21)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.99/2.68  tff(c_2317, plain, (![A_236, B_237, C_238]: (~r1_tarski(k2_zfmisc_1(A_236, B_237), k2_zfmisc_1(A_236, C_238)) | r1_tarski(B_237, C_238) | k1_xboole_0=A_236)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.99/2.68  tff(c_2330, plain, (![B_237]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_237), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_237, '#skF_7') | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2249, c_2317])).
% 4.99/2.68  tff(c_2375, plain, (![B_241]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_241), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_241, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_42, c_2330])).
% 4.99/2.68  tff(c_2386, plain, (r1_tarski('#skF_5', '#skF_7') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_2375])).
% 4.99/2.68  tff(c_2398, plain, (r1_tarski('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2386])).
% 4.99/2.68  tff(c_2406, plain, ('#skF_7'='#skF_5' | ~r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_2398, c_16])).
% 4.99/2.68  tff(c_2411, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2367, c_2406])).
% 4.99/2.68  tff(c_2413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2243, c_2411])).
% 4.99/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/2.68  
% 4.99/2.68  Inference rules
% 4.99/2.68  ----------------------
% 4.99/2.68  #Ref     : 0
% 4.99/2.68  #Sup     : 442
% 4.99/2.68  #Fact    : 0
% 4.99/2.68  #Define  : 0
% 4.99/2.68  #Split   : 22
% 4.99/2.68  #Chain   : 0
% 4.99/2.68  #Close   : 0
% 4.99/2.68  
% 4.99/2.68  Ordering : KBO
% 4.99/2.68  
% 4.99/2.68  Simplification rules
% 4.99/2.68  ----------------------
% 4.99/2.68  #Subsume      : 69
% 4.99/2.68  #Demod        : 240
% 4.99/2.68  #Tautology    : 185
% 4.99/2.68  #SimpNegUnit  : 61
% 4.99/2.68  #BackRed      : 65
% 4.99/2.68  
% 4.99/2.68  #Partial instantiations: 0
% 4.99/2.68  #Strategies tried      : 1
% 4.99/2.68  
% 4.99/2.68  Timing (in seconds)
% 4.99/2.68  ----------------------
% 5.38/2.69  Preprocessing        : 0.56
% 5.38/2.69  Parsing              : 0.30
% 5.38/2.69  CNF conversion       : 0.04
% 5.38/2.69  Main loop            : 1.15
% 5.38/2.69  Inferencing          : 0.44
% 5.38/2.69  Reduction            : 0.32
% 5.38/2.69  Demodulation         : 0.21
% 5.38/2.69  BG Simplification    : 0.06
% 5.38/2.69  Subsumption          : 0.26
% 5.38/2.69  Abstraction          : 0.04
% 5.38/2.69  MUC search           : 0.00
% 5.38/2.69  Cooper               : 0.00
% 5.38/2.69  Total                : 1.80
% 5.38/2.69  Index Insertion      : 0.00
% 5.38/2.69  Index Deletion       : 0.00
% 5.38/2.69  Index Matching       : 0.00
% 5.38/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
