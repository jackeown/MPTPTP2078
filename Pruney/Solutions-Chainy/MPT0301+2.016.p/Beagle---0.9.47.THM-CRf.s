%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:41 EST 2020

% Result     : Theorem 5.68s
% Output     : CNFRefutation 6.05s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 757 expanded)
%              Number of leaves         :   28 ( 237 expanded)
%              Depth                    :   13
%              Number of atoms          :  269 (1711 expanded)
%              Number of equality atoms :   92 ( 908 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_10 > #skF_9 > #skF_3 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
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

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r2_hidden('#skF_3'(A_6,B_7),A_6)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5849,plain,(
    ! [A_976,B_977] :
      ( r2_hidden('#skF_2'(A_976,B_977),B_977)
      | r2_hidden('#skF_3'(A_976,B_977),A_976)
      | B_977 = A_976 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5013,plain,(
    ! [A_845,B_846] :
      ( r2_hidden('#skF_2'(A_845,B_846),B_846)
      | r2_hidden('#skF_3'(A_845,B_846),A_845)
      | B_846 = A_845 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4110,plain,(
    ! [A_686,B_687] :
      ( r2_hidden('#skF_2'(A_686,B_687),B_687)
      | r2_hidden('#skF_3'(A_686,B_687),A_686)
      | B_687 = A_686 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2595,plain,(
    ! [A_413,B_414] :
      ( r2_hidden('#skF_2'(A_413,B_414),B_414)
      | r2_hidden('#skF_3'(A_413,B_414),A_413)
      | B_414 = A_413 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0
    | k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k2_zfmisc_1('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_65,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_261,plain,(
    ! [E_102,F_103,A_104,B_105] :
      ( r2_hidden(k4_tarski(E_102,F_103),k2_zfmisc_1(A_104,B_105))
      | ~ r2_hidden(F_103,B_105)
      | ~ r2_hidden(E_102,A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_268,plain,(
    ! [E_102,F_103] :
      ( r2_hidden(k4_tarski(E_102,F_103),k1_xboole_0)
      | ~ r2_hidden(F_103,'#skF_14')
      | ~ r2_hidden(E_102,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_261])).

tff(c_302,plain,(
    ! [E_109,F_110] :
      ( r2_hidden(k4_tarski(E_109,F_110),k1_xboole_0)
      | ~ r2_hidden(F_110,'#skF_14')
      | ~ r2_hidden(E_109,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_261])).

tff(c_24,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_91,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,B_65)
      | ~ r2_hidden(C_66,A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    ! [C_66,A_15] :
      ( ~ r2_hidden(C_66,k1_xboole_0)
      | ~ r2_hidden(C_66,A_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_91])).

tff(c_367,plain,(
    ! [E_120,F_121,A_122] :
      ( ~ r2_hidden(k4_tarski(E_120,F_121),A_122)
      | ~ r2_hidden(F_121,'#skF_14')
      | ~ r2_hidden(E_120,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_302,c_94])).

tff(c_374,plain,(
    ! [F_103,E_102] :
      ( ~ r2_hidden(F_103,'#skF_14')
      | ~ r2_hidden(E_102,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_268,c_367])).

tff(c_376,plain,(
    ! [E_102] : ~ r2_hidden(E_102,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_439,plain,(
    ! [A_127,B_128,D_129] :
      ( r2_hidden('#skF_9'(A_127,B_128,k2_zfmisc_1(A_127,B_128),D_129),A_127)
      | ~ r2_hidden(D_129,k2_zfmisc_1(A_127,B_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_455,plain,(
    ! [D_129] :
      ( r2_hidden('#skF_9'('#skF_13','#skF_14',k1_xboole_0,D_129),'#skF_13')
      | ~ r2_hidden(D_129,k2_zfmisc_1('#skF_13','#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_439])).

tff(c_461,plain,(
    ! [D_129] :
      ( r2_hidden('#skF_9'('#skF_13','#skF_14',k1_xboole_0,D_129),'#skF_13')
      | ~ r2_hidden(D_129,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_455])).

tff(c_463,plain,(
    ! [D_130] : ~ r2_hidden(D_130,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_461])).

tff(c_948,plain,(
    ! [B_175] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_175),B_175)
      | k1_xboole_0 = B_175 ) ),
    inference(resolution,[status(thm)],[c_14,c_463])).

tff(c_972,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_948,c_376])).

tff(c_991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_972])).

tff(c_992,plain,(
    ! [F_103] : ~ r2_hidden(F_103,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_328,plain,(
    ! [A_114,B_115,D_116] :
      ( r2_hidden('#skF_10'(A_114,B_115,k2_zfmisc_1(A_114,B_115),D_116),B_115)
      | ~ r2_hidden(D_116,k2_zfmisc_1(A_114,B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_340,plain,(
    ! [D_116] :
      ( r2_hidden('#skF_10'('#skF_13','#skF_14',k1_xboole_0,D_116),'#skF_14')
      | ~ r2_hidden(D_116,k2_zfmisc_1('#skF_13','#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_328])).

tff(c_345,plain,(
    ! [D_116] :
      ( r2_hidden('#skF_10'('#skF_13','#skF_14',k1_xboole_0,D_116),'#skF_14')
      | ~ r2_hidden(D_116,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_340])).

tff(c_1042,plain,(
    ! [D_177] : ~ r2_hidden(D_177,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_992,c_345])).

tff(c_1560,plain,(
    ! [B_228] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_228),B_228)
      | k1_xboole_0 = B_228 ) ),
    inference(resolution,[status(thm)],[c_14,c_1042])).

tff(c_1584,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_1560,c_992])).

tff(c_1603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1584])).

tff(c_1604,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1606,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1604])).

tff(c_1605,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2474,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_1605])).

tff(c_1610,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_24])).

tff(c_1640,plain,(
    ! [A_243,B_244,C_245] :
      ( ~ r1_xboole_0(A_243,B_244)
      | ~ r2_hidden(C_245,B_244)
      | ~ r2_hidden(C_245,A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1651,plain,(
    ! [C_248,A_249] :
      ( ~ r2_hidden(C_248,'#skF_12')
      | ~ r2_hidden(C_248,A_249) ) ),
    inference(resolution,[status(thm)],[c_1610,c_1640])).

tff(c_1949,plain,(
    ! [B_314,A_315] :
      ( ~ r2_hidden('#skF_3'('#skF_12',B_314),A_315)
      | r2_hidden('#skF_2'('#skF_12',B_314),B_314)
      | B_314 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_14,c_1651])).

tff(c_1957,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'('#skF_12',B_7),B_7)
      | B_7 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_14,c_1949])).

tff(c_30,plain,(
    ! [A_16,B_17,D_43] :
      ( r2_hidden('#skF_10'(A_16,B_17,k2_zfmisc_1(A_16,B_17),D_43),B_17)
      | ~ r2_hidden(D_43,k2_zfmisc_1(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    ! [A_16,B_17,D_43] :
      ( r2_hidden('#skF_9'(A_16,B_17,k2_zfmisc_1(A_16,B_17),D_43),A_16)
      | ~ r2_hidden(D_43,k2_zfmisc_1(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1837,plain,(
    ! [A_290,B_291,D_292] :
      ( r2_hidden('#skF_9'(A_290,B_291,k2_zfmisc_1(A_290,B_291),D_292),A_290)
      | ~ r2_hidden(D_292,k2_zfmisc_1(A_290,B_291)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1643,plain,(
    ! [C_245,A_15] :
      ( ~ r2_hidden(C_245,'#skF_12')
      | ~ r2_hidden(C_245,A_15) ) ),
    inference(resolution,[status(thm)],[c_1610,c_1640])).

tff(c_2158,plain,(
    ! [B_358,D_359,A_360] :
      ( ~ r2_hidden('#skF_9'('#skF_12',B_358,k2_zfmisc_1('#skF_12',B_358),D_359),A_360)
      | ~ r2_hidden(D_359,k2_zfmisc_1('#skF_12',B_358)) ) ),
    inference(resolution,[status(thm)],[c_1837,c_1643])).

tff(c_2165,plain,(
    ! [D_366,B_367] : ~ r2_hidden(D_366,k2_zfmisc_1('#skF_12',B_367)) ),
    inference(resolution,[status(thm)],[c_32,c_2158])).

tff(c_2241,plain,(
    ! [B_367] : k2_zfmisc_1('#skF_12',B_367) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1957,c_2165])).

tff(c_2163,plain,(
    ! [D_43,B_17] : ~ r2_hidden(D_43,k2_zfmisc_1('#skF_12',B_17)) ),
    inference(resolution,[status(thm)],[c_32,c_2158])).

tff(c_2283,plain,(
    ! [D_369] : ~ r2_hidden(D_369,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_2163])).

tff(c_2374,plain,(
    ! [D_375,A_376] : ~ r2_hidden(D_375,k2_zfmisc_1(A_376,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_30,c_2283])).

tff(c_2453,plain,(
    ! [A_376] : k2_zfmisc_1(A_376,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1957,c_2374])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0
    | k2_zfmisc_1('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1617,plain,
    ( k2_zfmisc_1('#skF_11','#skF_12') != '#skF_12'
    | k2_zfmisc_1('#skF_13','#skF_14') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_1606,c_58])).

tff(c_1618,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1617])).

tff(c_2471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2453,c_1618])).

tff(c_2472,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1617])).

tff(c_2475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2474,c_2472])).

tff(c_2476,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_1604])).

tff(c_2481,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_24])).

tff(c_2502,plain,(
    ! [A_388,B_389,C_390] :
      ( ~ r1_xboole_0(A_388,B_389)
      | ~ r2_hidden(C_390,B_389)
      | ~ r2_hidden(C_390,A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2505,plain,(
    ! [C_390,A_15] :
      ( ~ r2_hidden(C_390,'#skF_11')
      | ~ r2_hidden(C_390,A_15) ) ),
    inference(resolution,[status(thm)],[c_2481,c_2502])).

tff(c_2821,plain,(
    ! [B_462,A_463] :
      ( ~ r2_hidden('#skF_3'('#skF_11',B_462),A_463)
      | r2_hidden('#skF_2'('#skF_11',B_462),B_462)
      | B_462 = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_2595,c_2505])).

tff(c_2829,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'('#skF_11',B_7),B_7)
      | B_7 = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_14,c_2821])).

tff(c_2758,plain,(
    ! [A_447,B_448,D_449] :
      ( r2_hidden('#skF_9'(A_447,B_448,k2_zfmisc_1(A_447,B_448),D_449),A_447)
      | ~ r2_hidden(D_449,k2_zfmisc_1(A_447,B_448)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3021,plain,(
    ! [B_508,D_509,A_510] :
      ( ~ r2_hidden('#skF_9'('#skF_11',B_508,k2_zfmisc_1('#skF_11',B_508),D_509),A_510)
      | ~ r2_hidden(D_509,k2_zfmisc_1('#skF_11',B_508)) ) ),
    inference(resolution,[status(thm)],[c_2758,c_2505])).

tff(c_3027,plain,(
    ! [D_511,B_512] : ~ r2_hidden(D_511,k2_zfmisc_1('#skF_11',B_512)) ),
    inference(resolution,[status(thm)],[c_32,c_3021])).

tff(c_3105,plain,(
    ! [B_512] : k2_zfmisc_1('#skF_11',B_512) = '#skF_11' ),
    inference(resolution,[status(thm)],[c_2829,c_3027])).

tff(c_2489,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_1605])).

tff(c_2491,plain,
    ( k2_zfmisc_1('#skF_11','#skF_12') != '#skF_11'
    | k2_zfmisc_1('#skF_13','#skF_14') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_2476,c_58])).

tff(c_2492,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_2489,c_2491])).

tff(c_3121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3105,c_2492])).

tff(c_3123,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3138,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3123,c_24])).

tff(c_4050,plain,(
    ! [A_670,B_671,C_672] :
      ( ~ r1_xboole_0(A_670,B_671)
      | ~ r2_hidden(C_672,B_671)
      | ~ r2_hidden(C_672,A_670) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4053,plain,(
    ! [C_672,A_15] :
      ( ~ r2_hidden(C_672,'#skF_14')
      | ~ r2_hidden(C_672,A_15) ) ),
    inference(resolution,[status(thm)],[c_3138,c_4050])).

tff(c_4371,plain,(
    ! [B_746,A_747] :
      ( ~ r2_hidden('#skF_3'('#skF_14',B_746),A_747)
      | r2_hidden('#skF_2'('#skF_14',B_746),B_746)
      | B_746 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_4110,c_4053])).

tff(c_4378,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'('#skF_14',B_7),B_7)
      | B_7 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_14,c_4371])).

tff(c_4278,plain,(
    ! [A_720,B_721,D_722] :
      ( r2_hidden('#skF_10'(A_720,B_721,k2_zfmisc_1(A_720,B_721),D_722),B_721)
      | ~ r2_hidden(D_722,k2_zfmisc_1(A_720,B_721)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4573,plain,(
    ! [A_790,D_791,A_792] :
      ( ~ r2_hidden('#skF_10'(A_790,'#skF_14',k2_zfmisc_1(A_790,'#skF_14'),D_791),A_792)
      | ~ r2_hidden(D_791,k2_zfmisc_1(A_790,'#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_4278,c_4053])).

tff(c_4579,plain,(
    ! [D_793,A_794] : ~ r2_hidden(D_793,k2_zfmisc_1(A_794,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_30,c_4573])).

tff(c_4657,plain,(
    ! [A_794] : k2_zfmisc_1(A_794,'#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_4378,c_4579])).

tff(c_4578,plain,(
    ! [D_43,A_16] : ~ r2_hidden(D_43,k2_zfmisc_1(A_16,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_30,c_4573])).

tff(c_4697,plain,(
    ! [D_796] : ~ r2_hidden(D_796,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4657,c_4578])).

tff(c_4789,plain,(
    ! [D_807,B_808] : ~ r2_hidden(D_807,k2_zfmisc_1('#skF_14',B_808)) ),
    inference(resolution,[status(thm)],[c_32,c_4697])).

tff(c_4870,plain,(
    ! [B_808] : k2_zfmisc_1('#skF_14',B_808) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_4378,c_4789])).

tff(c_3222,plain,(
    ! [A_537,B_538] :
      ( r2_hidden('#skF_2'(A_537,B_538),B_538)
      | r2_hidden('#skF_3'(A_537,B_538),A_537)
      | B_538 = A_537 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3122,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3146,plain,
    ( '#skF_11' = '#skF_14'
    | '#skF_14' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3123,c_3123,c_3122])).

tff(c_3147,plain,(
    '#skF_14' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_3146])).

tff(c_3148,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3147,c_3138])).

tff(c_3177,plain,(
    ! [A_526,B_527,C_528] :
      ( ~ r1_xboole_0(A_526,B_527)
      | ~ r2_hidden(C_528,B_527)
      | ~ r2_hidden(C_528,A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3180,plain,(
    ! [C_528,A_15] :
      ( ~ r2_hidden(C_528,'#skF_12')
      | ~ r2_hidden(C_528,A_15) ) ),
    inference(resolution,[status(thm)],[c_3148,c_3177])).

tff(c_3496,plain,(
    ! [B_600,A_601] :
      ( ~ r2_hidden('#skF_3'('#skF_12',B_600),A_601)
      | r2_hidden('#skF_2'('#skF_12',B_600),B_600)
      | B_600 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_3222,c_3180])).

tff(c_3504,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'('#skF_12',B_7),B_7)
      | B_7 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_14,c_3496])).

tff(c_3482,plain,(
    ! [A_597,B_598,D_599] :
      ( r2_hidden('#skF_9'(A_597,B_598,k2_zfmisc_1(A_597,B_598),D_599),A_597)
      | ~ r2_hidden(D_599,k2_zfmisc_1(A_597,B_598)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3693,plain,(
    ! [B_641,D_642,A_643] :
      ( ~ r2_hidden('#skF_9'('#skF_12',B_641,k2_zfmisc_1('#skF_12',B_641),D_642),A_643)
      | ~ r2_hidden(D_642,k2_zfmisc_1('#skF_12',B_641)) ) ),
    inference(resolution,[status(thm)],[c_3482,c_3180])).

tff(c_3711,plain,(
    ! [D_647,B_648] : ~ r2_hidden(D_647,k2_zfmisc_1('#skF_12',B_648)) ),
    inference(resolution,[status(thm)],[c_32,c_3693])).

tff(c_3789,plain,(
    ! [B_648] : k2_zfmisc_1('#skF_12',B_648) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3504,c_3711])).

tff(c_3698,plain,(
    ! [D_43,B_17] : ~ r2_hidden(D_43,k2_zfmisc_1('#skF_12',B_17)) ),
    inference(resolution,[status(thm)],[c_32,c_3693])).

tff(c_3829,plain,(
    ! [D_650] : ~ r2_hidden(D_650,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3789,c_3698])).

tff(c_3920,plain,(
    ! [D_656,A_657] : ~ r2_hidden(D_656,k2_zfmisc_1(A_657,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_30,c_3829])).

tff(c_4001,plain,(
    ! [A_657] : k2_zfmisc_1(A_657,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3504,c_3920])).

tff(c_3151,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3147,c_3123])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3124,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_3133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3123,c_3124])).

tff(c_3134,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3164,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_3134])).

tff(c_4017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4001,c_3164])).

tff(c_4018,plain,(
    '#skF_11' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_3146])).

tff(c_4024,plain,(
    k2_zfmisc_1('#skF_14','#skF_12') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_3123,c_3134])).

tff(c_4886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4870,c_4024])).

tff(c_4888,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4890,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4888,c_24])).

tff(c_4920,plain,(
    ! [A_820,B_821,C_822] :
      ( ~ r1_xboole_0(A_820,B_821)
      | ~ r2_hidden(C_822,B_821)
      | ~ r2_hidden(C_822,A_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4923,plain,(
    ! [C_822,A_15] :
      ( ~ r2_hidden(C_822,'#skF_13')
      | ~ r2_hidden(C_822,A_15) ) ),
    inference(resolution,[status(thm)],[c_4890,c_4920])).

tff(c_5250,plain,(
    ! [B_896,A_897] :
      ( ~ r2_hidden('#skF_3'('#skF_13',B_896),A_897)
      | r2_hidden('#skF_2'('#skF_13',B_896),B_896)
      | B_896 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_5013,c_4923])).

tff(c_5258,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'('#skF_13',B_7),B_7)
      | B_7 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_14,c_5250])).

tff(c_5184,plain,(
    ! [A_879,B_880,D_881] :
      ( r2_hidden('#skF_10'(A_879,B_880,k2_zfmisc_1(A_879,B_880),D_881),B_880)
      | ~ r2_hidden(D_881,k2_zfmisc_1(A_879,B_880)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5401,plain,(
    ! [A_921,D_922,A_923] :
      ( ~ r2_hidden('#skF_10'(A_921,'#skF_13',k2_zfmisc_1(A_921,'#skF_13'),D_922),A_923)
      | ~ r2_hidden(D_922,k2_zfmisc_1(A_921,'#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_5184,c_4923])).

tff(c_5407,plain,(
    ! [D_924,A_925] : ~ r2_hidden(D_924,k2_zfmisc_1(A_925,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_30,c_5401])).

tff(c_5485,plain,(
    ! [A_925] : k2_zfmisc_1(A_925,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_5258,c_5407])).

tff(c_5406,plain,(
    ! [D_43,A_16] : ~ r2_hidden(D_43,k2_zfmisc_1(A_16,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_30,c_5401])).

tff(c_5526,plain,(
    ! [D_932] : ~ r2_hidden(D_932,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5485,c_5406])).

tff(c_5612,plain,(
    ! [D_933,B_934] : ~ r2_hidden(D_933,k2_zfmisc_1('#skF_13',B_934)) ),
    inference(resolution,[status(thm)],[c_32,c_5526])).

tff(c_5693,plain,(
    ! [B_934] : k2_zfmisc_1('#skF_13',B_934) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_5258,c_5612])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4899,plain,
    ( '#skF_13' = '#skF_12'
    | '#skF_11' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4888,c_4888,c_4888,c_56])).

tff(c_4900,plain,(
    '#skF_11' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_4899])).

tff(c_4887,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4897,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4888,c_4887])).

tff(c_4901,plain,(
    k2_zfmisc_1('#skF_13','#skF_12') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4900,c_4897])).

tff(c_5721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5693,c_4901])).

tff(c_5722,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_4899])).

tff(c_5725,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5722,c_4890])).

tff(c_5766,plain,(
    ! [A_952,B_953,C_954] :
      ( ~ r1_xboole_0(A_952,B_953)
      | ~ r2_hidden(C_954,B_953)
      | ~ r2_hidden(C_954,A_952) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5769,plain,(
    ! [C_954,A_15] :
      ( ~ r2_hidden(C_954,'#skF_12')
      | ~ r2_hidden(C_954,A_15) ) ),
    inference(resolution,[status(thm)],[c_5725,c_5766])).

tff(c_6076,plain,(
    ! [B_1026,A_1027] :
      ( ~ r2_hidden('#skF_3'('#skF_12',B_1026),A_1027)
      | r2_hidden('#skF_2'('#skF_12',B_1026),B_1026)
      | B_1026 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_5849,c_5769])).

tff(c_6083,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_2'('#skF_12',B_7),B_7)
      | B_7 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_14,c_6076])).

tff(c_6025,plain,(
    ! [A_1008,B_1009,D_1010] :
      ( r2_hidden('#skF_9'(A_1008,B_1009,k2_zfmisc_1(A_1008,B_1009),D_1010),A_1008)
      | ~ r2_hidden(D_1010,k2_zfmisc_1(A_1008,B_1009)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6252,plain,(
    ! [B_1063,D_1064,A_1065] :
      ( ~ r2_hidden('#skF_9'('#skF_12',B_1063,k2_zfmisc_1('#skF_12',B_1063),D_1064),A_1065)
      | ~ r2_hidden(D_1064,k2_zfmisc_1('#skF_12',B_1063)) ) ),
    inference(resolution,[status(thm)],[c_6025,c_5769])).

tff(c_6258,plain,(
    ! [D_1066,B_1067] : ~ r2_hidden(D_1066,k2_zfmisc_1('#skF_12',B_1067)) ),
    inference(resolution,[status(thm)],[c_32,c_6252])).

tff(c_6336,plain,(
    ! [B_1067] : k2_zfmisc_1('#skF_12',B_1067) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6083,c_6258])).

tff(c_6257,plain,(
    ! [D_43,B_17] : ~ r2_hidden(D_43,k2_zfmisc_1('#skF_12',B_17)) ),
    inference(resolution,[status(thm)],[c_32,c_6252])).

tff(c_6379,plain,(
    ! [D_1074] : ~ r2_hidden(D_1074,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6336,c_6257])).

tff(c_6468,plain,(
    ! [D_1080,A_1081] : ~ r2_hidden(D_1080,k2_zfmisc_1(A_1081,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_30,c_6379])).

tff(c_6549,plain,(
    ! [A_1081] : k2_zfmisc_1(A_1081,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6083,c_6468])).

tff(c_5724,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5722,c_4897])).

tff(c_6565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6549,c_5724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:28:38 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.68/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.28  
% 5.68/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_10 > #skF_9 > #skF_3 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4
% 5.68/2.29  
% 5.68/2.29  %Foreground sorts:
% 5.68/2.29  
% 5.68/2.29  
% 5.68/2.29  %Background operators:
% 5.68/2.29  
% 5.68/2.29  
% 5.68/2.29  %Foreground operators:
% 5.68/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.68/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.68/2.29  tff('#skF_11', type, '#skF_11': $i).
% 5.68/2.29  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.68/2.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.68/2.29  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 5.68/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.68/2.29  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 5.68/2.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.68/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.68/2.29  tff('#skF_14', type, '#skF_14': $i).
% 5.68/2.29  tff('#skF_13', type, '#skF_13': $i).
% 5.68/2.29  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.68/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.68/2.29  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.68/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.68/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.68/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.68/2.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.68/2.29  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.68/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.68/2.29  tff('#skF_12', type, '#skF_12': $i).
% 5.68/2.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.68/2.29  
% 6.05/2.31  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 6.05/2.31  tff(f_80, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.05/2.31  tff(f_73, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.05/2.31  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.05/2.31  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.05/2.31  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r2_hidden('#skF_3'(A_6, B_7), A_6) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.05/2.31  tff(c_5849, plain, (![A_976, B_977]: (r2_hidden('#skF_2'(A_976, B_977), B_977) | r2_hidden('#skF_3'(A_976, B_977), A_976) | B_977=A_976)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.05/2.31  tff(c_5013, plain, (![A_845, B_846]: (r2_hidden('#skF_2'(A_845, B_846), B_846) | r2_hidden('#skF_3'(A_845, B_846), A_845) | B_846=A_845)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.05/2.31  tff(c_4110, plain, (![A_686, B_687]: (r2_hidden('#skF_2'(A_686, B_687), B_687) | r2_hidden('#skF_3'(A_686, B_687), A_686) | B_687=A_686)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.05/2.31  tff(c_2595, plain, (![A_413, B_414]: (r2_hidden('#skF_2'(A_413, B_414), B_414) | r2_hidden('#skF_3'(A_413, B_414), A_413) | B_414=A_413)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.05/2.31  tff(c_52, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.05/2.31  tff(c_64, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_52])).
% 6.05/2.31  tff(c_54, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0 | k1_xboole_0!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.05/2.31  tff(c_63, plain, (k1_xboole_0!='#skF_13'), inference(splitLeft, [status(thm)], [c_54])).
% 6.05/2.31  tff(c_60, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_13', '#skF_14')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.05/2.31  tff(c_65, plain, (k2_zfmisc_1('#skF_13', '#skF_14')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 6.05/2.31  tff(c_261, plain, (![E_102, F_103, A_104, B_105]: (r2_hidden(k4_tarski(E_102, F_103), k2_zfmisc_1(A_104, B_105)) | ~r2_hidden(F_103, B_105) | ~r2_hidden(E_102, A_104))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_268, plain, (![E_102, F_103]: (r2_hidden(k4_tarski(E_102, F_103), k1_xboole_0) | ~r2_hidden(F_103, '#skF_14') | ~r2_hidden(E_102, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_261])).
% 6.05/2.31  tff(c_302, plain, (![E_109, F_110]: (r2_hidden(k4_tarski(E_109, F_110), k1_xboole_0) | ~r2_hidden(F_110, '#skF_14') | ~r2_hidden(E_109, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_261])).
% 6.05/2.31  tff(c_24, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.05/2.31  tff(c_91, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, B_65) | ~r2_hidden(C_66, A_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.05/2.31  tff(c_94, plain, (![C_66, A_15]: (~r2_hidden(C_66, k1_xboole_0) | ~r2_hidden(C_66, A_15))), inference(resolution, [status(thm)], [c_24, c_91])).
% 6.05/2.31  tff(c_367, plain, (![E_120, F_121, A_122]: (~r2_hidden(k4_tarski(E_120, F_121), A_122) | ~r2_hidden(F_121, '#skF_14') | ~r2_hidden(E_120, '#skF_13'))), inference(resolution, [status(thm)], [c_302, c_94])).
% 6.05/2.31  tff(c_374, plain, (![F_103, E_102]: (~r2_hidden(F_103, '#skF_14') | ~r2_hidden(E_102, '#skF_13'))), inference(resolution, [status(thm)], [c_268, c_367])).
% 6.05/2.31  tff(c_376, plain, (![E_102]: (~r2_hidden(E_102, '#skF_13'))), inference(splitLeft, [status(thm)], [c_374])).
% 6.05/2.31  tff(c_439, plain, (![A_127, B_128, D_129]: (r2_hidden('#skF_9'(A_127, B_128, k2_zfmisc_1(A_127, B_128), D_129), A_127) | ~r2_hidden(D_129, k2_zfmisc_1(A_127, B_128)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_455, plain, (![D_129]: (r2_hidden('#skF_9'('#skF_13', '#skF_14', k1_xboole_0, D_129), '#skF_13') | ~r2_hidden(D_129, k2_zfmisc_1('#skF_13', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_65, c_439])).
% 6.05/2.31  tff(c_461, plain, (![D_129]: (r2_hidden('#skF_9'('#skF_13', '#skF_14', k1_xboole_0, D_129), '#skF_13') | ~r2_hidden(D_129, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_455])).
% 6.05/2.31  tff(c_463, plain, (![D_130]: (~r2_hidden(D_130, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_376, c_461])).
% 6.05/2.31  tff(c_948, plain, (![B_175]: (r2_hidden('#skF_2'(k1_xboole_0, B_175), B_175) | k1_xboole_0=B_175)), inference(resolution, [status(thm)], [c_14, c_463])).
% 6.05/2.31  tff(c_972, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_948, c_376])).
% 6.05/2.31  tff(c_991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_972])).
% 6.05/2.31  tff(c_992, plain, (![F_103]: (~r2_hidden(F_103, '#skF_14'))), inference(splitRight, [status(thm)], [c_374])).
% 6.05/2.31  tff(c_328, plain, (![A_114, B_115, D_116]: (r2_hidden('#skF_10'(A_114, B_115, k2_zfmisc_1(A_114, B_115), D_116), B_115) | ~r2_hidden(D_116, k2_zfmisc_1(A_114, B_115)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_340, plain, (![D_116]: (r2_hidden('#skF_10'('#skF_13', '#skF_14', k1_xboole_0, D_116), '#skF_14') | ~r2_hidden(D_116, k2_zfmisc_1('#skF_13', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_65, c_328])).
% 6.05/2.31  tff(c_345, plain, (![D_116]: (r2_hidden('#skF_10'('#skF_13', '#skF_14', k1_xboole_0, D_116), '#skF_14') | ~r2_hidden(D_116, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_340])).
% 6.05/2.31  tff(c_1042, plain, (![D_177]: (~r2_hidden(D_177, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_992, c_345])).
% 6.05/2.31  tff(c_1560, plain, (![B_228]: (r2_hidden('#skF_2'(k1_xboole_0, B_228), B_228) | k1_xboole_0=B_228)), inference(resolution, [status(thm)], [c_14, c_1042])).
% 6.05/2.31  tff(c_1584, plain, (k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_1560, c_992])).
% 6.05/2.31  tff(c_1603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1584])).
% 6.05/2.31  tff(c_1604, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_60])).
% 6.05/2.31  tff(c_1606, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_1604])).
% 6.05/2.31  tff(c_1605, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 6.05/2.31  tff(c_2474, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1605])).
% 6.05/2.31  tff(c_1610, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_24])).
% 6.05/2.31  tff(c_1640, plain, (![A_243, B_244, C_245]: (~r1_xboole_0(A_243, B_244) | ~r2_hidden(C_245, B_244) | ~r2_hidden(C_245, A_243))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.05/2.31  tff(c_1651, plain, (![C_248, A_249]: (~r2_hidden(C_248, '#skF_12') | ~r2_hidden(C_248, A_249))), inference(resolution, [status(thm)], [c_1610, c_1640])).
% 6.05/2.31  tff(c_1949, plain, (![B_314, A_315]: (~r2_hidden('#skF_3'('#skF_12', B_314), A_315) | r2_hidden('#skF_2'('#skF_12', B_314), B_314) | B_314='#skF_12')), inference(resolution, [status(thm)], [c_14, c_1651])).
% 6.05/2.31  tff(c_1957, plain, (![B_7]: (r2_hidden('#skF_2'('#skF_12', B_7), B_7) | B_7='#skF_12')), inference(resolution, [status(thm)], [c_14, c_1949])).
% 6.05/2.31  tff(c_30, plain, (![A_16, B_17, D_43]: (r2_hidden('#skF_10'(A_16, B_17, k2_zfmisc_1(A_16, B_17), D_43), B_17) | ~r2_hidden(D_43, k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_32, plain, (![A_16, B_17, D_43]: (r2_hidden('#skF_9'(A_16, B_17, k2_zfmisc_1(A_16, B_17), D_43), A_16) | ~r2_hidden(D_43, k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_1837, plain, (![A_290, B_291, D_292]: (r2_hidden('#skF_9'(A_290, B_291, k2_zfmisc_1(A_290, B_291), D_292), A_290) | ~r2_hidden(D_292, k2_zfmisc_1(A_290, B_291)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_1643, plain, (![C_245, A_15]: (~r2_hidden(C_245, '#skF_12') | ~r2_hidden(C_245, A_15))), inference(resolution, [status(thm)], [c_1610, c_1640])).
% 6.05/2.31  tff(c_2158, plain, (![B_358, D_359, A_360]: (~r2_hidden('#skF_9'('#skF_12', B_358, k2_zfmisc_1('#skF_12', B_358), D_359), A_360) | ~r2_hidden(D_359, k2_zfmisc_1('#skF_12', B_358)))), inference(resolution, [status(thm)], [c_1837, c_1643])).
% 6.05/2.31  tff(c_2165, plain, (![D_366, B_367]: (~r2_hidden(D_366, k2_zfmisc_1('#skF_12', B_367)))), inference(resolution, [status(thm)], [c_32, c_2158])).
% 6.05/2.31  tff(c_2241, plain, (![B_367]: (k2_zfmisc_1('#skF_12', B_367)='#skF_12')), inference(resolution, [status(thm)], [c_1957, c_2165])).
% 6.05/2.31  tff(c_2163, plain, (![D_43, B_17]: (~r2_hidden(D_43, k2_zfmisc_1('#skF_12', B_17)))), inference(resolution, [status(thm)], [c_32, c_2158])).
% 6.05/2.31  tff(c_2283, plain, (![D_369]: (~r2_hidden(D_369, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_2163])).
% 6.05/2.31  tff(c_2374, plain, (![D_375, A_376]: (~r2_hidden(D_375, k2_zfmisc_1(A_376, '#skF_12')))), inference(resolution, [status(thm)], [c_30, c_2283])).
% 6.05/2.31  tff(c_2453, plain, (![A_376]: (k2_zfmisc_1(A_376, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_1957, c_2374])).
% 6.05/2.31  tff(c_58, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0 | k2_zfmisc_1('#skF_13', '#skF_14')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.05/2.31  tff(c_1617, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_12' | k2_zfmisc_1('#skF_13', '#skF_14')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1606, c_58])).
% 6.05/2.31  tff(c_1618, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_12'), inference(splitLeft, [status(thm)], [c_1617])).
% 6.05/2.31  tff(c_2471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2453, c_1618])).
% 6.05/2.31  tff(c_2472, plain, (k2_zfmisc_1('#skF_13', '#skF_14')='#skF_12'), inference(splitRight, [status(thm)], [c_1617])).
% 6.05/2.31  tff(c_2475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2474, c_2472])).
% 6.05/2.31  tff(c_2476, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_1604])).
% 6.05/2.31  tff(c_2481, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_24])).
% 6.05/2.31  tff(c_2502, plain, (![A_388, B_389, C_390]: (~r1_xboole_0(A_388, B_389) | ~r2_hidden(C_390, B_389) | ~r2_hidden(C_390, A_388))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.05/2.31  tff(c_2505, plain, (![C_390, A_15]: (~r2_hidden(C_390, '#skF_11') | ~r2_hidden(C_390, A_15))), inference(resolution, [status(thm)], [c_2481, c_2502])).
% 6.05/2.31  tff(c_2821, plain, (![B_462, A_463]: (~r2_hidden('#skF_3'('#skF_11', B_462), A_463) | r2_hidden('#skF_2'('#skF_11', B_462), B_462) | B_462='#skF_11')), inference(resolution, [status(thm)], [c_2595, c_2505])).
% 6.05/2.31  tff(c_2829, plain, (![B_7]: (r2_hidden('#skF_2'('#skF_11', B_7), B_7) | B_7='#skF_11')), inference(resolution, [status(thm)], [c_14, c_2821])).
% 6.05/2.31  tff(c_2758, plain, (![A_447, B_448, D_449]: (r2_hidden('#skF_9'(A_447, B_448, k2_zfmisc_1(A_447, B_448), D_449), A_447) | ~r2_hidden(D_449, k2_zfmisc_1(A_447, B_448)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_3021, plain, (![B_508, D_509, A_510]: (~r2_hidden('#skF_9'('#skF_11', B_508, k2_zfmisc_1('#skF_11', B_508), D_509), A_510) | ~r2_hidden(D_509, k2_zfmisc_1('#skF_11', B_508)))), inference(resolution, [status(thm)], [c_2758, c_2505])).
% 6.05/2.31  tff(c_3027, plain, (![D_511, B_512]: (~r2_hidden(D_511, k2_zfmisc_1('#skF_11', B_512)))), inference(resolution, [status(thm)], [c_32, c_3021])).
% 6.05/2.31  tff(c_3105, plain, (![B_512]: (k2_zfmisc_1('#skF_11', B_512)='#skF_11')), inference(resolution, [status(thm)], [c_2829, c_3027])).
% 6.05/2.31  tff(c_2489, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_1605])).
% 6.05/2.31  tff(c_2491, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_11' | k2_zfmisc_1('#skF_13', '#skF_14')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_2476, c_58])).
% 6.05/2.31  tff(c_2492, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_2489, c_2491])).
% 6.05/2.31  tff(c_3121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3105, c_2492])).
% 6.05/2.31  tff(c_3123, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_52])).
% 6.05/2.31  tff(c_3138, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_3123, c_24])).
% 6.05/2.31  tff(c_4050, plain, (![A_670, B_671, C_672]: (~r1_xboole_0(A_670, B_671) | ~r2_hidden(C_672, B_671) | ~r2_hidden(C_672, A_670))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.05/2.31  tff(c_4053, plain, (![C_672, A_15]: (~r2_hidden(C_672, '#skF_14') | ~r2_hidden(C_672, A_15))), inference(resolution, [status(thm)], [c_3138, c_4050])).
% 6.05/2.31  tff(c_4371, plain, (![B_746, A_747]: (~r2_hidden('#skF_3'('#skF_14', B_746), A_747) | r2_hidden('#skF_2'('#skF_14', B_746), B_746) | B_746='#skF_14')), inference(resolution, [status(thm)], [c_4110, c_4053])).
% 6.05/2.31  tff(c_4378, plain, (![B_7]: (r2_hidden('#skF_2'('#skF_14', B_7), B_7) | B_7='#skF_14')), inference(resolution, [status(thm)], [c_14, c_4371])).
% 6.05/2.31  tff(c_4278, plain, (![A_720, B_721, D_722]: (r2_hidden('#skF_10'(A_720, B_721, k2_zfmisc_1(A_720, B_721), D_722), B_721) | ~r2_hidden(D_722, k2_zfmisc_1(A_720, B_721)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_4573, plain, (![A_790, D_791, A_792]: (~r2_hidden('#skF_10'(A_790, '#skF_14', k2_zfmisc_1(A_790, '#skF_14'), D_791), A_792) | ~r2_hidden(D_791, k2_zfmisc_1(A_790, '#skF_14')))), inference(resolution, [status(thm)], [c_4278, c_4053])).
% 6.05/2.31  tff(c_4579, plain, (![D_793, A_794]: (~r2_hidden(D_793, k2_zfmisc_1(A_794, '#skF_14')))), inference(resolution, [status(thm)], [c_30, c_4573])).
% 6.05/2.31  tff(c_4657, plain, (![A_794]: (k2_zfmisc_1(A_794, '#skF_14')='#skF_14')), inference(resolution, [status(thm)], [c_4378, c_4579])).
% 6.05/2.31  tff(c_4578, plain, (![D_43, A_16]: (~r2_hidden(D_43, k2_zfmisc_1(A_16, '#skF_14')))), inference(resolution, [status(thm)], [c_30, c_4573])).
% 6.05/2.31  tff(c_4697, plain, (![D_796]: (~r2_hidden(D_796, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_4657, c_4578])).
% 6.05/2.31  tff(c_4789, plain, (![D_807, B_808]: (~r2_hidden(D_807, k2_zfmisc_1('#skF_14', B_808)))), inference(resolution, [status(thm)], [c_32, c_4697])).
% 6.05/2.31  tff(c_4870, plain, (![B_808]: (k2_zfmisc_1('#skF_14', B_808)='#skF_14')), inference(resolution, [status(thm)], [c_4378, c_4789])).
% 6.05/2.31  tff(c_3222, plain, (![A_537, B_538]: (r2_hidden('#skF_2'(A_537, B_538), B_538) | r2_hidden('#skF_3'(A_537, B_538), A_537) | B_538=A_537)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.05/2.31  tff(c_3122, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_52])).
% 6.05/2.31  tff(c_3146, plain, ('#skF_11'='#skF_14' | '#skF_14'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3123, c_3123, c_3122])).
% 6.05/2.31  tff(c_3147, plain, ('#skF_14'='#skF_12'), inference(splitLeft, [status(thm)], [c_3146])).
% 6.05/2.31  tff(c_3148, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3147, c_3138])).
% 6.05/2.31  tff(c_3177, plain, (![A_526, B_527, C_528]: (~r1_xboole_0(A_526, B_527) | ~r2_hidden(C_528, B_527) | ~r2_hidden(C_528, A_526))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.05/2.31  tff(c_3180, plain, (![C_528, A_15]: (~r2_hidden(C_528, '#skF_12') | ~r2_hidden(C_528, A_15))), inference(resolution, [status(thm)], [c_3148, c_3177])).
% 6.05/2.31  tff(c_3496, plain, (![B_600, A_601]: (~r2_hidden('#skF_3'('#skF_12', B_600), A_601) | r2_hidden('#skF_2'('#skF_12', B_600), B_600) | B_600='#skF_12')), inference(resolution, [status(thm)], [c_3222, c_3180])).
% 6.05/2.31  tff(c_3504, plain, (![B_7]: (r2_hidden('#skF_2'('#skF_12', B_7), B_7) | B_7='#skF_12')), inference(resolution, [status(thm)], [c_14, c_3496])).
% 6.05/2.31  tff(c_3482, plain, (![A_597, B_598, D_599]: (r2_hidden('#skF_9'(A_597, B_598, k2_zfmisc_1(A_597, B_598), D_599), A_597) | ~r2_hidden(D_599, k2_zfmisc_1(A_597, B_598)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_3693, plain, (![B_641, D_642, A_643]: (~r2_hidden('#skF_9'('#skF_12', B_641, k2_zfmisc_1('#skF_12', B_641), D_642), A_643) | ~r2_hidden(D_642, k2_zfmisc_1('#skF_12', B_641)))), inference(resolution, [status(thm)], [c_3482, c_3180])).
% 6.05/2.31  tff(c_3711, plain, (![D_647, B_648]: (~r2_hidden(D_647, k2_zfmisc_1('#skF_12', B_648)))), inference(resolution, [status(thm)], [c_32, c_3693])).
% 6.05/2.31  tff(c_3789, plain, (![B_648]: (k2_zfmisc_1('#skF_12', B_648)='#skF_12')), inference(resolution, [status(thm)], [c_3504, c_3711])).
% 6.05/2.31  tff(c_3698, plain, (![D_43, B_17]: (~r2_hidden(D_43, k2_zfmisc_1('#skF_12', B_17)))), inference(resolution, [status(thm)], [c_32, c_3693])).
% 6.05/2.31  tff(c_3829, plain, (![D_650]: (~r2_hidden(D_650, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3789, c_3698])).
% 6.05/2.31  tff(c_3920, plain, (![D_656, A_657]: (~r2_hidden(D_656, k2_zfmisc_1(A_657, '#skF_12')))), inference(resolution, [status(thm)], [c_30, c_3829])).
% 6.05/2.31  tff(c_4001, plain, (![A_657]: (k2_zfmisc_1(A_657, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_3504, c_3920])).
% 6.05/2.31  tff(c_3151, plain, (k1_xboole_0='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3147, c_3123])).
% 6.05/2.31  tff(c_50, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0 | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.05/2.31  tff(c_3124, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_50])).
% 6.05/2.31  tff(c_3133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3123, c_3124])).
% 6.05/2.31  tff(c_3134, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 6.05/2.31  tff(c_3164, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3151, c_3134])).
% 6.05/2.31  tff(c_4017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4001, c_3164])).
% 6.05/2.31  tff(c_4018, plain, ('#skF_11'='#skF_14'), inference(splitRight, [status(thm)], [c_3146])).
% 6.05/2.31  tff(c_4024, plain, (k2_zfmisc_1('#skF_14', '#skF_12')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_4018, c_3123, c_3134])).
% 6.05/2.31  tff(c_4886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4870, c_4024])).
% 6.05/2.31  tff(c_4888, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_54])).
% 6.05/2.31  tff(c_4890, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_4888, c_24])).
% 6.05/2.31  tff(c_4920, plain, (![A_820, B_821, C_822]: (~r1_xboole_0(A_820, B_821) | ~r2_hidden(C_822, B_821) | ~r2_hidden(C_822, A_820))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.05/2.31  tff(c_4923, plain, (![C_822, A_15]: (~r2_hidden(C_822, '#skF_13') | ~r2_hidden(C_822, A_15))), inference(resolution, [status(thm)], [c_4890, c_4920])).
% 6.05/2.31  tff(c_5250, plain, (![B_896, A_897]: (~r2_hidden('#skF_3'('#skF_13', B_896), A_897) | r2_hidden('#skF_2'('#skF_13', B_896), B_896) | B_896='#skF_13')), inference(resolution, [status(thm)], [c_5013, c_4923])).
% 6.05/2.31  tff(c_5258, plain, (![B_7]: (r2_hidden('#skF_2'('#skF_13', B_7), B_7) | B_7='#skF_13')), inference(resolution, [status(thm)], [c_14, c_5250])).
% 6.05/2.31  tff(c_5184, plain, (![A_879, B_880, D_881]: (r2_hidden('#skF_10'(A_879, B_880, k2_zfmisc_1(A_879, B_880), D_881), B_880) | ~r2_hidden(D_881, k2_zfmisc_1(A_879, B_880)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_5401, plain, (![A_921, D_922, A_923]: (~r2_hidden('#skF_10'(A_921, '#skF_13', k2_zfmisc_1(A_921, '#skF_13'), D_922), A_923) | ~r2_hidden(D_922, k2_zfmisc_1(A_921, '#skF_13')))), inference(resolution, [status(thm)], [c_5184, c_4923])).
% 6.05/2.31  tff(c_5407, plain, (![D_924, A_925]: (~r2_hidden(D_924, k2_zfmisc_1(A_925, '#skF_13')))), inference(resolution, [status(thm)], [c_30, c_5401])).
% 6.05/2.31  tff(c_5485, plain, (![A_925]: (k2_zfmisc_1(A_925, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_5258, c_5407])).
% 6.05/2.31  tff(c_5406, plain, (![D_43, A_16]: (~r2_hidden(D_43, k2_zfmisc_1(A_16, '#skF_13')))), inference(resolution, [status(thm)], [c_30, c_5401])).
% 6.05/2.31  tff(c_5526, plain, (![D_932]: (~r2_hidden(D_932, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_5485, c_5406])).
% 6.05/2.31  tff(c_5612, plain, (![D_933, B_934]: (~r2_hidden(D_933, k2_zfmisc_1('#skF_13', B_934)))), inference(resolution, [status(thm)], [c_32, c_5526])).
% 6.05/2.31  tff(c_5693, plain, (![B_934]: (k2_zfmisc_1('#skF_13', B_934)='#skF_13')), inference(resolution, [status(thm)], [c_5258, c_5612])).
% 6.05/2.31  tff(c_56, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.05/2.31  tff(c_4899, plain, ('#skF_13'='#skF_12' | '#skF_11'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4888, c_4888, c_4888, c_56])).
% 6.05/2.31  tff(c_4900, plain, ('#skF_11'='#skF_13'), inference(splitLeft, [status(thm)], [c_4899])).
% 6.05/2.31  tff(c_4887, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 6.05/2.31  tff(c_4897, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4888, c_4887])).
% 6.05/2.31  tff(c_4901, plain, (k2_zfmisc_1('#skF_13', '#skF_12')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4900, c_4897])).
% 6.05/2.31  tff(c_5721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5693, c_4901])).
% 6.05/2.31  tff(c_5722, plain, ('#skF_13'='#skF_12'), inference(splitRight, [status(thm)], [c_4899])).
% 6.05/2.31  tff(c_5725, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_5722, c_4890])).
% 6.05/2.31  tff(c_5766, plain, (![A_952, B_953, C_954]: (~r1_xboole_0(A_952, B_953) | ~r2_hidden(C_954, B_953) | ~r2_hidden(C_954, A_952))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.05/2.31  tff(c_5769, plain, (![C_954, A_15]: (~r2_hidden(C_954, '#skF_12') | ~r2_hidden(C_954, A_15))), inference(resolution, [status(thm)], [c_5725, c_5766])).
% 6.05/2.31  tff(c_6076, plain, (![B_1026, A_1027]: (~r2_hidden('#skF_3'('#skF_12', B_1026), A_1027) | r2_hidden('#skF_2'('#skF_12', B_1026), B_1026) | B_1026='#skF_12')), inference(resolution, [status(thm)], [c_5849, c_5769])).
% 6.05/2.31  tff(c_6083, plain, (![B_7]: (r2_hidden('#skF_2'('#skF_12', B_7), B_7) | B_7='#skF_12')), inference(resolution, [status(thm)], [c_14, c_6076])).
% 6.05/2.31  tff(c_6025, plain, (![A_1008, B_1009, D_1010]: (r2_hidden('#skF_9'(A_1008, B_1009, k2_zfmisc_1(A_1008, B_1009), D_1010), A_1008) | ~r2_hidden(D_1010, k2_zfmisc_1(A_1008, B_1009)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.05/2.31  tff(c_6252, plain, (![B_1063, D_1064, A_1065]: (~r2_hidden('#skF_9'('#skF_12', B_1063, k2_zfmisc_1('#skF_12', B_1063), D_1064), A_1065) | ~r2_hidden(D_1064, k2_zfmisc_1('#skF_12', B_1063)))), inference(resolution, [status(thm)], [c_6025, c_5769])).
% 6.05/2.31  tff(c_6258, plain, (![D_1066, B_1067]: (~r2_hidden(D_1066, k2_zfmisc_1('#skF_12', B_1067)))), inference(resolution, [status(thm)], [c_32, c_6252])).
% 6.05/2.31  tff(c_6336, plain, (![B_1067]: (k2_zfmisc_1('#skF_12', B_1067)='#skF_12')), inference(resolution, [status(thm)], [c_6083, c_6258])).
% 6.05/2.31  tff(c_6257, plain, (![D_43, B_17]: (~r2_hidden(D_43, k2_zfmisc_1('#skF_12', B_17)))), inference(resolution, [status(thm)], [c_32, c_6252])).
% 6.05/2.31  tff(c_6379, plain, (![D_1074]: (~r2_hidden(D_1074, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_6336, c_6257])).
% 6.05/2.31  tff(c_6468, plain, (![D_1080, A_1081]: (~r2_hidden(D_1080, k2_zfmisc_1(A_1081, '#skF_12')))), inference(resolution, [status(thm)], [c_30, c_6379])).
% 6.05/2.31  tff(c_6549, plain, (![A_1081]: (k2_zfmisc_1(A_1081, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_6083, c_6468])).
% 6.05/2.31  tff(c_5724, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5722, c_4897])).
% 6.05/2.31  tff(c_6565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6549, c_5724])).
% 6.05/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.31  
% 6.05/2.31  Inference rules
% 6.05/2.31  ----------------------
% 6.05/2.31  #Ref     : 0
% 6.05/2.31  #Sup     : 1449
% 6.05/2.31  #Fact    : 0
% 6.05/2.31  #Define  : 0
% 6.05/2.31  #Split   : 12
% 6.05/2.31  #Chain   : 0
% 6.05/2.31  #Close   : 0
% 6.05/2.31  
% 6.05/2.31  Ordering : KBO
% 6.05/2.31  
% 6.05/2.31  Simplification rules
% 6.05/2.31  ----------------------
% 6.05/2.31  #Subsume      : 430
% 6.05/2.31  #Demod        : 274
% 6.05/2.31  #Tautology    : 220
% 6.05/2.31  #SimpNegUnit  : 10
% 6.05/2.31  #BackRed      : 44
% 6.05/2.31  
% 6.05/2.31  #Partial instantiations: 0
% 6.05/2.31  #Strategies tried      : 1
% 6.05/2.31  
% 6.05/2.31  Timing (in seconds)
% 6.05/2.31  ----------------------
% 6.05/2.32  Preprocessing        : 0.38
% 6.05/2.32  Parsing              : 0.18
% 6.05/2.32  CNF conversion       : 0.03
% 6.05/2.32  Main loop            : 1.05
% 6.05/2.32  Inferencing          : 0.41
% 6.05/2.32  Reduction            : 0.27
% 6.05/2.32  Demodulation         : 0.17
% 6.05/2.32  BG Simplification    : 0.05
% 6.05/2.32  Subsumption          : 0.22
% 6.05/2.32  Abstraction          : 0.05
% 6.05/2.32  MUC search           : 0.00
% 6.05/2.32  Cooper               : 0.00
% 6.05/2.32  Total                : 1.49
% 6.05/2.32  Index Insertion      : 0.00
% 6.05/2.32  Index Deletion       : 0.00
% 6.05/2.32  Index Matching       : 0.00
% 6.05/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
