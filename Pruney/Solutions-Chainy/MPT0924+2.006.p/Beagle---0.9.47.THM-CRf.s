%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:22 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 557 expanded)
%              Number of leaves         :   32 ( 188 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 (1212 expanded)
%              Number of equality atoms :    9 ( 124 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_15 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_5 > #skF_6 > #skF_13 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( r2_hidden(k4_mcart_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
      <=> ( r2_hidden(A,E)
          & r2_hidden(B,F)
          & r2_hidden(C,G)
          & r2_hidden(D,H) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_22,plain,
    ( r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_330,plain,(
    ~ r2_hidden('#skF_9','#skF_13') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_30,plain,
    ( r2_hidden('#skF_3','#skF_7')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_151,plain,(
    r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] : k4_tarski(k3_mcart_1(A_11,B_12,C_13),D_14) = k4_mcart_1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_37,B_38,C_39,D_40] : k2_zfmisc_1(k3_zfmisc_1(A_37,B_38,C_39),D_40) = k4_zfmisc_1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_391,plain,(
    ! [B_137,C_136,A_133,A_138,D_135,B_134] :
      ( r2_hidden(A_138,k3_zfmisc_1(A_133,B_134,C_136))
      | ~ r2_hidden(k4_tarski(A_138,B_137),k4_zfmisc_1(A_133,B_134,C_136,D_135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_6])).

tff(c_656,plain,(
    ! [B_209,A_206,D_210,D_211,C_205,C_212,A_208,B_207] :
      ( r2_hidden(k3_mcart_1(A_208,B_209,C_205),k3_zfmisc_1(A_206,B_207,C_212))
      | ~ r2_hidden(k4_mcart_1(A_208,B_209,C_205,D_211),k4_zfmisc_1(A_206,B_207,C_212,D_210)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_391])).

tff(c_676,plain,(
    r2_hidden(k3_mcart_1('#skF_9','#skF_10','#skF_11'),k3_zfmisc_1('#skF_13','#skF_14','#skF_15')) ),
    inference(resolution,[status(thm)],[c_151,c_656])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [A_29,C_30,B_31,D_32] :
      ( r2_hidden(A_29,C_30)
      | ~ r2_hidden(k4_tarski(A_29,B_31),k2_zfmisc_1(C_30,D_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_230,plain,(
    ! [C_89,B_88,D_86,C_87,A_90] :
      ( r2_hidden(k4_tarski(A_90,B_88),C_87)
      | ~ r2_hidden(k3_mcart_1(A_90,B_88,C_89),k2_zfmisc_1(C_87,D_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_239,plain,(
    ! [C_89,A_8,B_88,C_10,B_9,A_90] :
      ( r2_hidden(k4_tarski(A_90,B_88),k2_zfmisc_1(A_8,B_9))
      | ~ r2_hidden(k3_mcart_1(A_90,B_88,C_89),k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_230])).

tff(c_683,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_676,c_239])).

tff(c_687,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(resolution,[status(thm)],[c_683,c_6])).

tff(c_694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_687])).

tff(c_696,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [B_66,A_65,D_67,A_70,C_68,B_69] :
      ( r2_hidden(B_69,D_67)
      | ~ r2_hidden(k4_tarski(A_70,B_69),k4_zfmisc_1(A_65,B_66,C_68,D_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_4])).

tff(c_325,plain,(
    ! [B_118,D_115,A_117,B_119,C_122,D_121,A_120,C_116] :
      ( r2_hidden(D_121,D_115)
      | ~ r2_hidden(k4_mcart_1(A_117,B_118,C_116,D_121),k4_zfmisc_1(A_120,B_119,C_122,D_115)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_181])).

tff(c_329,plain,(
    r2_hidden('#skF_12','#skF_16') ),
    inference(resolution,[status(thm)],[c_151,c_325])).

tff(c_695,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_12','#skF_16')
    | r2_hidden('#skF_2','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_704,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_11','#skF_15')
    | r2_hidden('#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_695])).

tff(c_705,plain,(
    ~ r2_hidden('#skF_11','#skF_15') ),
    inference(splitLeft,[status(thm)],[c_704])).

tff(c_776,plain,(
    ! [D_231,A_229,A_234,B_233,C_232,B_230] :
      ( r2_hidden(A_234,k3_zfmisc_1(A_229,B_230,C_232))
      | ~ r2_hidden(k4_tarski(A_234,B_233),k4_zfmisc_1(A_229,B_230,C_232,D_231)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_6])).

tff(c_1030,plain,(
    ! [B_301,C_296,C_297,D_299,A_300,A_298,D_302,B_295] :
      ( r2_hidden(k3_mcart_1(A_300,B_301,C_297),k3_zfmisc_1(A_298,B_295,C_296))
      | ~ r2_hidden(k4_mcart_1(A_300,B_301,C_297,D_302),k4_zfmisc_1(A_298,B_295,C_296,D_299)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_776])).

tff(c_1050,plain,(
    r2_hidden(k3_mcart_1('#skF_9','#skF_10','#skF_11'),k3_zfmisc_1('#skF_13','#skF_14','#skF_15')) ),
    inference(resolution,[status(thm)],[c_151,c_1030])).

tff(c_65,plain,(
    ! [B_25,D_26,A_27,C_28] :
      ( r2_hidden(B_25,D_26)
      | ~ r2_hidden(k4_tarski(A_27,B_25),k2_zfmisc_1(C_28,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [B_47,C_48,C_50,D_46,A_49] :
      ( r2_hidden(C_48,D_46)
      | ~ r2_hidden(k3_mcart_1(A_49,B_47,C_48),k2_zfmisc_1(C_50,D_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_128,plain,(
    ! [A_8,B_47,C_48,C_10,B_9,A_49] :
      ( r2_hidden(C_48,C_10)
      | ~ r2_hidden(k3_mcart_1(A_49,B_47,C_48),k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_122])).

tff(c_1056,plain,(
    r2_hidden('#skF_11','#skF_15') ),
    inference(resolution,[status(thm)],[c_1050,c_128])).

tff(c_1061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_705,c_1056])).

tff(c_1063,plain,(
    r2_hidden('#skF_11','#skF_15') ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_24,plain,
    ( r2_hidden('#skF_1','#skF_5')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1072,plain,
    ( r2_hidden('#skF_1','#skF_5')
    | ~ r2_hidden('#skF_10','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_1063,c_329,c_24])).

tff(c_1073,plain,(
    ~ r2_hidden('#skF_10','#skF_14') ),
    inference(splitLeft,[status(thm)],[c_1072])).

tff(c_1132,plain,(
    ! [A_318,B_317,C_316,D_315,B_314,A_313] :
      ( r2_hidden(A_318,k3_zfmisc_1(A_313,B_314,C_316))
      | ~ r2_hidden(k4_tarski(A_318,B_317),k4_zfmisc_1(A_313,B_314,C_316,D_315)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_6])).

tff(c_1396,plain,(
    ! [D_390,B_389,A_392,B_391,A_387,D_386,C_385,C_388] :
      ( r2_hidden(k3_mcart_1(A_387,B_389,C_385),k3_zfmisc_1(A_392,B_391,C_388))
      | ~ r2_hidden(k4_mcart_1(A_387,B_389,C_385,D_390),k4_zfmisc_1(A_392,B_391,C_388,D_386)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1132])).

tff(c_1416,plain,(
    r2_hidden(k3_mcart_1('#skF_9','#skF_10','#skF_11'),k3_zfmisc_1('#skF_13','#skF_14','#skF_15')) ),
    inference(resolution,[status(thm)],[c_151,c_1396])).

tff(c_219,plain,(
    ! [C_85,A_82,B_81,B_84,A_83] :
      ( r2_hidden(A_83,k2_zfmisc_1(A_82,B_84))
      | ~ r2_hidden(k4_tarski(A_83,B_81),k3_zfmisc_1(A_82,B_84,C_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_228,plain,(
    ! [B_6,C_85,C_7,A_82,B_84,A_5] :
      ( r2_hidden(k4_tarski(A_5,B_6),k2_zfmisc_1(A_82,B_84))
      | ~ r2_hidden(k3_mcart_1(A_5,B_6,C_7),k3_zfmisc_1(A_82,B_84,C_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_219])).

tff(c_1423,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_1416,c_228])).

tff(c_1431,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(resolution,[status(thm)],[c_1423,c_4])).

tff(c_1437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1073,c_1431])).

tff(c_1438,plain,(
    r2_hidden('#skF_1','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1072])).

tff(c_1439,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(splitRight,[status(thm)],[c_1072])).

tff(c_1062,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | r2_hidden('#skF_2','#skF_6') ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_1446,plain,(
    r2_hidden('#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1062])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,
    ( r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_697,plain,(
    ~ r2_hidden('#skF_9','#skF_13') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_697])).

tff(c_700,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_12','#skF_16')
    | r2_hidden('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1065,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_11','#skF_15')
    | r2_hidden('#skF_3','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_700])).

tff(c_1066,plain,(
    ~ r2_hidden('#skF_11','#skF_15') ),
    inference(splitLeft,[status(thm)],[c_1065])).

tff(c_1068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1066])).

tff(c_1069,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | r2_hidden('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1065])).

tff(c_1442,plain,(
    r2_hidden('#skF_3','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1069])).

tff(c_189,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( r2_hidden(k4_tarski(A_71,B_72),k2_zfmisc_1(C_73,D_74))
      | ~ r2_hidden(B_72,D_74)
      | ~ r2_hidden(A_71,C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1526,plain,(
    ! [D_416,B_415,C_419,C_417,A_418] :
      ( r2_hidden(k3_mcart_1(A_418,B_415,C_417),k2_zfmisc_1(C_419,D_416))
      | ~ r2_hidden(C_417,D_416)
      | ~ r2_hidden(k4_tarski(A_418,B_415),C_419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_189])).

tff(c_1544,plain,(
    ! [B_415,A_8,C_417,C_10,A_418,B_9] :
      ( r2_hidden(k3_mcart_1(A_418,B_415,C_417),k3_zfmisc_1(A_8,B_9,C_10))
      | ~ r2_hidden(C_417,C_10)
      | ~ r2_hidden(k4_tarski(A_418,B_415),k2_zfmisc_1(A_8,B_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1526])).

tff(c_18,plain,
    ( r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1444,plain,(
    r2_hidden('#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_1439,c_1063,c_329,c_18])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_zfmisc_1(k3_zfmisc_1(A_15,B_16,C_17),D_18) = k4_zfmisc_1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1649,plain,(
    ! [C_443,D_444,A_448,B_445,B_447,A_446] :
      ( r2_hidden(k4_tarski(A_446,B_447),k4_zfmisc_1(A_448,B_445,C_443,D_444))
      | ~ r2_hidden(B_447,D_444)
      | ~ r2_hidden(A_446,k3_zfmisc_1(A_448,B_445,C_443)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_189])).

tff(c_1856,plain,(
    ! [B_501,C_497,C_498,D_503,A_504,A_500,D_499,B_502] :
      ( r2_hidden(k4_mcart_1(A_500,B_502,C_497,D_503),k4_zfmisc_1(A_504,B_501,C_498,D_499))
      | ~ r2_hidden(D_503,D_499)
      | ~ r2_hidden(k3_mcart_1(A_500,B_502,C_497),k3_zfmisc_1(A_504,B_501,C_498)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1649])).

tff(c_16,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1503,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_1439,c_1063,c_329,c_16])).

tff(c_1862,plain,
    ( ~ r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1856,c_1503])).

tff(c_1881,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1862])).

tff(c_1889,plain,
    ( ~ r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1544,c_1881])).

tff(c_1892,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_1889])).

tff(c_1895,plain,
    ( ~ r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_1892])).

tff(c_1899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_1446,c_1895])).

tff(c_1901,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( r2_hidden('#skF_1','#skF_5')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1991,plain,(
    r2_hidden('#skF_1','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1901,c_34])).

tff(c_32,plain,
    ( r2_hidden('#skF_2','#skF_6')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1931,plain,(
    r2_hidden('#skF_2','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1901,c_32])).

tff(c_1900,plain,(
    r2_hidden('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1948,plain,(
    ! [A_527,B_528,C_529,D_530] :
      ( r2_hidden(k4_tarski(A_527,B_528),k2_zfmisc_1(C_529,D_530))
      | ~ r2_hidden(B_528,D_530)
      | ~ r2_hidden(A_527,C_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2156,plain,(
    ! [A_599,C_598,C_596,D_595,B_597] :
      ( r2_hidden(k3_mcart_1(A_599,B_597,C_598),k2_zfmisc_1(C_596,D_595))
      | ~ r2_hidden(C_598,D_595)
      | ~ r2_hidden(k4_tarski(A_599,B_597),C_596) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1948])).

tff(c_2174,plain,(
    ! [A_599,A_8,C_598,C_10,B_9,B_597] :
      ( r2_hidden(k3_mcart_1(A_599,B_597,C_598),k3_zfmisc_1(A_8,B_9,C_10))
      | ~ r2_hidden(C_598,C_10)
      | ~ r2_hidden(k4_tarski(A_599,B_597),k2_zfmisc_1(A_8,B_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2156])).

tff(c_28,plain,
    ( r2_hidden('#skF_4','#skF_8')
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2000,plain,(
    r2_hidden('#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1901,c_28])).

tff(c_2307,plain,(
    ! [C_630,D_634,B_633,C_631,D_629,A_632] :
      ( r2_hidden(k4_mcart_1(A_632,B_633,C_631,D_634),k2_zfmisc_1(C_630,D_629))
      | ~ r2_hidden(D_634,D_629)
      | ~ r2_hidden(k3_mcart_1(A_632,B_633,C_631),C_630) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1948])).

tff(c_2463,plain,(
    ! [B_681,D_678,C_677,B_680,A_683,C_682,D_679,A_684] :
      ( r2_hidden(k4_mcart_1(A_683,B_680,C_682,D_679),k4_zfmisc_1(A_684,B_681,C_677,D_678))
      | ~ r2_hidden(D_679,D_678)
      | ~ r2_hidden(k3_mcart_1(A_683,B_680,C_682),k3_zfmisc_1(A_684,B_681,C_677)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2307])).

tff(c_26,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2155,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1901,c_26])).

tff(c_2469,plain,
    ( ~ r2_hidden('#skF_4','#skF_8')
    | ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2463,c_2155])).

tff(c_2491,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_2469])).

tff(c_2500,plain,
    ( ~ r2_hidden('#skF_3','#skF_7')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2174,c_2491])).

tff(c_2503,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1900,c_2500])).

tff(c_2506,plain,
    ( ~ r2_hidden('#skF_2','#skF_6')
    | ~ r2_hidden('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_2503])).

tff(c_2510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1991,c_1931,c_2506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.83  
% 4.62/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.84  %$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_15 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_5 > #skF_6 > #skF_13 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12
% 4.62/1.84  
% 4.62/1.84  %Foreground sorts:
% 4.62/1.84  
% 4.62/1.84  
% 4.62/1.84  %Background operators:
% 4.62/1.84  
% 4.62/1.84  
% 4.62/1.84  %Foreground operators:
% 4.62/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.84  tff('#skF_11', type, '#skF_11': $i).
% 4.62/1.84  tff('#skF_15', type, '#skF_15': $i).
% 4.62/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.62/1.84  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.62/1.84  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.62/1.84  tff('#skF_7', type, '#skF_7': $i).
% 4.62/1.84  tff('#skF_10', type, '#skF_10': $i).
% 4.62/1.84  tff('#skF_16', type, '#skF_16': $i).
% 4.62/1.84  tff('#skF_14', type, '#skF_14': $i).
% 4.62/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.84  tff('#skF_13', type, '#skF_13': $i).
% 4.62/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.62/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.62/1.84  tff('#skF_9', type, '#skF_9': $i).
% 4.62/1.84  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.62/1.84  tff('#skF_8', type, '#skF_8': $i).
% 4.62/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.62/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.84  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.62/1.84  tff('#skF_12', type, '#skF_12': $i).
% 4.62/1.84  
% 4.62/1.87  tff(f_50, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (r2_hidden(k4_mcart_1(A, B, C, D), k4_zfmisc_1(E, F, G, H)) <=> (((r2_hidden(A, E) & r2_hidden(B, F)) & r2_hidden(C, G)) & r2_hidden(D, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_mcart_1)).
% 4.62/1.87  tff(f_37, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 4.62/1.87  tff(f_39, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 4.62/1.87  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.62/1.87  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.62/1.87  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.62/1.87  tff(c_22, plain, (r2_hidden('#skF_2', '#skF_6') | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_330, plain, (~r2_hidden('#skF_9', '#skF_13')), inference(splitLeft, [status(thm)], [c_22])).
% 4.62/1.87  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_7') | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_151, plain, (r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(splitLeft, [status(thm)], [c_30])).
% 4.62/1.87  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k4_tarski(k3_mcart_1(A_11, B_12, C_13), D_14)=k4_mcart_1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.62/1.87  tff(c_97, plain, (![A_37, B_38, C_39, D_40]: (k2_zfmisc_1(k3_zfmisc_1(A_37, B_38, C_39), D_40)=k4_zfmisc_1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.87  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.87  tff(c_391, plain, (![B_137, C_136, A_133, A_138, D_135, B_134]: (r2_hidden(A_138, k3_zfmisc_1(A_133, B_134, C_136)) | ~r2_hidden(k4_tarski(A_138, B_137), k4_zfmisc_1(A_133, B_134, C_136, D_135)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_6])).
% 4.62/1.87  tff(c_656, plain, (![B_209, A_206, D_210, D_211, C_205, C_212, A_208, B_207]: (r2_hidden(k3_mcart_1(A_208, B_209, C_205), k3_zfmisc_1(A_206, B_207, C_212)) | ~r2_hidden(k4_mcart_1(A_208, B_209, C_205, D_211), k4_zfmisc_1(A_206, B_207, C_212, D_210)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_391])).
% 4.62/1.87  tff(c_676, plain, (r2_hidden(k3_mcart_1('#skF_9', '#skF_10', '#skF_11'), k3_zfmisc_1('#skF_13', '#skF_14', '#skF_15'))), inference(resolution, [status(thm)], [c_151, c_656])).
% 4.62/1.87  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.62/1.87  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.62/1.87  tff(c_72, plain, (![A_29, C_30, B_31, D_32]: (r2_hidden(A_29, C_30) | ~r2_hidden(k4_tarski(A_29, B_31), k2_zfmisc_1(C_30, D_32)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.87  tff(c_230, plain, (![C_89, B_88, D_86, C_87, A_90]: (r2_hidden(k4_tarski(A_90, B_88), C_87) | ~r2_hidden(k3_mcart_1(A_90, B_88, C_89), k2_zfmisc_1(C_87, D_86)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 4.62/1.87  tff(c_239, plain, (![C_89, A_8, B_88, C_10, B_9, A_90]: (r2_hidden(k4_tarski(A_90, B_88), k2_zfmisc_1(A_8, B_9)) | ~r2_hidden(k3_mcart_1(A_90, B_88, C_89), k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_230])).
% 4.62/1.87  tff(c_683, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_676, c_239])).
% 4.62/1.87  tff(c_687, plain, (r2_hidden('#skF_9', '#skF_13')), inference(resolution, [status(thm)], [c_683, c_6])).
% 4.62/1.87  tff(c_694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_687])).
% 4.62/1.87  tff(c_696, plain, (r2_hidden('#skF_9', '#skF_13')), inference(splitRight, [status(thm)], [c_22])).
% 4.62/1.87  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.87  tff(c_181, plain, (![B_66, A_65, D_67, A_70, C_68, B_69]: (r2_hidden(B_69, D_67) | ~r2_hidden(k4_tarski(A_70, B_69), k4_zfmisc_1(A_65, B_66, C_68, D_67)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_4])).
% 4.62/1.87  tff(c_325, plain, (![B_118, D_115, A_117, B_119, C_122, D_121, A_120, C_116]: (r2_hidden(D_121, D_115) | ~r2_hidden(k4_mcart_1(A_117, B_118, C_116, D_121), k4_zfmisc_1(A_120, B_119, C_122, D_115)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_181])).
% 4.62/1.87  tff(c_329, plain, (r2_hidden('#skF_12', '#skF_16')), inference(resolution, [status(thm)], [c_151, c_325])).
% 4.62/1.87  tff(c_695, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_12', '#skF_16') | r2_hidden('#skF_2', '#skF_6')), inference(splitRight, [status(thm)], [c_22])).
% 4.62/1.87  tff(c_704, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_11', '#skF_15') | r2_hidden('#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_695])).
% 4.62/1.87  tff(c_705, plain, (~r2_hidden('#skF_11', '#skF_15')), inference(splitLeft, [status(thm)], [c_704])).
% 4.62/1.87  tff(c_776, plain, (![D_231, A_229, A_234, B_233, C_232, B_230]: (r2_hidden(A_234, k3_zfmisc_1(A_229, B_230, C_232)) | ~r2_hidden(k4_tarski(A_234, B_233), k4_zfmisc_1(A_229, B_230, C_232, D_231)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_6])).
% 4.62/1.87  tff(c_1030, plain, (![B_301, C_296, C_297, D_299, A_300, A_298, D_302, B_295]: (r2_hidden(k3_mcart_1(A_300, B_301, C_297), k3_zfmisc_1(A_298, B_295, C_296)) | ~r2_hidden(k4_mcart_1(A_300, B_301, C_297, D_302), k4_zfmisc_1(A_298, B_295, C_296, D_299)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_776])).
% 4.62/1.87  tff(c_1050, plain, (r2_hidden(k3_mcart_1('#skF_9', '#skF_10', '#skF_11'), k3_zfmisc_1('#skF_13', '#skF_14', '#skF_15'))), inference(resolution, [status(thm)], [c_151, c_1030])).
% 4.62/1.87  tff(c_65, plain, (![B_25, D_26, A_27, C_28]: (r2_hidden(B_25, D_26) | ~r2_hidden(k4_tarski(A_27, B_25), k2_zfmisc_1(C_28, D_26)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.87  tff(c_122, plain, (![B_47, C_48, C_50, D_46, A_49]: (r2_hidden(C_48, D_46) | ~r2_hidden(k3_mcart_1(A_49, B_47, C_48), k2_zfmisc_1(C_50, D_46)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 4.62/1.87  tff(c_128, plain, (![A_8, B_47, C_48, C_10, B_9, A_49]: (r2_hidden(C_48, C_10) | ~r2_hidden(k3_mcart_1(A_49, B_47, C_48), k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_122])).
% 4.62/1.87  tff(c_1056, plain, (r2_hidden('#skF_11', '#skF_15')), inference(resolution, [status(thm)], [c_1050, c_128])).
% 4.62/1.87  tff(c_1061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_705, c_1056])).
% 4.62/1.87  tff(c_1063, plain, (r2_hidden('#skF_11', '#skF_15')), inference(splitRight, [status(thm)], [c_704])).
% 4.62/1.87  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_5') | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_1072, plain, (r2_hidden('#skF_1', '#skF_5') | ~r2_hidden('#skF_10', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_696, c_1063, c_329, c_24])).
% 4.62/1.87  tff(c_1073, plain, (~r2_hidden('#skF_10', '#skF_14')), inference(splitLeft, [status(thm)], [c_1072])).
% 4.62/1.87  tff(c_1132, plain, (![A_318, B_317, C_316, D_315, B_314, A_313]: (r2_hidden(A_318, k3_zfmisc_1(A_313, B_314, C_316)) | ~r2_hidden(k4_tarski(A_318, B_317), k4_zfmisc_1(A_313, B_314, C_316, D_315)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_6])).
% 4.62/1.87  tff(c_1396, plain, (![D_390, B_389, A_392, B_391, A_387, D_386, C_385, C_388]: (r2_hidden(k3_mcart_1(A_387, B_389, C_385), k3_zfmisc_1(A_392, B_391, C_388)) | ~r2_hidden(k4_mcart_1(A_387, B_389, C_385, D_390), k4_zfmisc_1(A_392, B_391, C_388, D_386)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1132])).
% 4.62/1.87  tff(c_1416, plain, (r2_hidden(k3_mcart_1('#skF_9', '#skF_10', '#skF_11'), k3_zfmisc_1('#skF_13', '#skF_14', '#skF_15'))), inference(resolution, [status(thm)], [c_151, c_1396])).
% 4.62/1.87  tff(c_219, plain, (![C_85, A_82, B_81, B_84, A_83]: (r2_hidden(A_83, k2_zfmisc_1(A_82, B_84)) | ~r2_hidden(k4_tarski(A_83, B_81), k3_zfmisc_1(A_82, B_84, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_72])).
% 4.62/1.87  tff(c_228, plain, (![B_6, C_85, C_7, A_82, B_84, A_5]: (r2_hidden(k4_tarski(A_5, B_6), k2_zfmisc_1(A_82, B_84)) | ~r2_hidden(k3_mcart_1(A_5, B_6, C_7), k3_zfmisc_1(A_82, B_84, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_219])).
% 4.62/1.87  tff(c_1423, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_1416, c_228])).
% 4.62/1.87  tff(c_1431, plain, (r2_hidden('#skF_10', '#skF_14')), inference(resolution, [status(thm)], [c_1423, c_4])).
% 4.62/1.87  tff(c_1437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1073, c_1431])).
% 4.62/1.87  tff(c_1438, plain, (r2_hidden('#skF_1', '#skF_5')), inference(splitRight, [status(thm)], [c_1072])).
% 4.62/1.87  tff(c_1439, plain, (r2_hidden('#skF_10', '#skF_14')), inference(splitRight, [status(thm)], [c_1072])).
% 4.62/1.87  tff(c_1062, plain, (~r2_hidden('#skF_10', '#skF_14') | r2_hidden('#skF_2', '#skF_6')), inference(splitRight, [status(thm)], [c_704])).
% 4.62/1.87  tff(c_1446, plain, (r2_hidden('#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1062])).
% 4.62/1.87  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)) | ~r2_hidden(B_2, D_4) | ~r2_hidden(A_1, C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.87  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_7') | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_697, plain, (~r2_hidden('#skF_9', '#skF_13')), inference(splitLeft, [status(thm)], [c_20])).
% 4.62/1.87  tff(c_699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_696, c_697])).
% 4.62/1.87  tff(c_700, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_12', '#skF_16') | r2_hidden('#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_20])).
% 4.62/1.87  tff(c_1065, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_11', '#skF_15') | r2_hidden('#skF_3', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_700])).
% 4.62/1.87  tff(c_1066, plain, (~r2_hidden('#skF_11', '#skF_15')), inference(splitLeft, [status(thm)], [c_1065])).
% 4.62/1.87  tff(c_1068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1066])).
% 4.62/1.87  tff(c_1069, plain, (~r2_hidden('#skF_10', '#skF_14') | r2_hidden('#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_1065])).
% 4.62/1.87  tff(c_1442, plain, (r2_hidden('#skF_3', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1069])).
% 4.62/1.87  tff(c_189, plain, (![A_71, B_72, C_73, D_74]: (r2_hidden(k4_tarski(A_71, B_72), k2_zfmisc_1(C_73, D_74)) | ~r2_hidden(B_72, D_74) | ~r2_hidden(A_71, C_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.87  tff(c_1526, plain, (![D_416, B_415, C_419, C_417, A_418]: (r2_hidden(k3_mcart_1(A_418, B_415, C_417), k2_zfmisc_1(C_419, D_416)) | ~r2_hidden(C_417, D_416) | ~r2_hidden(k4_tarski(A_418, B_415), C_419))), inference(superposition, [status(thm), theory('equality')], [c_8, c_189])).
% 4.62/1.87  tff(c_1544, plain, (![B_415, A_8, C_417, C_10, A_418, B_9]: (r2_hidden(k3_mcart_1(A_418, B_415, C_417), k3_zfmisc_1(A_8, B_9, C_10)) | ~r2_hidden(C_417, C_10) | ~r2_hidden(k4_tarski(A_418, B_415), k2_zfmisc_1(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1526])).
% 4.62/1.87  tff(c_18, plain, (r2_hidden('#skF_4', '#skF_8') | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_1444, plain, (r2_hidden('#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_696, c_1439, c_1063, c_329, c_18])).
% 4.62/1.87  tff(c_14, plain, (![A_15, B_16, C_17, D_18]: (k2_zfmisc_1(k3_zfmisc_1(A_15, B_16, C_17), D_18)=k4_zfmisc_1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.87  tff(c_1649, plain, (![C_443, D_444, A_448, B_445, B_447, A_446]: (r2_hidden(k4_tarski(A_446, B_447), k4_zfmisc_1(A_448, B_445, C_443, D_444)) | ~r2_hidden(B_447, D_444) | ~r2_hidden(A_446, k3_zfmisc_1(A_448, B_445, C_443)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_189])).
% 4.62/1.87  tff(c_1856, plain, (![B_501, C_497, C_498, D_503, A_504, A_500, D_499, B_502]: (r2_hidden(k4_mcart_1(A_500, B_502, C_497, D_503), k4_zfmisc_1(A_504, B_501, C_498, D_499)) | ~r2_hidden(D_503, D_499) | ~r2_hidden(k3_mcart_1(A_500, B_502, C_497), k3_zfmisc_1(A_504, B_501, C_498)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1649])).
% 4.62/1.87  tff(c_16, plain, (~r2_hidden(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_1503, plain, (~r2_hidden(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_1439, c_1063, c_329, c_16])).
% 4.62/1.87  tff(c_1862, plain, (~r2_hidden('#skF_4', '#skF_8') | ~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1856, c_1503])).
% 4.62/1.87  tff(c_1881, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1862])).
% 4.62/1.87  tff(c_1889, plain, (~r2_hidden('#skF_3', '#skF_7') | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1544, c_1881])).
% 4.62/1.87  tff(c_1892, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_1889])).
% 4.62/1.87  tff(c_1895, plain, (~r2_hidden('#skF_2', '#skF_6') | ~r2_hidden('#skF_1', '#skF_5')), inference(resolution, [status(thm)], [c_2, c_1892])).
% 4.62/1.87  tff(c_1899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1438, c_1446, c_1895])).
% 4.62/1.87  tff(c_1901, plain, (~r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(splitRight, [status(thm)], [c_30])).
% 4.62/1.87  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_5') | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_1991, plain, (r2_hidden('#skF_1', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1901, c_34])).
% 4.62/1.87  tff(c_32, plain, (r2_hidden('#skF_2', '#skF_6') | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_1931, plain, (r2_hidden('#skF_2', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1901, c_32])).
% 4.62/1.87  tff(c_1900, plain, (r2_hidden('#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_30])).
% 4.62/1.87  tff(c_1948, plain, (![A_527, B_528, C_529, D_530]: (r2_hidden(k4_tarski(A_527, B_528), k2_zfmisc_1(C_529, D_530)) | ~r2_hidden(B_528, D_530) | ~r2_hidden(A_527, C_529))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.87  tff(c_2156, plain, (![A_599, C_598, C_596, D_595, B_597]: (r2_hidden(k3_mcart_1(A_599, B_597, C_598), k2_zfmisc_1(C_596, D_595)) | ~r2_hidden(C_598, D_595) | ~r2_hidden(k4_tarski(A_599, B_597), C_596))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1948])).
% 4.62/1.87  tff(c_2174, plain, (![A_599, A_8, C_598, C_10, B_9, B_597]: (r2_hidden(k3_mcart_1(A_599, B_597, C_598), k3_zfmisc_1(A_8, B_9, C_10)) | ~r2_hidden(C_598, C_10) | ~r2_hidden(k4_tarski(A_599, B_597), k2_zfmisc_1(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2156])).
% 4.62/1.87  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_8') | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_2000, plain, (r2_hidden('#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1901, c_28])).
% 4.62/1.87  tff(c_2307, plain, (![C_630, D_634, B_633, C_631, D_629, A_632]: (r2_hidden(k4_mcart_1(A_632, B_633, C_631, D_634), k2_zfmisc_1(C_630, D_629)) | ~r2_hidden(D_634, D_629) | ~r2_hidden(k3_mcart_1(A_632, B_633, C_631), C_630))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1948])).
% 4.62/1.87  tff(c_2463, plain, (![B_681, D_678, C_677, B_680, A_683, C_682, D_679, A_684]: (r2_hidden(k4_mcart_1(A_683, B_680, C_682, D_679), k4_zfmisc_1(A_684, B_681, C_677, D_678)) | ~r2_hidden(D_679, D_678) | ~r2_hidden(k3_mcart_1(A_683, B_680, C_682), k3_zfmisc_1(A_684, B_681, C_677)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2307])).
% 4.62/1.87  tff(c_26, plain, (~r2_hidden(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.62/1.87  tff(c_2155, plain, (~r2_hidden(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1901, c_26])).
% 4.62/1.87  tff(c_2469, plain, (~r2_hidden('#skF_4', '#skF_8') | ~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2463, c_2155])).
% 4.62/1.87  tff(c_2491, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_2469])).
% 4.62/1.87  tff(c_2500, plain, (~r2_hidden('#skF_3', '#skF_7') | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2174, c_2491])).
% 4.62/1.87  tff(c_2503, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1900, c_2500])).
% 4.62/1.87  tff(c_2506, plain, (~r2_hidden('#skF_2', '#skF_6') | ~r2_hidden('#skF_1', '#skF_5')), inference(resolution, [status(thm)], [c_2, c_2503])).
% 4.62/1.87  tff(c_2510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1991, c_1931, c_2506])).
% 4.62/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.87  
% 4.62/1.87  Inference rules
% 4.62/1.87  ----------------------
% 4.62/1.87  #Ref     : 0
% 4.62/1.87  #Sup     : 596
% 4.62/1.87  #Fact    : 0
% 4.62/1.87  #Define  : 0
% 4.62/1.87  #Split   : 6
% 4.62/1.87  #Chain   : 0
% 4.62/1.87  #Close   : 0
% 4.62/1.87  
% 4.62/1.87  Ordering : KBO
% 4.62/1.87  
% 4.62/1.87  Simplification rules
% 4.62/1.87  ----------------------
% 4.62/1.87  #Subsume      : 321
% 4.62/1.87  #Demod        : 466
% 4.62/1.87  #Tautology    : 241
% 4.62/1.87  #SimpNegUnit  : 7
% 4.62/1.87  #BackRed      : 0
% 4.62/1.87  
% 4.62/1.87  #Partial instantiations: 0
% 4.62/1.87  #Strategies tried      : 1
% 4.62/1.87  
% 4.62/1.87  Timing (in seconds)
% 4.62/1.87  ----------------------
% 4.62/1.87  Preprocessing        : 0.28
% 4.62/1.87  Parsing              : 0.15
% 4.62/1.87  CNF conversion       : 0.02
% 4.62/1.87  Main loop            : 0.80
% 4.62/1.87  Inferencing          : 0.33
% 4.62/1.87  Reduction            : 0.25
% 4.62/1.87  Demodulation         : 0.19
% 4.62/1.87  BG Simplification    : 0.03
% 4.62/1.87  Subsumption          : 0.13
% 4.62/1.87  Abstraction          : 0.04
% 4.62/1.87  MUC search           : 0.00
% 4.62/1.87  Cooper               : 0.00
% 4.62/1.87  Total                : 1.14
% 4.62/1.87  Index Insertion      : 0.00
% 4.62/1.87  Index Deletion       : 0.00
% 4.62/1.87  Index Matching       : 0.00
% 4.62/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
