%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:17 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 571 expanded)
%              Number of leaves         :   29 ( 195 expanded)
%              Depth                    :   15
%              Number of atoms          :  195 (1280 expanded)
%              Number of equality atoms :   33 ( 352 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,
    ( '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_68,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_246,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( r2_hidden(k4_tarski(A_99,B_100),k2_zfmisc_1(C_101,D_102))
      | ~ r2_hidden(B_100,D_102)
      | ~ r2_hidden(A_99,C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_214,plain,(
    ! [B_88,D_89,A_90,C_91] :
      ( r2_hidden(B_88,D_89)
      | ~ r2_hidden(k4_tarski(A_90,B_88),k2_zfmisc_1(C_91,D_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_217,plain,(
    ! [B_88,A_90] :
      ( r2_hidden(B_88,'#skF_12')
      | ~ r2_hidden(k4_tarski(A_90,B_88),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_214])).

tff(c_272,plain,(
    ! [B_100,A_99] :
      ( r2_hidden(B_100,'#skF_12')
      | ~ r2_hidden(B_100,'#skF_10')
      | ~ r2_hidden(A_99,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_246,c_217])).

tff(c_295,plain,(
    ! [A_105] : ~ r2_hidden(A_105,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_306,plain,(
    ! [B_106] : r1_tarski('#skF_9',B_106) ),
    inference(resolution,[status(thm)],[c_6,c_295])).

tff(c_123,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [A_13,C_64] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_116])).

tff(c_121,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_132,plain,(
    ! [B_67] : r1_tarski(k1_xboole_0,B_67) ),
    inference(resolution,[status(thm)],[c_123,c_121])).

tff(c_135,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_140,plain,(
    ! [B_67] :
      ( k1_xboole_0 = B_67
      | ~ r1_tarski(B_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_132,c_135])).

tff(c_313,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_306,c_140])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_313])).

tff(c_323,plain,(
    ! [B_107] :
      ( r2_hidden(B_107,'#skF_12')
      | ~ r2_hidden(B_107,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_367,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_1'('#skF_10',B_111),'#skF_12')
      | r1_tarski('#skF_10',B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_375,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_367,c_4])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_378,plain,
    ( '#skF_10' = '#skF_12'
    | ~ r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_375,c_12])).

tff(c_379,plain,(
    ~ r1_tarski('#skF_12','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_380,plain,(
    ! [A_112,B_113] :
      ( r2_hidden(k4_tarski(A_112,B_113),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(B_113,'#skF_12')
      | ~ r2_hidden(A_112,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_246])).

tff(c_48,plain,(
    ! [B_50,D_52,A_49,C_51] :
      ( r2_hidden(B_50,D_52)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_397,plain,(
    ! [B_113,A_112] :
      ( r2_hidden(B_113,'#skF_10')
      | ~ r2_hidden(B_113,'#skF_12')
      | ~ r2_hidden(A_112,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_380,c_48])).

tff(c_497,plain,(
    ! [A_121] : ~ r2_hidden(A_121,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_517,plain,(
    ! [B_2] : r1_tarski('#skF_11',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_497])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_203,plain,(
    ! [A_84,C_85,B_86,D_87] :
      ( r2_hidden(A_84,C_85)
      | ~ r2_hidden(k4_tarski(A_84,B_86),k2_zfmisc_1(C_85,D_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_206,plain,(
    ! [A_84,B_86] :
      ( r2_hidden(A_84,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_84,B_86),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_203])).

tff(c_273,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(A_99,'#skF_11')
      | ~ r2_hidden(B_100,'#skF_10')
      | ~ r2_hidden(A_99,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_246,c_206])).

tff(c_401,plain,(
    ! [B_114] : ~ r2_hidden(B_114,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_419,plain,(
    ! [B_115] : r1_tarski('#skF_10',B_115) ),
    inference(resolution,[status(thm)],[c_6,c_401])).

tff(c_426,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_419,c_140])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_426])).

tff(c_436,plain,(
    ! [A_116] :
      ( r2_hidden(A_116,'#skF_11')
      | ~ r2_hidden(A_116,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_478,plain,(
    ! [A_120] :
      ( r1_tarski(A_120,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_120,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_436,c_4])).

tff(c_488,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_478])).

tff(c_490,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_488,c_12])).

tff(c_493,plain,(
    ~ r1_tarski('#skF_11','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_490])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_493])).

tff(c_543,plain,(
    ! [B_123] :
      ( r2_hidden(B_123,'#skF_10')
      | ~ r2_hidden(B_123,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_591,plain,(
    ! [A_128] :
      ( r1_tarski(A_128,'#skF_10')
      | ~ r2_hidden('#skF_1'(A_128,'#skF_10'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_543,c_4])).

tff(c_603,plain,(
    r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_6,c_591])).

tff(c_610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_379,c_603])).

tff(c_611,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_620,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_60])).

tff(c_648,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(A_99,'#skF_11')
      | ~ r2_hidden(B_100,'#skF_12')
      | ~ r2_hidden(A_99,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_273])).

tff(c_650,plain,(
    ! [B_129] : ~ r2_hidden(B_129,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_648])).

tff(c_700,plain,(
    ! [B_133] : r1_tarski('#skF_12',B_133) ),
    inference(resolution,[status(thm)],[c_6,c_650])).

tff(c_707,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_700,c_140])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_707])).

tff(c_717,plain,(
    ! [A_134] :
      ( r2_hidden(A_134,'#skF_11')
      | ~ r2_hidden(A_134,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_648])).

tff(c_726,plain,(
    ! [A_135] :
      ( r1_tarski(A_135,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_135,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_717,c_4])).

tff(c_736,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_726])).

tff(c_751,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_736,c_12])).

tff(c_754,plain,(
    ~ r1_tarski('#skF_11','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_751])).

tff(c_265,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(k4_tarski(A_99,B_100),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(B_100,'#skF_12')
      | ~ r2_hidden(A_99,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_246])).

tff(c_738,plain,(
    ! [A_136,B_137] :
      ( r2_hidden(k4_tarski(A_136,B_137),k2_zfmisc_1('#skF_9','#skF_12'))
      | ~ r2_hidden(B_137,'#skF_12')
      | ~ r2_hidden(A_136,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_265])).

tff(c_50,plain,(
    ! [A_49,C_51,B_50,D_52] :
      ( r2_hidden(A_49,C_51)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_748,plain,(
    ! [A_136,B_137] :
      ( r2_hidden(A_136,'#skF_9')
      | ~ r2_hidden(B_137,'#skF_12')
      | ~ r2_hidden(A_136,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_738,c_50])).

tff(c_814,plain,(
    ! [B_145] : ~ r2_hidden(B_145,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_835,plain,(
    ! [B_146] : r1_tarski('#skF_12',B_146) ),
    inference(resolution,[status(thm)],[c_6,c_814])).

tff(c_842,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_835,c_140])).

tff(c_850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_842])).

tff(c_862,plain,(
    ! [A_149] :
      ( r2_hidden(A_149,'#skF_9')
      | ~ r2_hidden(A_149,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_887,plain,(
    ! [B_150] :
      ( r2_hidden('#skF_1'('#skF_11',B_150),'#skF_9')
      | r1_tarski('#skF_11',B_150) ) ),
    inference(resolution,[status(thm)],[c_6,c_862])).

tff(c_899,plain,(
    r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_887,c_4])).

tff(c_907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_754,c_754,c_899])).

tff(c_908,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1091,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( r2_hidden(k4_tarski(A_191,B_192),k2_zfmisc_1(C_193,D_194))
      | ~ r2_hidden(B_192,D_194)
      | ~ r2_hidden(A_191,C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_909,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_943,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_9','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_64])).

tff(c_1060,plain,(
    ! [B_182,D_183,A_184,C_185] :
      ( r2_hidden(B_182,D_183)
      | ~ r2_hidden(k4_tarski(A_184,B_182),k2_zfmisc_1(C_185,D_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1063,plain,(
    ! [B_182,A_184] :
      ( r2_hidden(B_182,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_184,B_182),k2_zfmisc_1('#skF_9','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_1060])).

tff(c_1113,plain,(
    ! [B_192,A_191] :
      ( r2_hidden(B_192,'#skF_10')
      | ~ r2_hidden(B_192,'#skF_12')
      | ~ r2_hidden(A_191,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1091,c_1063])).

tff(c_1135,plain,(
    ! [A_197] : ~ r2_hidden(A_197,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1113])).

tff(c_1146,plain,(
    ! [B_198] : r1_tarski('#skF_9',B_198) ),
    inference(resolution,[status(thm)],[c_6,c_1135])).

tff(c_978,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_1'(A_164,B_165),A_164)
      | r1_tarski(A_164,B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_971,plain,(
    ! [A_160,B_161,C_162] :
      ( ~ r1_xboole_0(A_160,B_161)
      | ~ r2_hidden(C_162,k3_xboole_0(A_160,B_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_974,plain,(
    ! [A_13,C_162] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_162,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_971])).

tff(c_976,plain,(
    ! [C_162] : ~ r2_hidden(C_162,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_974])).

tff(c_999,plain,(
    ! [B_169] : r1_tarski(k1_xboole_0,B_169) ),
    inference(resolution,[status(thm)],[c_978,c_976])).

tff(c_1002,plain,(
    ! [B_169] :
      ( k1_xboole_0 = B_169
      | ~ r1_tarski(B_169,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_999,c_12])).

tff(c_1153,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1146,c_1002])).

tff(c_1161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1153])).

tff(c_1163,plain,(
    ! [B_199] :
      ( r2_hidden(B_199,'#skF_10')
      | ~ r2_hidden(B_199,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_1172,plain,(
    ! [A_200] :
      ( r1_tarski(A_200,'#skF_10')
      | ~ r2_hidden('#skF_1'(A_200,'#skF_10'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_1163,c_4])).

tff(c_1182,plain,(
    r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_6,c_1172])).

tff(c_1184,plain,
    ( '#skF_10' = '#skF_12'
    | ~ r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_1182,c_12])).

tff(c_1187,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_908,c_1184])).

tff(c_1242,plain,(
    ! [A_208,B_209] :
      ( r2_hidden(k4_tarski(A_208,B_209),k2_zfmisc_1('#skF_9','#skF_12'))
      | ~ r2_hidden(B_209,'#skF_10')
      | ~ r2_hidden(A_208,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_1091])).

tff(c_1255,plain,(
    ! [B_209,A_208] :
      ( r2_hidden(B_209,'#skF_12')
      | ~ r2_hidden(B_209,'#skF_10')
      | ~ r2_hidden(A_208,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1242,c_48])).

tff(c_1259,plain,(
    ! [A_210] : ~ r2_hidden(A_210,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1255])).

tff(c_1275,plain,(
    ! [B_211] : r1_tarski('#skF_9',B_211) ),
    inference(resolution,[status(thm)],[c_6,c_1259])).

tff(c_1282,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1275,c_1002])).

tff(c_1290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1282])).

tff(c_1292,plain,(
    ! [B_212] :
      ( r2_hidden(B_212,'#skF_12')
      | ~ r2_hidden(B_212,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_1255])).

tff(c_1312,plain,(
    ! [B_213] :
      ( r2_hidden('#skF_1'('#skF_10',B_213),'#skF_12')
      | r1_tarski('#skF_10',B_213) ) ),
    inference(resolution,[status(thm)],[c_6,c_1292])).

tff(c_1324,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_1312,c_4])).

tff(c_1332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_1187,c_1324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 3.19/1.49  
% 3.19/1.49  %Foreground sorts:
% 3.19/1.49  
% 3.19/1.49  
% 3.19/1.49  %Background operators:
% 3.19/1.49  
% 3.19/1.49  
% 3.19/1.49  %Foreground operators:
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.49  tff('#skF_11', type, '#skF_11': $i).
% 3.19/1.49  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.19/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.19/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.19/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.49  tff('#skF_10', type, '#skF_10': $i).
% 3.19/1.49  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.19/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.19/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.49  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.19/1.49  tff('#skF_9', type, '#skF_9': $i).
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.49  tff('#skF_12', type, '#skF_12': $i).
% 3.19/1.49  
% 3.19/1.51  tff(f_91, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.19/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.19/1.51  tff(f_74, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.19/1.51  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.19/1.51  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.19/1.51  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.19/1.51  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.19/1.51  tff(c_58, plain, ('#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.51  tff(c_68, plain, ('#skF_11'!='#skF_9'), inference(splitLeft, [status(thm)], [c_58])).
% 3.19/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.51  tff(c_62, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.51  tff(c_246, plain, (![A_99, B_100, C_101, D_102]: (r2_hidden(k4_tarski(A_99, B_100), k2_zfmisc_1(C_101, D_102)) | ~r2_hidden(B_100, D_102) | ~r2_hidden(A_99, C_101))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.51  tff(c_64, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.51  tff(c_214, plain, (![B_88, D_89, A_90, C_91]: (r2_hidden(B_88, D_89) | ~r2_hidden(k4_tarski(A_90, B_88), k2_zfmisc_1(C_91, D_89)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.51  tff(c_217, plain, (![B_88, A_90]: (r2_hidden(B_88, '#skF_12') | ~r2_hidden(k4_tarski(A_90, B_88), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_214])).
% 3.19/1.51  tff(c_272, plain, (![B_100, A_99]: (r2_hidden(B_100, '#skF_12') | ~r2_hidden(B_100, '#skF_10') | ~r2_hidden(A_99, '#skF_9'))), inference(resolution, [status(thm)], [c_246, c_217])).
% 3.19/1.51  tff(c_295, plain, (![A_105]: (~r2_hidden(A_105, '#skF_9'))), inference(splitLeft, [status(thm)], [c_272])).
% 3.19/1.51  tff(c_306, plain, (![B_106]: (r1_tarski('#skF_9', B_106))), inference(resolution, [status(thm)], [c_6, c_295])).
% 3.19/1.51  tff(c_123, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.51  tff(c_20, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.19/1.51  tff(c_18, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.19/1.51  tff(c_116, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.19/1.51  tff(c_119, plain, (![A_13, C_64]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_116])).
% 3.19/1.51  tff(c_121, plain, (![C_64]: (~r2_hidden(C_64, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_119])).
% 3.19/1.51  tff(c_132, plain, (![B_67]: (r1_tarski(k1_xboole_0, B_67))), inference(resolution, [status(thm)], [c_123, c_121])).
% 3.19/1.51  tff(c_135, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.19/1.51  tff(c_140, plain, (![B_67]: (k1_xboole_0=B_67 | ~r1_tarski(B_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_132, c_135])).
% 3.19/1.51  tff(c_313, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_306, c_140])).
% 3.19/1.51  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_313])).
% 3.19/1.51  tff(c_323, plain, (![B_107]: (r2_hidden(B_107, '#skF_12') | ~r2_hidden(B_107, '#skF_10'))), inference(splitRight, [status(thm)], [c_272])).
% 3.19/1.51  tff(c_367, plain, (![B_111]: (r2_hidden('#skF_1'('#skF_10', B_111), '#skF_12') | r1_tarski('#skF_10', B_111))), inference(resolution, [status(thm)], [c_6, c_323])).
% 3.19/1.51  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.51  tff(c_375, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_367, c_4])).
% 3.19/1.51  tff(c_12, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.19/1.51  tff(c_378, plain, ('#skF_10'='#skF_12' | ~r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_375, c_12])).
% 3.19/1.51  tff(c_379, plain, (~r1_tarski('#skF_12', '#skF_10')), inference(splitLeft, [status(thm)], [c_378])).
% 3.19/1.51  tff(c_380, plain, (![A_112, B_113]: (r2_hidden(k4_tarski(A_112, B_113), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(B_113, '#skF_12') | ~r2_hidden(A_112, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_246])).
% 3.19/1.51  tff(c_48, plain, (![B_50, D_52, A_49, C_51]: (r2_hidden(B_50, D_52) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.51  tff(c_397, plain, (![B_113, A_112]: (r2_hidden(B_113, '#skF_10') | ~r2_hidden(B_113, '#skF_12') | ~r2_hidden(A_112, '#skF_11'))), inference(resolution, [status(thm)], [c_380, c_48])).
% 3.19/1.51  tff(c_497, plain, (![A_121]: (~r2_hidden(A_121, '#skF_11'))), inference(splitLeft, [status(thm)], [c_397])).
% 3.19/1.51  tff(c_517, plain, (![B_2]: (r1_tarski('#skF_11', B_2))), inference(resolution, [status(thm)], [c_6, c_497])).
% 3.19/1.51  tff(c_60, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.51  tff(c_203, plain, (![A_84, C_85, B_86, D_87]: (r2_hidden(A_84, C_85) | ~r2_hidden(k4_tarski(A_84, B_86), k2_zfmisc_1(C_85, D_87)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.51  tff(c_206, plain, (![A_84, B_86]: (r2_hidden(A_84, '#skF_11') | ~r2_hidden(k4_tarski(A_84, B_86), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_203])).
% 3.19/1.51  tff(c_273, plain, (![A_99, B_100]: (r2_hidden(A_99, '#skF_11') | ~r2_hidden(B_100, '#skF_10') | ~r2_hidden(A_99, '#skF_9'))), inference(resolution, [status(thm)], [c_246, c_206])).
% 3.19/1.51  tff(c_401, plain, (![B_114]: (~r2_hidden(B_114, '#skF_10'))), inference(splitLeft, [status(thm)], [c_273])).
% 3.19/1.51  tff(c_419, plain, (![B_115]: (r1_tarski('#skF_10', B_115))), inference(resolution, [status(thm)], [c_6, c_401])).
% 3.19/1.51  tff(c_426, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_419, c_140])).
% 3.19/1.51  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_426])).
% 3.19/1.51  tff(c_436, plain, (![A_116]: (r2_hidden(A_116, '#skF_11') | ~r2_hidden(A_116, '#skF_9'))), inference(splitRight, [status(thm)], [c_273])).
% 3.19/1.51  tff(c_478, plain, (![A_120]: (r1_tarski(A_120, '#skF_11') | ~r2_hidden('#skF_1'(A_120, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_436, c_4])).
% 3.19/1.51  tff(c_488, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_478])).
% 3.19/1.51  tff(c_490, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_488, c_12])).
% 3.19/1.51  tff(c_493, plain, (~r1_tarski('#skF_11', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_68, c_490])).
% 3.19/1.51  tff(c_541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_517, c_493])).
% 3.19/1.51  tff(c_543, plain, (![B_123]: (r2_hidden(B_123, '#skF_10') | ~r2_hidden(B_123, '#skF_12'))), inference(splitRight, [status(thm)], [c_397])).
% 3.19/1.51  tff(c_591, plain, (![A_128]: (r1_tarski(A_128, '#skF_10') | ~r2_hidden('#skF_1'(A_128, '#skF_10'), '#skF_12'))), inference(resolution, [status(thm)], [c_543, c_4])).
% 3.19/1.51  tff(c_603, plain, (r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_6, c_591])).
% 3.19/1.51  tff(c_610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_379, c_603])).
% 3.19/1.51  tff(c_611, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_378])).
% 3.19/1.51  tff(c_620, plain, (k1_xboole_0!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_611, c_60])).
% 3.19/1.51  tff(c_648, plain, (![A_99, B_100]: (r2_hidden(A_99, '#skF_11') | ~r2_hidden(B_100, '#skF_12') | ~r2_hidden(A_99, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_273])).
% 3.19/1.51  tff(c_650, plain, (![B_129]: (~r2_hidden(B_129, '#skF_12'))), inference(splitLeft, [status(thm)], [c_648])).
% 3.19/1.51  tff(c_700, plain, (![B_133]: (r1_tarski('#skF_12', B_133))), inference(resolution, [status(thm)], [c_6, c_650])).
% 3.19/1.51  tff(c_707, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_700, c_140])).
% 3.19/1.51  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_707])).
% 3.19/1.51  tff(c_717, plain, (![A_134]: (r2_hidden(A_134, '#skF_11') | ~r2_hidden(A_134, '#skF_9'))), inference(splitRight, [status(thm)], [c_648])).
% 3.19/1.51  tff(c_726, plain, (![A_135]: (r1_tarski(A_135, '#skF_11') | ~r2_hidden('#skF_1'(A_135, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_717, c_4])).
% 3.19/1.51  tff(c_736, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_726])).
% 3.19/1.51  tff(c_751, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_736, c_12])).
% 3.19/1.51  tff(c_754, plain, (~r1_tarski('#skF_11', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_68, c_751])).
% 3.19/1.51  tff(c_265, plain, (![A_99, B_100]: (r2_hidden(k4_tarski(A_99, B_100), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(B_100, '#skF_12') | ~r2_hidden(A_99, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_246])).
% 3.19/1.51  tff(c_738, plain, (![A_136, B_137]: (r2_hidden(k4_tarski(A_136, B_137), k2_zfmisc_1('#skF_9', '#skF_12')) | ~r2_hidden(B_137, '#skF_12') | ~r2_hidden(A_136, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_265])).
% 3.19/1.51  tff(c_50, plain, (![A_49, C_51, B_50, D_52]: (r2_hidden(A_49, C_51) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.51  tff(c_748, plain, (![A_136, B_137]: (r2_hidden(A_136, '#skF_9') | ~r2_hidden(B_137, '#skF_12') | ~r2_hidden(A_136, '#skF_11'))), inference(resolution, [status(thm)], [c_738, c_50])).
% 3.19/1.51  tff(c_814, plain, (![B_145]: (~r2_hidden(B_145, '#skF_12'))), inference(splitLeft, [status(thm)], [c_748])).
% 3.19/1.51  tff(c_835, plain, (![B_146]: (r1_tarski('#skF_12', B_146))), inference(resolution, [status(thm)], [c_6, c_814])).
% 3.19/1.51  tff(c_842, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_835, c_140])).
% 3.19/1.51  tff(c_850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_842])).
% 3.19/1.51  tff(c_862, plain, (![A_149]: (r2_hidden(A_149, '#skF_9') | ~r2_hidden(A_149, '#skF_11'))), inference(splitRight, [status(thm)], [c_748])).
% 3.19/1.51  tff(c_887, plain, (![B_150]: (r2_hidden('#skF_1'('#skF_11', B_150), '#skF_9') | r1_tarski('#skF_11', B_150))), inference(resolution, [status(thm)], [c_6, c_862])).
% 3.19/1.51  tff(c_899, plain, (r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_887, c_4])).
% 3.19/1.51  tff(c_907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_754, c_754, c_899])).
% 3.19/1.51  tff(c_908, plain, ('#skF_10'!='#skF_12'), inference(splitRight, [status(thm)], [c_58])).
% 3.19/1.51  tff(c_1091, plain, (![A_191, B_192, C_193, D_194]: (r2_hidden(k4_tarski(A_191, B_192), k2_zfmisc_1(C_193, D_194)) | ~r2_hidden(B_192, D_194) | ~r2_hidden(A_191, C_193))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.51  tff(c_909, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 3.19/1.51  tff(c_943, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_909, c_64])).
% 3.19/1.51  tff(c_1060, plain, (![B_182, D_183, A_184, C_185]: (r2_hidden(B_182, D_183) | ~r2_hidden(k4_tarski(A_184, B_182), k2_zfmisc_1(C_185, D_183)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.51  tff(c_1063, plain, (![B_182, A_184]: (r2_hidden(B_182, '#skF_10') | ~r2_hidden(k4_tarski(A_184, B_182), k2_zfmisc_1('#skF_9', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_943, c_1060])).
% 3.19/1.51  tff(c_1113, plain, (![B_192, A_191]: (r2_hidden(B_192, '#skF_10') | ~r2_hidden(B_192, '#skF_12') | ~r2_hidden(A_191, '#skF_9'))), inference(resolution, [status(thm)], [c_1091, c_1063])).
% 3.19/1.51  tff(c_1135, plain, (![A_197]: (~r2_hidden(A_197, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1113])).
% 3.19/1.51  tff(c_1146, plain, (![B_198]: (r1_tarski('#skF_9', B_198))), inference(resolution, [status(thm)], [c_6, c_1135])).
% 3.19/1.51  tff(c_978, plain, (![A_164, B_165]: (r2_hidden('#skF_1'(A_164, B_165), A_164) | r1_tarski(A_164, B_165))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.51  tff(c_971, plain, (![A_160, B_161, C_162]: (~r1_xboole_0(A_160, B_161) | ~r2_hidden(C_162, k3_xboole_0(A_160, B_161)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.19/1.51  tff(c_974, plain, (![A_13, C_162]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_162, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_971])).
% 3.19/1.51  tff(c_976, plain, (![C_162]: (~r2_hidden(C_162, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_974])).
% 3.19/1.51  tff(c_999, plain, (![B_169]: (r1_tarski(k1_xboole_0, B_169))), inference(resolution, [status(thm)], [c_978, c_976])).
% 3.19/1.51  tff(c_1002, plain, (![B_169]: (k1_xboole_0=B_169 | ~r1_tarski(B_169, k1_xboole_0))), inference(resolution, [status(thm)], [c_999, c_12])).
% 3.19/1.51  tff(c_1153, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1146, c_1002])).
% 3.19/1.51  tff(c_1161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1153])).
% 3.19/1.51  tff(c_1163, plain, (![B_199]: (r2_hidden(B_199, '#skF_10') | ~r2_hidden(B_199, '#skF_12'))), inference(splitRight, [status(thm)], [c_1113])).
% 3.19/1.51  tff(c_1172, plain, (![A_200]: (r1_tarski(A_200, '#skF_10') | ~r2_hidden('#skF_1'(A_200, '#skF_10'), '#skF_12'))), inference(resolution, [status(thm)], [c_1163, c_4])).
% 3.19/1.51  tff(c_1182, plain, (r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_6, c_1172])).
% 3.19/1.51  tff(c_1184, plain, ('#skF_10'='#skF_12' | ~r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_1182, c_12])).
% 3.19/1.51  tff(c_1187, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_908, c_1184])).
% 3.19/1.51  tff(c_1242, plain, (![A_208, B_209]: (r2_hidden(k4_tarski(A_208, B_209), k2_zfmisc_1('#skF_9', '#skF_12')) | ~r2_hidden(B_209, '#skF_10') | ~r2_hidden(A_208, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_943, c_1091])).
% 3.19/1.51  tff(c_1255, plain, (![B_209, A_208]: (r2_hidden(B_209, '#skF_12') | ~r2_hidden(B_209, '#skF_10') | ~r2_hidden(A_208, '#skF_9'))), inference(resolution, [status(thm)], [c_1242, c_48])).
% 3.19/1.51  tff(c_1259, plain, (![A_210]: (~r2_hidden(A_210, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1255])).
% 3.19/1.51  tff(c_1275, plain, (![B_211]: (r1_tarski('#skF_9', B_211))), inference(resolution, [status(thm)], [c_6, c_1259])).
% 3.19/1.51  tff(c_1282, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1275, c_1002])).
% 3.19/1.51  tff(c_1290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1282])).
% 3.19/1.51  tff(c_1292, plain, (![B_212]: (r2_hidden(B_212, '#skF_12') | ~r2_hidden(B_212, '#skF_10'))), inference(splitRight, [status(thm)], [c_1255])).
% 3.19/1.51  tff(c_1312, plain, (![B_213]: (r2_hidden('#skF_1'('#skF_10', B_213), '#skF_12') | r1_tarski('#skF_10', B_213))), inference(resolution, [status(thm)], [c_6, c_1292])).
% 3.19/1.51  tff(c_1324, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_1312, c_4])).
% 3.19/1.51  tff(c_1332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1187, c_1187, c_1324])).
% 3.19/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.51  
% 3.19/1.51  Inference rules
% 3.19/1.51  ----------------------
% 3.19/1.51  #Ref     : 0
% 3.19/1.51  #Sup     : 263
% 3.19/1.51  #Fact    : 0
% 3.19/1.51  #Define  : 0
% 3.19/1.51  #Split   : 10
% 3.19/1.51  #Chain   : 0
% 3.19/1.51  #Close   : 0
% 3.19/1.51  
% 3.19/1.51  Ordering : KBO
% 3.19/1.51  
% 3.19/1.51  Simplification rules
% 3.19/1.51  ----------------------
% 3.19/1.51  #Subsume      : 48
% 3.19/1.51  #Demod        : 67
% 3.19/1.51  #Tautology    : 80
% 3.19/1.51  #SimpNegUnit  : 32
% 3.19/1.51  #BackRed      : 10
% 3.19/1.51  
% 3.19/1.51  #Partial instantiations: 0
% 3.19/1.51  #Strategies tried      : 1
% 3.19/1.51  
% 3.19/1.51  Timing (in seconds)
% 3.19/1.51  ----------------------
% 3.19/1.52  Preprocessing        : 0.33
% 3.19/1.52  Parsing              : 0.17
% 3.19/1.52  CNF conversion       : 0.03
% 3.19/1.52  Main loop            : 0.41
% 3.19/1.52  Inferencing          : 0.15
% 3.19/1.52  Reduction            : 0.12
% 3.19/1.52  Demodulation         : 0.08
% 3.19/1.52  BG Simplification    : 0.02
% 3.19/1.52  Subsumption          : 0.08
% 3.19/1.52  Abstraction          : 0.02
% 3.19/1.52  MUC search           : 0.00
% 3.19/1.52  Cooper               : 0.00
% 3.19/1.52  Total                : 0.78
% 3.19/1.52  Index Insertion      : 0.00
% 3.19/1.52  Index Deletion       : 0.00
% 3.19/1.52  Index Matching       : 0.00
% 3.19/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
