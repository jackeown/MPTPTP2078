%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:16 EST 2020

% Result     : Theorem 5.67s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 307 expanded)
%              Number of leaves         :   32 ( 115 expanded)
%              Depth                    :   10
%              Number of atoms          :  201 ( 694 expanded)
%              Number of equality atoms :   38 ( 259 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_46,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_64,plain,
    ( '#skF_11' != '#skF_9'
    | '#skF_10' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_78,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_28,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_206,plain,(
    ! [C_88,A_89,B_90] :
      ( r1_tarski(k2_zfmisc_1(C_88,A_89),k2_zfmisc_1(C_88,B_90))
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_217,plain,(
    ! [B_90] :
      ( r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1('#skF_10',B_90))
      | ~ r1_tarski('#skF_11',B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_206])).

tff(c_579,plain,(
    ! [B_129,A_130,C_131] :
      ( ~ r1_tarski(k2_zfmisc_1(B_129,A_130),k2_zfmisc_1(C_131,A_130))
      | r1_tarski(B_129,C_131)
      | k1_xboole_0 = A_130 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_587,plain,
    ( r1_tarski('#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_217,c_579])).

tff(c_613,plain,
    ( r1_tarski('#skF_8','#skF_10')
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_587])).

tff(c_647,plain,(
    ~ r1_tarski('#skF_11','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_229,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_tarski(k2_zfmisc_1(A_97,C_98),k2_zfmisc_1(B_99,C_98))
      | ~ r1_tarski(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_243,plain,(
    ! [A_97] :
      ( r1_tarski(k2_zfmisc_1(A_97,'#skF_11'),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r1_tarski(A_97,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_229])).

tff(c_652,plain,(
    ! [A_135,B_136,C_137] :
      ( ~ r1_tarski(k2_zfmisc_1(A_135,B_136),k2_zfmisc_1(A_135,C_137))
      | r1_tarski(B_136,C_137)
      | k1_xboole_0 = A_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_656,plain,
    ( r1_tarski('#skF_11','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_243,c_652])).

tff(c_683,plain,(
    ~ r1_tarski('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_647,c_656])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_220,plain,(
    ! [A_89] :
      ( r1_tarski(k2_zfmisc_1('#skF_10',A_89),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r1_tarski(A_89,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_206])).

tff(c_583,plain,
    ( r1_tarski('#skF_10','#skF_8')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_220,c_579])).

tff(c_610,plain,
    ( r1_tarski('#skF_10','#skF_8')
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_583])).

tff(c_642,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_646,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_136,c_642])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_798,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( r2_hidden(k4_tarski(A_141,B_142),k2_zfmisc_1(C_143,D_144))
      | ~ r2_hidden(B_142,D_144)
      | ~ r2_hidden(A_141,C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_180,plain,(
    ! [A_79,C_80,B_81,D_82] :
      ( r2_hidden(A_79,C_80)
      | ~ r2_hidden(k4_tarski(A_79,B_81),k2_zfmisc_1(C_80,D_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_183,plain,(
    ! [A_79,B_81] :
      ( r2_hidden(A_79,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_79,B_81),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_180])).

tff(c_825,plain,(
    ! [A_141,B_142] :
      ( r2_hidden(A_141,'#skF_10')
      | ~ r2_hidden(B_142,'#skF_9')
      | ~ r2_hidden(A_141,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_798,c_183])).

tff(c_1815,plain,(
    ! [B_186] : ~ r2_hidden(B_186,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_825])).

tff(c_1849,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_1815])).

tff(c_1860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_1849])).

tff(c_1889,plain,(
    ! [A_189] :
      ( r2_hidden(A_189,'#skF_10')
      | ~ r2_hidden(A_189,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_825])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1910,plain,(
    ! [A_190] :
      ( r1_tarski(A_190,'#skF_10')
      | ~ r2_hidden('#skF_2'(A_190,'#skF_10'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1889,c_8])).

tff(c_1914,plain,(
    r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_10,c_1910])).

tff(c_1918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_683,c_1914])).

tff(c_1920,plain,(
    r1_tarski('#skF_11','#skF_9') ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2891,plain,(
    ! [A_234,B_235,C_236,D_237] :
      ( r2_hidden(k4_tarski(A_234,B_235),k2_zfmisc_1(C_236,D_237))
      | ~ r2_hidden(B_235,D_237)
      | ~ r2_hidden(A_234,C_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_225,plain,(
    ! [B_93,D_94,A_95,C_96] :
      ( r2_hidden(B_93,D_94)
      | ~ r2_hidden(k4_tarski(A_95,B_93),k2_zfmisc_1(C_96,D_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_228,plain,(
    ! [B_93,A_95] :
      ( r2_hidden(B_93,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_95,B_93),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_225])).

tff(c_2916,plain,(
    ! [B_235,A_234] :
      ( r2_hidden(B_235,'#skF_11')
      | ~ r2_hidden(B_235,'#skF_9')
      | ~ r2_hidden(A_234,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2891,c_228])).

tff(c_3606,plain,(
    ! [A_267] : ~ r2_hidden(A_267,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2916])).

tff(c_3648,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_3606])).

tff(c_18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_144,plain,(
    ! [A_69,B_70] :
      ( ~ v1_xboole_0(A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_111,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_3'(A_59,B_60),B_60)
      | ~ r2_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_121,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | ~ r2_xboole_0(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_125,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_152,plain,(
    ! [B_71,A_72] :
      ( ~ v1_xboole_0(B_71)
      | B_71 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_144,c_125])).

tff(c_155,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_18,c_152])).

tff(c_3660,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3648,c_155])).

tff(c_3670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3660])).

tff(c_3672,plain,(
    ! [B_268] :
      ( r2_hidden(B_268,'#skF_11')
      | ~ r2_hidden(B_268,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2916])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_3'(A_12,B_13),A_12)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3763,plain,(
    ! [B_271] :
      ( ~ r2_xboole_0('#skF_11',B_271)
      | ~ r2_hidden('#skF_3'('#skF_11',B_271),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3672,c_20])).

tff(c_3768,plain,(
    ~ r2_xboole_0('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_22,c_3763])).

tff(c_3782,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_12,c_3768])).

tff(c_3785,plain,(
    '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_3782])).

tff(c_3795,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3785,c_642])).

tff(c_3805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3795])).

tff(c_3806,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_4887,plain,(
    ! [A_320,B_321,C_322,D_323] :
      ( r2_hidden(k4_tarski(A_320,B_321),k2_zfmisc_1(C_322,D_323))
      | ~ r2_hidden(B_321,D_323)
      | ~ r2_hidden(A_320,C_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4914,plain,(
    ! [A_320,B_321] :
      ( r2_hidden(A_320,'#skF_10')
      | ~ r2_hidden(B_321,'#skF_9')
      | ~ r2_hidden(A_320,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4887,c_183])).

tff(c_5419,plain,(
    ! [B_341] : ~ r2_hidden(B_341,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4914])).

tff(c_5461,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_5419])).

tff(c_5473,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_5461,c_155])).

tff(c_5483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5473])).

tff(c_5485,plain,(
    ! [A_342] :
      ( r2_hidden(A_342,'#skF_10')
      | ~ r2_hidden(A_342,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_4914])).

tff(c_5516,plain,(
    ! [B_346] :
      ( ~ r2_xboole_0('#skF_10',B_346)
      | ~ r2_hidden('#skF_3'('#skF_10',B_346),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5485,c_20])).

tff(c_5521,plain,(
    ~ r2_xboole_0('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_22,c_5516])).

tff(c_5524,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_5521])).

tff(c_5527,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3806,c_5524])).

tff(c_5529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5527])).

tff(c_5530,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5531,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_5536,plain,(
    k2_zfmisc_1('#skF_8','#skF_11') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5531,c_70])).

tff(c_5673,plain,(
    ! [A_387,C_388,B_389] :
      ( r1_tarski(k2_zfmisc_1(A_387,C_388),k2_zfmisc_1(B_389,C_388))
      | ~ r1_tarski(A_387,B_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5684,plain,(
    ! [B_389] :
      ( r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(B_389,'#skF_11'))
      | ~ r1_tarski('#skF_8',B_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5536,c_5673])).

tff(c_6080,plain,(
    ! [A_424,B_425,C_426] :
      ( ~ r1_tarski(k2_zfmisc_1(A_424,B_425),k2_zfmisc_1(A_424,C_426))
      | r1_tarski(B_425,C_426)
      | k1_xboole_0 = A_424 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6084,plain,
    ( r1_tarski('#skF_9','#skF_11')
    | k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_5684,c_6080])).

tff(c_6110,plain,
    ( r1_tarski('#skF_9','#skF_11')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6084])).

tff(c_6111,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6110])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6131,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_6111,c_24])).

tff(c_6138,plain,(
    ~ r1_tarski('#skF_11','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_5530,c_6131])).

tff(c_60,plain,(
    ! [A_43,C_45,B_44] :
      ( r1_tarski(k2_zfmisc_1(A_43,C_45),k2_zfmisc_1(B_44,C_45))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6100,plain,(
    ! [C_426] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1('#skF_8',C_426))
      | r1_tarski('#skF_11',C_426)
      | k1_xboole_0 = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5536,c_6080])).

tff(c_6857,plain,(
    ! [C_456] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1('#skF_8',C_456))
      | r1_tarski('#skF_11',C_456) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6100])).

tff(c_6868,plain,
    ( r1_tarski('#skF_11','#skF_9')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_6857])).

tff(c_6889,plain,(
    r1_tarski('#skF_11','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6868])).

tff(c_6891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6138,c_6889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.67/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.15  
% 5.67/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.15  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 5.67/2.15  
% 5.67/2.15  %Foreground sorts:
% 5.67/2.15  
% 5.67/2.15  
% 5.67/2.15  %Background operators:
% 5.67/2.15  
% 5.67/2.15  
% 5.67/2.15  %Foreground operators:
% 5.67/2.15  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.67/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.67/2.15  tff('#skF_11', type, '#skF_11': $i).
% 5.67/2.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.67/2.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.67/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.67/2.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.67/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.67/2.15  tff('#skF_10', type, '#skF_10': $i).
% 5.67/2.15  tff('#skF_9', type, '#skF_9': $i).
% 5.67/2.15  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.67/2.15  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.67/2.15  tff('#skF_8', type, '#skF_8': $i).
% 5.67/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.67/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.67/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.67/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.67/2.15  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.67/2.15  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.67/2.15  
% 5.88/2.17  tff(f_107, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 5.88/2.17  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.88/2.17  tff(f_95, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 5.88/2.17  tff(f_89, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 5.88/2.17  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.88/2.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.88/2.17  tff(f_78, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.88/2.17  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.88/2.17  tff(f_56, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 5.88/2.17  tff(f_46, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.88/2.17  tff(c_64, plain, ('#skF_11'!='#skF_9' | '#skF_10'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.88/2.17  tff(c_78, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_64])).
% 5.88/2.17  tff(c_28, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.88/2.17  tff(c_68, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.88/2.17  tff(c_66, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.88/2.17  tff(c_70, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.88/2.17  tff(c_206, plain, (![C_88, A_89, B_90]: (r1_tarski(k2_zfmisc_1(C_88, A_89), k2_zfmisc_1(C_88, B_90)) | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.88/2.17  tff(c_217, plain, (![B_90]: (r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_10', B_90)) | ~r1_tarski('#skF_11', B_90))), inference(superposition, [status(thm), theory('equality')], [c_70, c_206])).
% 5.88/2.17  tff(c_579, plain, (![B_129, A_130, C_131]: (~r1_tarski(k2_zfmisc_1(B_129, A_130), k2_zfmisc_1(C_131, A_130)) | r1_tarski(B_129, C_131) | k1_xboole_0=A_130)), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.88/2.17  tff(c_587, plain, (r1_tarski('#skF_8', '#skF_10') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_217, c_579])).
% 5.88/2.17  tff(c_613, plain, (r1_tarski('#skF_8', '#skF_10') | ~r1_tarski('#skF_11', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_66, c_587])).
% 5.88/2.17  tff(c_647, plain, (~r1_tarski('#skF_11', '#skF_9')), inference(splitLeft, [status(thm)], [c_613])).
% 5.88/2.17  tff(c_229, plain, (![A_97, C_98, B_99]: (r1_tarski(k2_zfmisc_1(A_97, C_98), k2_zfmisc_1(B_99, C_98)) | ~r1_tarski(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.88/2.17  tff(c_243, plain, (![A_97]: (r1_tarski(k2_zfmisc_1(A_97, '#skF_11'), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r1_tarski(A_97, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_229])).
% 5.88/2.17  tff(c_652, plain, (![A_135, B_136, C_137]: (~r1_tarski(k2_zfmisc_1(A_135, B_136), k2_zfmisc_1(A_135, C_137)) | r1_tarski(B_136, C_137) | k1_xboole_0=A_135)), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.88/2.17  tff(c_656, plain, (r1_tarski('#skF_11', '#skF_9') | k1_xboole_0='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_243, c_652])).
% 5.88/2.17  tff(c_683, plain, (~r1_tarski('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_68, c_647, c_656])).
% 5.88/2.17  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.88/2.17  tff(c_132, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.88/2.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.17  tff(c_136, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_132, c_2])).
% 5.88/2.17  tff(c_220, plain, (![A_89]: (r1_tarski(k2_zfmisc_1('#skF_10', A_89), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r1_tarski(A_89, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_206])).
% 5.88/2.17  tff(c_583, plain, (r1_tarski('#skF_10', '#skF_8') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_220, c_579])).
% 5.88/2.17  tff(c_610, plain, (r1_tarski('#skF_10', '#skF_8') | ~r1_tarski('#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_66, c_583])).
% 5.88/2.17  tff(c_642, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_610])).
% 5.88/2.17  tff(c_646, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_136, c_642])).
% 5.88/2.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.17  tff(c_798, plain, (![A_141, B_142, C_143, D_144]: (r2_hidden(k4_tarski(A_141, B_142), k2_zfmisc_1(C_143, D_144)) | ~r2_hidden(B_142, D_144) | ~r2_hidden(A_141, C_143))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.17  tff(c_180, plain, (![A_79, C_80, B_81, D_82]: (r2_hidden(A_79, C_80) | ~r2_hidden(k4_tarski(A_79, B_81), k2_zfmisc_1(C_80, D_82)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.17  tff(c_183, plain, (![A_79, B_81]: (r2_hidden(A_79, '#skF_10') | ~r2_hidden(k4_tarski(A_79, B_81), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_180])).
% 5.88/2.17  tff(c_825, plain, (![A_141, B_142]: (r2_hidden(A_141, '#skF_10') | ~r2_hidden(B_142, '#skF_9') | ~r2_hidden(A_141, '#skF_8'))), inference(resolution, [status(thm)], [c_798, c_183])).
% 5.88/2.17  tff(c_1815, plain, (![B_186]: (~r2_hidden(B_186, '#skF_9'))), inference(splitLeft, [status(thm)], [c_825])).
% 5.88/2.17  tff(c_1849, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_1815])).
% 5.88/2.17  tff(c_1860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_1849])).
% 5.88/2.17  tff(c_1889, plain, (![A_189]: (r2_hidden(A_189, '#skF_10') | ~r2_hidden(A_189, '#skF_8'))), inference(splitRight, [status(thm)], [c_825])).
% 5.88/2.17  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.88/2.17  tff(c_1910, plain, (![A_190]: (r1_tarski(A_190, '#skF_10') | ~r2_hidden('#skF_2'(A_190, '#skF_10'), '#skF_8'))), inference(resolution, [status(thm)], [c_1889, c_8])).
% 5.88/2.17  tff(c_1914, plain, (r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_10, c_1910])).
% 5.88/2.17  tff(c_1918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_683, c_683, c_1914])).
% 5.88/2.17  tff(c_1920, plain, (r1_tarski('#skF_11', '#skF_9')), inference(splitRight, [status(thm)], [c_613])).
% 5.88/2.17  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.88/2.17  tff(c_22, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.17  tff(c_2891, plain, (![A_234, B_235, C_236, D_237]: (r2_hidden(k4_tarski(A_234, B_235), k2_zfmisc_1(C_236, D_237)) | ~r2_hidden(B_235, D_237) | ~r2_hidden(A_234, C_236))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.17  tff(c_225, plain, (![B_93, D_94, A_95, C_96]: (r2_hidden(B_93, D_94) | ~r2_hidden(k4_tarski(A_95, B_93), k2_zfmisc_1(C_96, D_94)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.17  tff(c_228, plain, (![B_93, A_95]: (r2_hidden(B_93, '#skF_11') | ~r2_hidden(k4_tarski(A_95, B_93), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_225])).
% 5.88/2.17  tff(c_2916, plain, (![B_235, A_234]: (r2_hidden(B_235, '#skF_11') | ~r2_hidden(B_235, '#skF_9') | ~r2_hidden(A_234, '#skF_8'))), inference(resolution, [status(thm)], [c_2891, c_228])).
% 5.88/2.17  tff(c_3606, plain, (![A_267]: (~r2_hidden(A_267, '#skF_8'))), inference(splitLeft, [status(thm)], [c_2916])).
% 5.88/2.17  tff(c_3648, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_3606])).
% 5.88/2.17  tff(c_18, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.17  tff(c_144, plain, (![A_69, B_70]: (~v1_xboole_0(A_69) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_132, c_2])).
% 5.88/2.17  tff(c_111, plain, (![A_59, B_60]: (r2_hidden('#skF_3'(A_59, B_60), B_60) | ~r2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.17  tff(c_121, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | ~r2_xboole_0(A_62, B_61))), inference(resolution, [status(thm)], [c_111, c_2])).
% 5.88/2.17  tff(c_125, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_121])).
% 5.88/2.17  tff(c_152, plain, (![B_71, A_72]: (~v1_xboole_0(B_71) | B_71=A_72 | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_144, c_125])).
% 5.88/2.17  tff(c_155, plain, (![A_72]: (k1_xboole_0=A_72 | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_18, c_152])).
% 5.88/2.17  tff(c_3660, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_3648, c_155])).
% 5.88/2.17  tff(c_3670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3660])).
% 5.88/2.17  tff(c_3672, plain, (![B_268]: (r2_hidden(B_268, '#skF_11') | ~r2_hidden(B_268, '#skF_9'))), inference(splitRight, [status(thm)], [c_2916])).
% 5.88/2.17  tff(c_20, plain, (![A_12, B_13]: (~r2_hidden('#skF_3'(A_12, B_13), A_12) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.17  tff(c_3763, plain, (![B_271]: (~r2_xboole_0('#skF_11', B_271) | ~r2_hidden('#skF_3'('#skF_11', B_271), '#skF_9'))), inference(resolution, [status(thm)], [c_3672, c_20])).
% 5.88/2.17  tff(c_3768, plain, (~r2_xboole_0('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_22, c_3763])).
% 5.88/2.17  tff(c_3782, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_12, c_3768])).
% 5.88/2.17  tff(c_3785, plain, ('#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_3782])).
% 5.88/2.17  tff(c_3795, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3785, c_642])).
% 5.88/2.17  tff(c_3805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_3795])).
% 5.88/2.17  tff(c_3806, plain, (r1_tarski('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_610])).
% 5.88/2.17  tff(c_4887, plain, (![A_320, B_321, C_322, D_323]: (r2_hidden(k4_tarski(A_320, B_321), k2_zfmisc_1(C_322, D_323)) | ~r2_hidden(B_321, D_323) | ~r2_hidden(A_320, C_322))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.17  tff(c_4914, plain, (![A_320, B_321]: (r2_hidden(A_320, '#skF_10') | ~r2_hidden(B_321, '#skF_9') | ~r2_hidden(A_320, '#skF_8'))), inference(resolution, [status(thm)], [c_4887, c_183])).
% 5.88/2.17  tff(c_5419, plain, (![B_341]: (~r2_hidden(B_341, '#skF_9'))), inference(splitLeft, [status(thm)], [c_4914])).
% 5.88/2.17  tff(c_5461, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_5419])).
% 5.88/2.17  tff(c_5473, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_5461, c_155])).
% 5.88/2.17  tff(c_5483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_5473])).
% 5.88/2.17  tff(c_5485, plain, (![A_342]: (r2_hidden(A_342, '#skF_10') | ~r2_hidden(A_342, '#skF_8'))), inference(splitRight, [status(thm)], [c_4914])).
% 5.88/2.17  tff(c_5516, plain, (![B_346]: (~r2_xboole_0('#skF_10', B_346) | ~r2_hidden('#skF_3'('#skF_10', B_346), '#skF_8'))), inference(resolution, [status(thm)], [c_5485, c_20])).
% 5.88/2.17  tff(c_5521, plain, (~r2_xboole_0('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_22, c_5516])).
% 5.88/2.17  tff(c_5524, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_12, c_5521])).
% 5.88/2.17  tff(c_5527, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3806, c_5524])).
% 5.88/2.17  tff(c_5529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5527])).
% 5.88/2.17  tff(c_5530, plain, ('#skF_11'!='#skF_9'), inference(splitRight, [status(thm)], [c_64])).
% 5.88/2.17  tff(c_5531, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 5.88/2.17  tff(c_5536, plain, (k2_zfmisc_1('#skF_8', '#skF_11')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5531, c_70])).
% 5.88/2.17  tff(c_5673, plain, (![A_387, C_388, B_389]: (r1_tarski(k2_zfmisc_1(A_387, C_388), k2_zfmisc_1(B_389, C_388)) | ~r1_tarski(A_387, B_389))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.88/2.17  tff(c_5684, plain, (![B_389]: (r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(B_389, '#skF_11')) | ~r1_tarski('#skF_8', B_389))), inference(superposition, [status(thm), theory('equality')], [c_5536, c_5673])).
% 5.88/2.17  tff(c_6080, plain, (![A_424, B_425, C_426]: (~r1_tarski(k2_zfmisc_1(A_424, B_425), k2_zfmisc_1(A_424, C_426)) | r1_tarski(B_425, C_426) | k1_xboole_0=A_424)), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.88/2.17  tff(c_6084, plain, (r1_tarski('#skF_9', '#skF_11') | k1_xboole_0='#skF_8' | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_5684, c_6080])).
% 5.88/2.17  tff(c_6110, plain, (r1_tarski('#skF_9', '#skF_11') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6084])).
% 5.88/2.17  tff(c_6111, plain, (r1_tarski('#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_68, c_6110])).
% 5.88/2.17  tff(c_24, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.88/2.17  tff(c_6131, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_6111, c_24])).
% 5.88/2.17  tff(c_6138, plain, (~r1_tarski('#skF_11', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_5530, c_6131])).
% 5.88/2.17  tff(c_60, plain, (![A_43, C_45, B_44]: (r1_tarski(k2_zfmisc_1(A_43, C_45), k2_zfmisc_1(B_44, C_45)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.88/2.17  tff(c_6100, plain, (![C_426]: (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_8', C_426)) | r1_tarski('#skF_11', C_426) | k1_xboole_0='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5536, c_6080])).
% 5.88/2.17  tff(c_6857, plain, (![C_456]: (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_8', C_456)) | r1_tarski('#skF_11', C_456))), inference(negUnitSimplification, [status(thm)], [c_68, c_6100])).
% 5.88/2.17  tff(c_6868, plain, (r1_tarski('#skF_11', '#skF_9') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_6857])).
% 5.88/2.17  tff(c_6889, plain, (r1_tarski('#skF_11', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6868])).
% 5.88/2.17  tff(c_6891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6138, c_6889])).
% 5.88/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.17  
% 5.88/2.17  Inference rules
% 5.88/2.17  ----------------------
% 5.88/2.17  #Ref     : 0
% 5.88/2.17  #Sup     : 1518
% 5.88/2.17  #Fact    : 0
% 5.88/2.17  #Define  : 0
% 5.88/2.17  #Split   : 20
% 5.88/2.17  #Chain   : 0
% 5.88/2.17  #Close   : 0
% 5.88/2.17  
% 5.88/2.17  Ordering : KBO
% 5.88/2.17  
% 5.88/2.17  Simplification rules
% 5.88/2.17  ----------------------
% 5.88/2.17  #Subsume      : 464
% 5.88/2.17  #Demod        : 984
% 5.88/2.17  #Tautology    : 512
% 5.88/2.17  #SimpNegUnit  : 68
% 5.88/2.17  #BackRed      : 120
% 5.88/2.17  
% 5.88/2.17  #Partial instantiations: 0
% 5.88/2.17  #Strategies tried      : 1
% 5.88/2.17  
% 5.88/2.17  Timing (in seconds)
% 5.88/2.17  ----------------------
% 5.88/2.18  Preprocessing        : 0.34
% 5.88/2.18  Parsing              : 0.18
% 5.88/2.18  CNF conversion       : 0.03
% 5.88/2.18  Main loop            : 1.01
% 5.88/2.18  Inferencing          : 0.36
% 5.88/2.18  Reduction            : 0.28
% 5.88/2.18  Demodulation         : 0.18
% 5.88/2.18  BG Simplification    : 0.04
% 5.88/2.18  Subsumption          : 0.24
% 5.88/2.18  Abstraction          : 0.05
% 5.88/2.18  MUC search           : 0.00
% 5.88/2.18  Cooper               : 0.00
% 5.88/2.18  Total                : 1.39
% 5.88/2.18  Index Insertion      : 0.00
% 5.88/2.18  Index Deletion       : 0.00
% 5.88/2.18  Index Matching       : 0.00
% 5.88/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
