%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:44 EST 2020

% Result     : Theorem 6.48s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  212 (1607 expanded)
%              Number of leaves         :   23 ( 471 expanded)
%              Depth                    :   13
%              Number of atoms          :  326 (3636 expanded)
%              Number of equality atoms :  117 (2060 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_8441,plain,(
    ! [A_4446,B_4447,C_4448] :
      ( r2_hidden('#skF_2'(A_4446,B_4447,C_4448),A_4446)
      | r2_hidden('#skF_4'(A_4446,B_4447,C_4448),C_4448)
      | k2_zfmisc_1(A_4446,B_4447) = C_4448 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( r2_hidden(k4_tarski(A_39,B_40),k2_zfmisc_1(C_41,D_42))
      | ~ r2_hidden(B_40,D_42)
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8055,plain,(
    ! [A_3914,B_3915,D_3916] :
      ( r2_hidden('#skF_6'(A_3914,B_3915,k2_zfmisc_1(A_3914,B_3915),D_3916),B_3915)
      | ~ r2_hidden(D_3916,k2_zfmisc_1(A_3914,B_3915)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5964,plain,(
    ! [A_3230,B_3231,C_3232] :
      ( r2_hidden('#skF_2'(A_3230,B_3231,C_3232),A_3230)
      | r2_hidden('#skF_4'(A_3230,B_3231,C_3232),C_3232)
      | k2_zfmisc_1(A_3230,B_3231) = C_3232 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_5,B_6,D_32] :
      ( r2_hidden('#skF_6'(A_5,B_6,k2_zfmisc_1(A_5,B_6),D_32),B_6)
      | ~ r2_hidden(D_32,k2_zfmisc_1(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5701,plain,(
    ! [A_2742,B_2743,D_2744] :
      ( r2_hidden('#skF_6'(A_2742,B_2743,k2_zfmisc_1(A_2742,B_2743),D_2744),B_2743)
      | ~ r2_hidden(D_2744,k2_zfmisc_1(A_2742,B_2743)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3024,plain,(
    ! [A_859,B_860,C_861] :
      ( r2_hidden('#skF_3'(A_859,B_860,C_861),B_860)
      | r2_hidden('#skF_4'(A_859,B_860,C_861),C_861)
      | k2_zfmisc_1(A_859,B_860) = C_861 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2553,plain,(
    ! [A_287,B_288,D_289] :
      ( r2_hidden('#skF_6'(A_287,B_288,k2_zfmisc_1(A_287,B_288),D_289),B_288)
      | ~ r2_hidden(D_289,k2_zfmisc_1(A_287,B_288)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1677,plain,(
    ! [A_230,B_231,C_232] :
      ( r2_hidden('#skF_3'(A_230,B_231,C_232),B_231)
      | r2_hidden('#skF_4'(A_230,B_231,C_232),C_232)
      | k2_zfmisc_1(A_230,B_231) = C_232 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1067,plain,(
    ! [A_154,B_155,C_156] :
      ( r2_hidden('#skF_2'(A_154,B_155,C_156),A_154)
      | r2_hidden('#skF_4'(A_154,B_155,C_156),C_156)
      | k2_zfmisc_1(A_154,B_155) = C_156 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_117,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( r2_hidden(k4_tarski(A_70,B_71),k2_zfmisc_1(C_72,D_73))
      | ~ r2_hidden(B_71,D_73)
      | ~ r2_hidden(A_70,C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(k4_tarski(A_70,B_71),k1_xboole_0)
      | ~ r2_hidden(B_71,'#skF_10')
      | ~ r2_hidden(A_70,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_117])).

tff(c_130,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski(A_76,B_77),k1_xboole_0)
      | ~ r2_hidden(B_77,'#skF_10')
      | ~ r2_hidden(A_76,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_117])).

tff(c_14,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_105,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ r2_hidden(A_67,C_68)
      | ~ r2_hidden(A_67,B_69)
      | ~ r2_hidden(A_67,k5_xboole_0(B_69,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [A_67,A_4] :
      ( ~ r2_hidden(A_67,k1_xboole_0)
      | ~ r2_hidden(A_67,A_4)
      | ~ r2_hidden(A_67,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_145,plain,(
    ! [A_78,B_79,A_80] :
      ( ~ r2_hidden(k4_tarski(A_78,B_79),A_80)
      | ~ r2_hidden(B_79,'#skF_10')
      | ~ r2_hidden(A_78,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_130,c_114])).

tff(c_160,plain,(
    ! [B_71,A_70] :
      ( ~ r2_hidden(B_71,'#skF_10')
      | ~ r2_hidden(A_70,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_126,c_145])).

tff(c_164,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_1307,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_2'(A_164,B_165,'#skF_9'),A_164)
      | k2_zfmisc_1(A_164,B_165) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1067,c_164])).

tff(c_1325,plain,(
    ! [B_165] : k2_zfmisc_1('#skF_9',B_165) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1307,c_164])).

tff(c_252,plain,(
    ! [A_108,B_109,D_110] :
      ( r2_hidden('#skF_5'(A_108,B_109,k2_zfmisc_1(A_108,B_109),D_110),A_108)
      | ~ r2_hidden(D_110,k2_zfmisc_1(A_108,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_293,plain,(
    ! [D_110] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_10',k1_xboole_0,D_110),'#skF_9')
      | ~ r2_hidden(D_110,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_252])).

tff(c_304,plain,(
    ! [D_110] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_10',k1_xboole_0,D_110),'#skF_9')
      | ~ r2_hidden(D_110,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_293])).

tff(c_305,plain,(
    ! [D_110] : ~ r2_hidden(D_110,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_304])).

tff(c_1145,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_2'(A_157,B_158,k1_xboole_0),A_157)
      | k2_zfmisc_1(A_157,B_158) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1067,c_305])).

tff(c_1183,plain,(
    ! [B_158] : k2_zfmisc_1('#skF_9',B_158) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1145,c_164])).

tff(c_1328,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1183])).

tff(c_1330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1328])).

tff(c_1331,plain,(
    ! [B_71] : ~ r2_hidden(B_71,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_2432,plain,(
    ! [A_256,B_257] :
      ( r2_hidden('#skF_3'(A_256,B_257,'#skF_10'),B_257)
      | k2_zfmisc_1(A_256,B_257) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1677,c_1331])).

tff(c_1335,plain,(
    ! [A_169,B_170,D_171] :
      ( r2_hidden('#skF_6'(A_169,B_170,k2_zfmisc_1(A_169,B_170),D_171),B_170)
      | ~ r2_hidden(D_171,k2_zfmisc_1(A_169,B_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1356,plain,(
    ! [D_171] :
      ( r2_hidden('#skF_6'('#skF_9','#skF_10',k1_xboole_0,D_171),'#skF_10')
      | ~ r2_hidden(D_171,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1335])).

tff(c_1362,plain,(
    ! [D_171] :
      ( r2_hidden('#skF_6'('#skF_9','#skF_10',k1_xboole_0,D_171),'#skF_10')
      | ~ r2_hidden(D_171,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1356])).

tff(c_1363,plain,(
    ! [D_171] : ~ r2_hidden(D_171,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1331,c_1362])).

tff(c_2479,plain,(
    ! [A_256] : k2_zfmisc_1(A_256,k1_xboole_0) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2432,c_1363])).

tff(c_1960,plain,(
    ! [A_245,B_246] :
      ( r2_hidden('#skF_3'(A_245,B_246,k1_xboole_0),B_246)
      | k2_zfmisc_1(A_245,B_246) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1677,c_1363])).

tff(c_2077,plain,(
    ! [A_245] : k2_zfmisc_1(A_245,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1960,c_1363])).

tff(c_2483,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2479,c_2077])).

tff(c_2485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2483])).

tff(c_2486,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2488,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2486])).

tff(c_2491,plain,(
    ! [A_4] : k5_xboole_0(A_4,'#skF_8') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_14])).

tff(c_2531,plain,(
    ! [A_278,B_279,C_280] :
      ( r2_hidden(A_278,B_279)
      | ~ r2_hidden(A_278,C_280)
      | r2_hidden(A_278,k5_xboole_0(B_279,C_280)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2540,plain,(
    ! [A_278,A_4] :
      ( r2_hidden(A_278,A_4)
      | ~ r2_hidden(A_278,'#skF_8')
      | r2_hidden(A_278,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2491,c_2531])).

tff(c_2568,plain,(
    ! [A_287,D_289,A_4] :
      ( r2_hidden('#skF_6'(A_287,'#skF_8',k2_zfmisc_1(A_287,'#skF_8'),D_289),A_4)
      | ~ r2_hidden(D_289,k2_zfmisc_1(A_287,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2553,c_2540])).

tff(c_2522,plain,(
    ! [A_273,C_274,B_275] :
      ( ~ r2_hidden(A_273,C_274)
      | ~ r2_hidden(A_273,B_275)
      | ~ r2_hidden(A_273,k5_xboole_0(B_275,C_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2528,plain,(
    ! [A_273,A_4] :
      ( ~ r2_hidden(A_273,'#skF_8')
      | ~ r2_hidden(A_273,A_4)
      | ~ r2_hidden(A_273,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2491,c_2522])).

tff(c_2621,plain,(
    ! [A_299,D_300,A_301] :
      ( ~ r2_hidden('#skF_6'(A_299,'#skF_8',k2_zfmisc_1(A_299,'#skF_8'),D_300),A_301)
      | ~ r2_hidden(D_300,k2_zfmisc_1(A_299,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2553,c_2528])).

tff(c_2641,plain,(
    ! [D_302,A_303] : ~ r2_hidden(D_302,k2_zfmisc_1(A_303,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_2568,c_2621])).

tff(c_2656,plain,(
    ! [B_40,A_39,C_41] :
      ( ~ r2_hidden(B_40,'#skF_8')
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(resolution,[status(thm)],[c_40,c_2641])).

tff(c_2657,plain,(
    ! [A_39,C_41] : ~ r2_hidden(A_39,C_41) ),
    inference(splitLeft,[status(thm)],[c_2656])).

tff(c_38,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_4'(A_5,B_6,C_7),C_7)
      | k2_zfmisc_1(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2714,plain,(
    ! [A_309,B_310] : k2_zfmisc_1(A_309,B_310) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_2657,c_2657,c_38])).

tff(c_2699,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(A_5,B_6) = C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_2657,c_2657,c_38])).

tff(c_2838,plain,(
    ! [C_583] : C_583 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2714,c_2699])).

tff(c_2487,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2505,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_2487])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2506,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8'
    | k2_zfmisc_1('#skF_9','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_2488,c_54])).

tff(c_2507,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_2505,c_2506])).

tff(c_2859,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2838,c_2507])).

tff(c_2860,plain,(
    ! [B_40] : ~ r2_hidden(B_40,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2656])).

tff(c_3453,plain,(
    ! [A_905,B_906] :
      ( r2_hidden('#skF_3'(A_905,B_906,'#skF_8'),B_906)
      | k2_zfmisc_1(A_905,B_906) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3024,c_2860])).

tff(c_3535,plain,(
    ! [A_905] : k2_zfmisc_1(A_905,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3453,c_2860])).

tff(c_3548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3535,c_2507])).

tff(c_3549,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2486])).

tff(c_4611,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3549,c_2487])).

tff(c_22,plain,(
    ! [A_5,B_6,D_32] :
      ( r2_hidden('#skF_5'(A_5,B_6,k2_zfmisc_1(A_5,B_6),D_32),A_5)
      | ~ r2_hidden(D_32,k2_zfmisc_1(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3616,plain,(
    ! [A_936,B_937,D_938] :
      ( r2_hidden('#skF_5'(A_936,B_937,k2_zfmisc_1(A_936,B_937),D_938),A_936)
      | ~ r2_hidden(D_938,k2_zfmisc_1(A_936,B_937)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3554,plain,(
    ! [A_4] : k5_xboole_0(A_4,'#skF_7') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3549,c_14])).

tff(c_3582,plain,(
    ! [A_924,C_925,B_926] :
      ( ~ r2_hidden(A_924,C_925)
      | ~ r2_hidden(A_924,B_926)
      | ~ r2_hidden(A_924,k5_xboole_0(B_926,C_925)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3591,plain,(
    ! [A_924,A_4] :
      ( ~ r2_hidden(A_924,'#skF_7')
      | ~ r2_hidden(A_924,A_4)
      | ~ r2_hidden(A_924,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3554,c_3582])).

tff(c_3654,plain,(
    ! [B_942,D_943,A_944] :
      ( ~ r2_hidden('#skF_5'('#skF_7',B_942,k2_zfmisc_1('#skF_7',B_942),D_943),A_944)
      | ~ r2_hidden(D_943,k2_zfmisc_1('#skF_7',B_942)) ) ),
    inference(resolution,[status(thm)],[c_3616,c_3591])).

tff(c_3701,plain,(
    ! [D_948,B_949] : ~ r2_hidden(D_948,k2_zfmisc_1('#skF_7',B_949)) ),
    inference(resolution,[status(thm)],[c_22,c_3654])).

tff(c_3726,plain,(
    ! [B_40,D_42,A_39] :
      ( ~ r2_hidden(B_40,D_42)
      | ~ r2_hidden(A_39,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40,c_3701])).

tff(c_3728,plain,(
    ! [A_950] : ~ r2_hidden(A_950,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3726])).

tff(c_4299,plain,(
    ! [A_1009,B_1010] :
      ( r2_hidden('#skF_2'(A_1009,B_1010,'#skF_7'),A_1009)
      | k2_zfmisc_1(A_1009,B_1010) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_38,c_3728])).

tff(c_3727,plain,(
    ! [A_39] : ~ r2_hidden(A_39,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3726])).

tff(c_4381,plain,(
    ! [B_1010] : k2_zfmisc_1('#skF_7',B_1010) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_4299,c_3727])).

tff(c_3551,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_3560,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3549,c_3551])).

tff(c_4394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4381,c_3560])).

tff(c_4395,plain,(
    ! [B_40,D_42] : ~ r2_hidden(B_40,D_42) ),
    inference(splitRight,[status(thm)],[c_3726])).

tff(c_4446,plain,(
    ! [A_1013,B_1014] : k2_zfmisc_1(A_1013,B_1014) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_4395,c_4395,c_38])).

tff(c_4396,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(A_5,B_6) = C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_4395,c_4395,c_38])).

tff(c_4568,plain,(
    ! [C_1563] : C_1563 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4446,c_4396])).

tff(c_3550,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2486])).

tff(c_3559,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3549,c_3550])).

tff(c_4595,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4568,c_3559])).

tff(c_4596,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4621,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3549,c_4596])).

tff(c_4622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4611,c_4621])).

tff(c_4624,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4626,plain,(
    ! [A_4] : k5_xboole_0(A_4,'#skF_10') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4624,c_14])).

tff(c_5670,plain,(
    ! [A_2728,C_2729,B_2730] :
      ( ~ r2_hidden(A_2728,C_2729)
      | ~ r2_hidden(A_2728,B_2730)
      | ~ r2_hidden(A_2728,k5_xboole_0(B_2730,C_2729)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5676,plain,(
    ! [A_2728,A_4] :
      ( ~ r2_hidden(A_2728,'#skF_10')
      | ~ r2_hidden(A_2728,A_4)
      | ~ r2_hidden(A_2728,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4626,c_5670])).

tff(c_5739,plain,(
    ! [A_2748,D_2749,A_2750] :
      ( ~ r2_hidden('#skF_6'(A_2748,'#skF_10',k2_zfmisc_1(A_2748,'#skF_10'),D_2749),A_2750)
      | ~ r2_hidden(D_2749,k2_zfmisc_1(A_2748,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_5701,c_5676])).

tff(c_5755,plain,(
    ! [D_2751,A_2752] : ~ r2_hidden(D_2751,k2_zfmisc_1(A_2752,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_20,c_5739])).

tff(c_5770,plain,(
    ! [B_40,A_39,C_41] :
      ( ~ r2_hidden(B_40,'#skF_10')
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(resolution,[status(thm)],[c_40,c_5755])).

tff(c_5771,plain,(
    ! [A_39,C_41] : ~ r2_hidden(A_39,C_41) ),
    inference(splitLeft,[status(thm)],[c_5770])).

tff(c_5798,plain,(
    ! [A_2755,B_2756] : k2_zfmisc_1(A_2755,B_2756) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_5771,c_5771,c_38])).

tff(c_5782,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(A_5,B_6) = C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_5771,c_5771,c_38])).

tff(c_5906,plain,(
    ! [C_2992] : C_2992 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_5798,c_5782])).

tff(c_5275,plain,(
    ! [A_2693,B_2694,C_2695] :
      ( r2_hidden('#skF_3'(A_2693,B_2694,C_2695),B_2694)
      | r2_hidden('#skF_4'(A_2693,B_2694,C_2695),C_2695)
      | k2_zfmisc_1(A_2693,B_2694) = C_2695 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4708,plain,(
    ! [A_1932,B_1933,D_1934] :
      ( r2_hidden('#skF_6'(A_1932,B_1933,k2_zfmisc_1(A_1932,B_1933),D_1934),B_1933)
      | ~ r2_hidden(D_1934,k2_zfmisc_1(A_1932,B_1933)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4623,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4631,plain,
    ( '#skF_7' = '#skF_10'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4624,c_4624,c_4623])).

tff(c_4632,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4631])).

tff(c_4649,plain,(
    ! [A_4] : k5_xboole_0(A_4,'#skF_8') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4632,c_4626])).

tff(c_4678,plain,(
    ! [A_1920,C_1921,B_1922] :
      ( ~ r2_hidden(A_1920,C_1921)
      | ~ r2_hidden(A_1920,B_1922)
      | ~ r2_hidden(A_1920,k5_xboole_0(B_1922,C_1921)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4684,plain,(
    ! [A_1920,A_4] :
      ( ~ r2_hidden(A_1920,'#skF_8')
      | ~ r2_hidden(A_1920,A_4)
      | ~ r2_hidden(A_1920,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4649,c_4678])).

tff(c_4746,plain,(
    ! [A_1938,D_1939,A_1940] :
      ( ~ r2_hidden('#skF_6'(A_1938,'#skF_8',k2_zfmisc_1(A_1938,'#skF_8'),D_1939),A_1940)
      | ~ r2_hidden(D_1939,k2_zfmisc_1(A_1938,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_4708,c_4684])).

tff(c_4762,plain,(
    ! [D_1941,A_1942] : ~ r2_hidden(D_1941,k2_zfmisc_1(A_1942,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_20,c_4746])).

tff(c_4777,plain,(
    ! [B_40,A_39,C_41] :
      ( ~ r2_hidden(B_40,'#skF_8')
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(resolution,[status(thm)],[c_40,c_4762])).

tff(c_4778,plain,(
    ! [A_39,C_41] : ~ r2_hidden(A_39,C_41) ),
    inference(splitLeft,[status(thm)],[c_4777])).

tff(c_4807,plain,(
    ! [A_1945,B_1946] : k2_zfmisc_1(A_1945,B_1946) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_4778,c_4778,c_38])).

tff(c_4791,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(A_5,B_6) = C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_4778,c_4778,c_38])).

tff(c_4938,plain,(
    ! [C_2391] : C_2391 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4807,c_4791])).

tff(c_4634,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4632,c_4624])).

tff(c_46,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4639,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4632,c_46])).

tff(c_4640,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4639])).

tff(c_4641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4640,c_4634])).

tff(c_4642,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4639])).

tff(c_4659,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4634,c_4642])).

tff(c_4953,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4938,c_4659])).

tff(c_4954,plain,(
    ! [B_40] : ~ r2_hidden(B_40,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_4777])).

tff(c_5539,plain,(
    ! [A_2711,B_2712] :
      ( r2_hidden('#skF_3'(A_2711,B_2712,'#skF_8'),B_2712)
      | k2_zfmisc_1(A_2711,B_2712) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_5275,c_4954])).

tff(c_5621,plain,(
    ! [A_2711] : k2_zfmisc_1(A_2711,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5539,c_4954])).

tff(c_5634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5621,c_4659])).

tff(c_5635,plain,(
    '#skF_7' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_4631])).

tff(c_5651,plain,(
    k2_zfmisc_1('#skF_10','#skF_8') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4624,c_5635,c_4624,c_46])).

tff(c_5935,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5906,c_5651])).

tff(c_5936,plain,(
    ! [B_40] : ~ r2_hidden(B_40,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_5770])).

tff(c_6863,plain,(
    ! [A_3299,B_3300] :
      ( r2_hidden('#skF_2'(A_3299,B_3300,'#skF_10'),A_3299)
      | k2_zfmisc_1(A_3299,B_3300) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_5964,c_5936])).

tff(c_6891,plain,(
    ! [B_3300] : k2_zfmisc_1('#skF_10',B_3300) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6863,c_5936])).

tff(c_6923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6891,c_5651])).

tff(c_6925,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6926,plain,(
    ! [A_4] : k5_xboole_0(A_4,'#skF_9') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6925,c_14])).

tff(c_8033,plain,(
    ! [A_3905,B_3906,C_3907] :
      ( r2_hidden(A_3905,B_3906)
      | ~ r2_hidden(A_3905,C_3907)
      | r2_hidden(A_3905,k5_xboole_0(B_3906,C_3907)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8042,plain,(
    ! [A_3905,A_4] :
      ( r2_hidden(A_3905,A_4)
      | ~ r2_hidden(A_3905,'#skF_9')
      | r2_hidden(A_3905,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6926,c_8033])).

tff(c_8070,plain,(
    ! [A_3914,D_3916,A_4] :
      ( r2_hidden('#skF_6'(A_3914,'#skF_9',k2_zfmisc_1(A_3914,'#skF_9'),D_3916),A_4)
      | ~ r2_hidden(D_3916,k2_zfmisc_1(A_3914,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_8055,c_8042])).

tff(c_8016,plain,(
    ! [A_3897,C_3898,B_3899] :
      ( ~ r2_hidden(A_3897,C_3898)
      | ~ r2_hidden(A_3897,B_3899)
      | ~ r2_hidden(A_3897,k5_xboole_0(B_3899,C_3898)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8019,plain,(
    ! [A_3897,A_4] :
      ( ~ r2_hidden(A_3897,'#skF_9')
      | ~ r2_hidden(A_3897,A_4)
      | ~ r2_hidden(A_3897,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6926,c_8016])).

tff(c_8123,plain,(
    ! [A_3926,D_3927,A_3928] :
      ( ~ r2_hidden('#skF_6'(A_3926,'#skF_9',k2_zfmisc_1(A_3926,'#skF_9'),D_3927),A_3928)
      | ~ r2_hidden(D_3927,k2_zfmisc_1(A_3926,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_8055,c_8019])).

tff(c_8143,plain,(
    ! [D_3929,A_3930] : ~ r2_hidden(D_3929,k2_zfmisc_1(A_3930,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_8070,c_8123])).

tff(c_8158,plain,(
    ! [B_40,A_39,C_41] :
      ( ~ r2_hidden(B_40,'#skF_9')
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(resolution,[status(thm)],[c_40,c_8143])).

tff(c_8159,plain,(
    ! [A_39,C_41] : ~ r2_hidden(A_39,C_41) ),
    inference(splitLeft,[status(thm)],[c_8158])).

tff(c_8213,plain,(
    ! [A_3936,B_3937,C_3938] : k2_zfmisc_1(A_3936,B_3937) = C_3938 ),
    inference(negUnitSimplification,[status(thm)],[c_8159,c_8159,c_38])).

tff(c_7549,plain,(
    ! [A_3853,B_3854,C_3855] :
      ( r2_hidden('#skF_3'(A_3853,B_3854,C_3855),B_3854)
      | r2_hidden('#skF_4'(A_3853,B_3854,C_3855),C_3855)
      | k2_zfmisc_1(A_3853,B_3854) = C_3855 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7005,plain,(
    ! [A_3333,B_3334,D_3335] :
      ( r2_hidden('#skF_6'(A_3333,B_3334,k2_zfmisc_1(A_3333,B_3334),D_3335),B_3334)
      | ~ r2_hidden(D_3335,k2_zfmisc_1(A_3333,B_3334)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6924,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6931,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6925,c_6925,c_6924])).

tff(c_6932,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_6931])).

tff(c_6945,plain,(
    ! [A_4] : k5_xboole_0(A_4,'#skF_8') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6932,c_6926])).

tff(c_6983,plain,(
    ! [A_3324,B_3325,C_3326] :
      ( r2_hidden(A_3324,B_3325)
      | ~ r2_hidden(A_3324,C_3326)
      | r2_hidden(A_3324,k5_xboole_0(B_3325,C_3326)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6992,plain,(
    ! [A_3324,A_4] :
      ( r2_hidden(A_3324,A_4)
      | ~ r2_hidden(A_3324,'#skF_8')
      | r2_hidden(A_3324,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6945,c_6983])).

tff(c_7020,plain,(
    ! [A_3333,D_3335,A_4] :
      ( r2_hidden('#skF_6'(A_3333,'#skF_8',k2_zfmisc_1(A_3333,'#skF_8'),D_3335),A_4)
      | ~ r2_hidden(D_3335,k2_zfmisc_1(A_3333,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_7005,c_6992])).

tff(c_6966,plain,(
    ! [A_3316,C_3317,B_3318] :
      ( ~ r2_hidden(A_3316,C_3317)
      | ~ r2_hidden(A_3316,B_3318)
      | ~ r2_hidden(A_3316,k5_xboole_0(B_3318,C_3317)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6969,plain,(
    ! [A_3316,A_4] :
      ( ~ r2_hidden(A_3316,'#skF_8')
      | ~ r2_hidden(A_3316,A_4)
      | ~ r2_hidden(A_3316,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6945,c_6966])).

tff(c_7073,plain,(
    ! [A_3345,D_3346,A_3347] :
      ( ~ r2_hidden('#skF_6'(A_3345,'#skF_8',k2_zfmisc_1(A_3345,'#skF_8'),D_3346),A_3347)
      | ~ r2_hidden(D_3346,k2_zfmisc_1(A_3345,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_7005,c_6969])).

tff(c_7093,plain,(
    ! [D_3348,A_3349] : ~ r2_hidden(D_3348,k2_zfmisc_1(A_3349,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_7020,c_7073])).

tff(c_7108,plain,(
    ! [B_40,A_39,C_41] :
      ( ~ r2_hidden(B_40,'#skF_8')
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(resolution,[status(thm)],[c_40,c_7093])).

tff(c_7109,plain,(
    ! [A_39,C_41] : ~ r2_hidden(A_39,C_41) ),
    inference(splitLeft,[status(thm)],[c_7108])).

tff(c_7163,plain,(
    ! [A_3355,B_3356,C_3357] : k2_zfmisc_1(A_3355,B_3356) = C_3357 ),
    inference(negUnitSimplification,[status(thm)],[c_7109,c_7109,c_38])).

tff(c_6935,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6932,c_6925])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6957,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6935,c_6932,c_6935,c_50])).

tff(c_7225,plain,(
    ! [C_3357] : C_3357 != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_7163,c_6957])).

tff(c_7316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7225,c_6935])).

tff(c_7317,plain,(
    ! [B_40] : ~ r2_hidden(B_40,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_7108])).

tff(c_7891,plain,(
    ! [A_3883,B_3884] :
      ( r2_hidden('#skF_3'(A_3883,B_3884,'#skF_8'),B_3884)
      | k2_zfmisc_1(A_3883,B_3884) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_7549,c_7317])).

tff(c_7973,plain,(
    ! [A_3883] : k2_zfmisc_1(A_3883,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7891,c_7317])).

tff(c_7986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7973,c_6957])).

tff(c_7987,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6931])).

tff(c_8005,plain,(
    k2_zfmisc_1('#skF_9','#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6925,c_7987,c_6925,c_50])).

tff(c_8275,plain,(
    ! [C_3938] : C_3938 != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_8213,c_8005])).

tff(c_8364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8275,c_6925])).

tff(c_8365,plain,(
    ! [B_40] : ~ r2_hidden(B_40,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_8158])).

tff(c_9301,plain,(
    ! [A_4506,B_4507] :
      ( r2_hidden('#skF_2'(A_4506,B_4507,'#skF_9'),A_4506)
      | k2_zfmisc_1(A_4506,B_4507) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_8441,c_8365])).

tff(c_9329,plain,(
    ! [B_4507] : k2_zfmisc_1('#skF_9',B_4507) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9301,c_8365])).

tff(c_9341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9329,c_8005])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.48/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.34  
% 6.48/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.34  %$ r2_hidden > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 6.48/2.34  
% 6.48/2.34  %Foreground sorts:
% 6.48/2.34  
% 6.48/2.34  
% 6.48/2.34  %Background operators:
% 6.48/2.34  
% 6.48/2.34  
% 6.48/2.34  %Foreground operators:
% 6.48/2.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.48/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.48/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.48/2.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.48/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.48/2.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.48/2.34  tff('#skF_7', type, '#skF_7': $i).
% 6.48/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.48/2.34  tff('#skF_10', type, '#skF_10': $i).
% 6.48/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.48/2.34  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.48/2.34  tff('#skF_9', type, '#skF_9': $i).
% 6.48/2.34  tff('#skF_8', type, '#skF_8': $i).
% 6.48/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.48/2.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.48/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.48/2.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.48/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.48/2.34  
% 6.77/2.37  tff(f_46, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.77/2.37  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.77/2.37  tff(f_59, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.77/2.37  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.77/2.37  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.77/2.37  tff(c_8441, plain, (![A_4446, B_4447, C_4448]: (r2_hidden('#skF_2'(A_4446, B_4447, C_4448), A_4446) | r2_hidden('#skF_4'(A_4446, B_4447, C_4448), C_4448) | k2_zfmisc_1(A_4446, B_4447)=C_4448)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_40, plain, (![A_39, B_40, C_41, D_42]: (r2_hidden(k4_tarski(A_39, B_40), k2_zfmisc_1(C_41, D_42)) | ~r2_hidden(B_40, D_42) | ~r2_hidden(A_39, C_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.77/2.37  tff(c_8055, plain, (![A_3914, B_3915, D_3916]: (r2_hidden('#skF_6'(A_3914, B_3915, k2_zfmisc_1(A_3914, B_3915), D_3916), B_3915) | ~r2_hidden(D_3916, k2_zfmisc_1(A_3914, B_3915)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_5964, plain, (![A_3230, B_3231, C_3232]: (r2_hidden('#skF_2'(A_3230, B_3231, C_3232), A_3230) | r2_hidden('#skF_4'(A_3230, B_3231, C_3232), C_3232) | k2_zfmisc_1(A_3230, B_3231)=C_3232)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_20, plain, (![A_5, B_6, D_32]: (r2_hidden('#skF_6'(A_5, B_6, k2_zfmisc_1(A_5, B_6), D_32), B_6) | ~r2_hidden(D_32, k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_5701, plain, (![A_2742, B_2743, D_2744]: (r2_hidden('#skF_6'(A_2742, B_2743, k2_zfmisc_1(A_2742, B_2743), D_2744), B_2743) | ~r2_hidden(D_2744, k2_zfmisc_1(A_2742, B_2743)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_3024, plain, (![A_859, B_860, C_861]: (r2_hidden('#skF_3'(A_859, B_860, C_861), B_860) | r2_hidden('#skF_4'(A_859, B_860, C_861), C_861) | k2_zfmisc_1(A_859, B_860)=C_861)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_2553, plain, (![A_287, B_288, D_289]: (r2_hidden('#skF_6'(A_287, B_288, k2_zfmisc_1(A_287, B_288), D_289), B_288) | ~r2_hidden(D_289, k2_zfmisc_1(A_287, B_288)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_48, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.37  tff(c_67, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_48])).
% 6.77/2.37  tff(c_1677, plain, (![A_230, B_231, C_232]: (r2_hidden('#skF_3'(A_230, B_231, C_232), B_231) | r2_hidden('#skF_4'(A_230, B_231, C_232), C_232) | k2_zfmisc_1(A_230, B_231)=C_232)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_52, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.37  tff(c_66, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_52])).
% 6.77/2.37  tff(c_1067, plain, (![A_154, B_155, C_156]: (r2_hidden('#skF_2'(A_154, B_155, C_156), A_154) | r2_hidden('#skF_4'(A_154, B_155, C_156), C_156) | k2_zfmisc_1(A_154, B_155)=C_156)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_56, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.37  tff(c_68, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 6.77/2.37  tff(c_117, plain, (![A_70, B_71, C_72, D_73]: (r2_hidden(k4_tarski(A_70, B_71), k2_zfmisc_1(C_72, D_73)) | ~r2_hidden(B_71, D_73) | ~r2_hidden(A_70, C_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.77/2.37  tff(c_126, plain, (![A_70, B_71]: (r2_hidden(k4_tarski(A_70, B_71), k1_xboole_0) | ~r2_hidden(B_71, '#skF_10') | ~r2_hidden(A_70, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_117])).
% 6.77/2.37  tff(c_130, plain, (![A_76, B_77]: (r2_hidden(k4_tarski(A_76, B_77), k1_xboole_0) | ~r2_hidden(B_77, '#skF_10') | ~r2_hidden(A_76, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_117])).
% 6.77/2.37  tff(c_14, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.77/2.37  tff(c_105, plain, (![A_67, C_68, B_69]: (~r2_hidden(A_67, C_68) | ~r2_hidden(A_67, B_69) | ~r2_hidden(A_67, k5_xboole_0(B_69, C_68)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_114, plain, (![A_67, A_4]: (~r2_hidden(A_67, k1_xboole_0) | ~r2_hidden(A_67, A_4) | ~r2_hidden(A_67, A_4))), inference(superposition, [status(thm), theory('equality')], [c_14, c_105])).
% 6.77/2.37  tff(c_145, plain, (![A_78, B_79, A_80]: (~r2_hidden(k4_tarski(A_78, B_79), A_80) | ~r2_hidden(B_79, '#skF_10') | ~r2_hidden(A_78, '#skF_9'))), inference(resolution, [status(thm)], [c_130, c_114])).
% 6.77/2.37  tff(c_160, plain, (![B_71, A_70]: (~r2_hidden(B_71, '#skF_10') | ~r2_hidden(A_70, '#skF_9'))), inference(resolution, [status(thm)], [c_126, c_145])).
% 6.77/2.37  tff(c_164, plain, (![A_70]: (~r2_hidden(A_70, '#skF_9'))), inference(splitLeft, [status(thm)], [c_160])).
% 6.77/2.37  tff(c_1307, plain, (![A_164, B_165]: (r2_hidden('#skF_2'(A_164, B_165, '#skF_9'), A_164) | k2_zfmisc_1(A_164, B_165)='#skF_9')), inference(resolution, [status(thm)], [c_1067, c_164])).
% 6.77/2.37  tff(c_1325, plain, (![B_165]: (k2_zfmisc_1('#skF_9', B_165)='#skF_9')), inference(resolution, [status(thm)], [c_1307, c_164])).
% 6.77/2.37  tff(c_252, plain, (![A_108, B_109, D_110]: (r2_hidden('#skF_5'(A_108, B_109, k2_zfmisc_1(A_108, B_109), D_110), A_108) | ~r2_hidden(D_110, k2_zfmisc_1(A_108, B_109)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_293, plain, (![D_110]: (r2_hidden('#skF_5'('#skF_9', '#skF_10', k1_xboole_0, D_110), '#skF_9') | ~r2_hidden(D_110, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_252])).
% 6.77/2.37  tff(c_304, plain, (![D_110]: (r2_hidden('#skF_5'('#skF_9', '#skF_10', k1_xboole_0, D_110), '#skF_9') | ~r2_hidden(D_110, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_293])).
% 6.77/2.37  tff(c_305, plain, (![D_110]: (~r2_hidden(D_110, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_164, c_304])).
% 6.77/2.37  tff(c_1145, plain, (![A_157, B_158]: (r2_hidden('#skF_2'(A_157, B_158, k1_xboole_0), A_157) | k2_zfmisc_1(A_157, B_158)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1067, c_305])).
% 6.77/2.37  tff(c_1183, plain, (![B_158]: (k2_zfmisc_1('#skF_9', B_158)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1145, c_164])).
% 6.77/2.37  tff(c_1328, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1183])).
% 6.77/2.37  tff(c_1330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1328])).
% 6.77/2.37  tff(c_1331, plain, (![B_71]: (~r2_hidden(B_71, '#skF_10'))), inference(splitRight, [status(thm)], [c_160])).
% 6.77/2.37  tff(c_2432, plain, (![A_256, B_257]: (r2_hidden('#skF_3'(A_256, B_257, '#skF_10'), B_257) | k2_zfmisc_1(A_256, B_257)='#skF_10')), inference(resolution, [status(thm)], [c_1677, c_1331])).
% 6.77/2.37  tff(c_1335, plain, (![A_169, B_170, D_171]: (r2_hidden('#skF_6'(A_169, B_170, k2_zfmisc_1(A_169, B_170), D_171), B_170) | ~r2_hidden(D_171, k2_zfmisc_1(A_169, B_170)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_1356, plain, (![D_171]: (r2_hidden('#skF_6'('#skF_9', '#skF_10', k1_xboole_0, D_171), '#skF_10') | ~r2_hidden(D_171, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1335])).
% 6.77/2.37  tff(c_1362, plain, (![D_171]: (r2_hidden('#skF_6'('#skF_9', '#skF_10', k1_xboole_0, D_171), '#skF_10') | ~r2_hidden(D_171, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1356])).
% 6.77/2.37  tff(c_1363, plain, (![D_171]: (~r2_hidden(D_171, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1331, c_1362])).
% 6.77/2.37  tff(c_2479, plain, (![A_256]: (k2_zfmisc_1(A_256, k1_xboole_0)='#skF_10')), inference(resolution, [status(thm)], [c_2432, c_1363])).
% 6.77/2.37  tff(c_1960, plain, (![A_245, B_246]: (r2_hidden('#skF_3'(A_245, B_246, k1_xboole_0), B_246) | k2_zfmisc_1(A_245, B_246)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1677, c_1363])).
% 6.77/2.37  tff(c_2077, plain, (![A_245]: (k2_zfmisc_1(A_245, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1960, c_1363])).
% 6.77/2.37  tff(c_2483, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2479, c_2077])).
% 6.77/2.37  tff(c_2485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_2483])).
% 6.77/2.37  tff(c_2486, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_56])).
% 6.77/2.37  tff(c_2488, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_2486])).
% 6.77/2.37  tff(c_2491, plain, (![A_4]: (k5_xboole_0(A_4, '#skF_8')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_14])).
% 6.77/2.37  tff(c_2531, plain, (![A_278, B_279, C_280]: (r2_hidden(A_278, B_279) | ~r2_hidden(A_278, C_280) | r2_hidden(A_278, k5_xboole_0(B_279, C_280)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_2540, plain, (![A_278, A_4]: (r2_hidden(A_278, A_4) | ~r2_hidden(A_278, '#skF_8') | r2_hidden(A_278, A_4))), inference(superposition, [status(thm), theory('equality')], [c_2491, c_2531])).
% 6.77/2.37  tff(c_2568, plain, (![A_287, D_289, A_4]: (r2_hidden('#skF_6'(A_287, '#skF_8', k2_zfmisc_1(A_287, '#skF_8'), D_289), A_4) | ~r2_hidden(D_289, k2_zfmisc_1(A_287, '#skF_8')))), inference(resolution, [status(thm)], [c_2553, c_2540])).
% 6.77/2.37  tff(c_2522, plain, (![A_273, C_274, B_275]: (~r2_hidden(A_273, C_274) | ~r2_hidden(A_273, B_275) | ~r2_hidden(A_273, k5_xboole_0(B_275, C_274)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_2528, plain, (![A_273, A_4]: (~r2_hidden(A_273, '#skF_8') | ~r2_hidden(A_273, A_4) | ~r2_hidden(A_273, A_4))), inference(superposition, [status(thm), theory('equality')], [c_2491, c_2522])).
% 6.77/2.37  tff(c_2621, plain, (![A_299, D_300, A_301]: (~r2_hidden('#skF_6'(A_299, '#skF_8', k2_zfmisc_1(A_299, '#skF_8'), D_300), A_301) | ~r2_hidden(D_300, k2_zfmisc_1(A_299, '#skF_8')))), inference(resolution, [status(thm)], [c_2553, c_2528])).
% 6.77/2.37  tff(c_2641, plain, (![D_302, A_303]: (~r2_hidden(D_302, k2_zfmisc_1(A_303, '#skF_8')))), inference(resolution, [status(thm)], [c_2568, c_2621])).
% 6.77/2.37  tff(c_2656, plain, (![B_40, A_39, C_41]: (~r2_hidden(B_40, '#skF_8') | ~r2_hidden(A_39, C_41))), inference(resolution, [status(thm)], [c_40, c_2641])).
% 6.77/2.37  tff(c_2657, plain, (![A_39, C_41]: (~r2_hidden(A_39, C_41))), inference(splitLeft, [status(thm)], [c_2656])).
% 6.77/2.37  tff(c_38, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_4'(A_5, B_6, C_7), C_7) | k2_zfmisc_1(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_2714, plain, (![A_309, B_310]: (k2_zfmisc_1(A_309, B_310)='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2657, c_2657, c_38])).
% 6.77/2.37  tff(c_2699, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(A_5, B_6)=C_7)), inference(negUnitSimplification, [status(thm)], [c_2657, c_2657, c_38])).
% 6.77/2.37  tff(c_2838, plain, (![C_583]: (C_583='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2714, c_2699])).
% 6.77/2.37  tff(c_2487, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 6.77/2.37  tff(c_2505, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_2487])).
% 6.77/2.37  tff(c_54, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.37  tff(c_2506, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8' | k2_zfmisc_1('#skF_9', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_2488, c_54])).
% 6.77/2.37  tff(c_2507, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_2505, c_2506])).
% 6.77/2.37  tff(c_2859, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2838, c_2507])).
% 6.77/2.37  tff(c_2860, plain, (![B_40]: (~r2_hidden(B_40, '#skF_8'))), inference(splitRight, [status(thm)], [c_2656])).
% 6.77/2.37  tff(c_3453, plain, (![A_905, B_906]: (r2_hidden('#skF_3'(A_905, B_906, '#skF_8'), B_906) | k2_zfmisc_1(A_905, B_906)='#skF_8')), inference(resolution, [status(thm)], [c_3024, c_2860])).
% 6.77/2.37  tff(c_3535, plain, (![A_905]: (k2_zfmisc_1(A_905, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_3453, c_2860])).
% 6.77/2.37  tff(c_3548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3535, c_2507])).
% 6.77/2.37  tff(c_3549, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2486])).
% 6.77/2.37  tff(c_4611, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3549, c_2487])).
% 6.77/2.37  tff(c_22, plain, (![A_5, B_6, D_32]: (r2_hidden('#skF_5'(A_5, B_6, k2_zfmisc_1(A_5, B_6), D_32), A_5) | ~r2_hidden(D_32, k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_3616, plain, (![A_936, B_937, D_938]: (r2_hidden('#skF_5'(A_936, B_937, k2_zfmisc_1(A_936, B_937), D_938), A_936) | ~r2_hidden(D_938, k2_zfmisc_1(A_936, B_937)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_3554, plain, (![A_4]: (k5_xboole_0(A_4, '#skF_7')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_3549, c_14])).
% 6.77/2.37  tff(c_3582, plain, (![A_924, C_925, B_926]: (~r2_hidden(A_924, C_925) | ~r2_hidden(A_924, B_926) | ~r2_hidden(A_924, k5_xboole_0(B_926, C_925)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_3591, plain, (![A_924, A_4]: (~r2_hidden(A_924, '#skF_7') | ~r2_hidden(A_924, A_4) | ~r2_hidden(A_924, A_4))), inference(superposition, [status(thm), theory('equality')], [c_3554, c_3582])).
% 6.77/2.37  tff(c_3654, plain, (![B_942, D_943, A_944]: (~r2_hidden('#skF_5'('#skF_7', B_942, k2_zfmisc_1('#skF_7', B_942), D_943), A_944) | ~r2_hidden(D_943, k2_zfmisc_1('#skF_7', B_942)))), inference(resolution, [status(thm)], [c_3616, c_3591])).
% 6.77/2.37  tff(c_3701, plain, (![D_948, B_949]: (~r2_hidden(D_948, k2_zfmisc_1('#skF_7', B_949)))), inference(resolution, [status(thm)], [c_22, c_3654])).
% 6.77/2.37  tff(c_3726, plain, (![B_40, D_42, A_39]: (~r2_hidden(B_40, D_42) | ~r2_hidden(A_39, '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_3701])).
% 6.77/2.37  tff(c_3728, plain, (![A_950]: (~r2_hidden(A_950, '#skF_7'))), inference(splitLeft, [status(thm)], [c_3726])).
% 6.77/2.37  tff(c_4299, plain, (![A_1009, B_1010]: (r2_hidden('#skF_2'(A_1009, B_1010, '#skF_7'), A_1009) | k2_zfmisc_1(A_1009, B_1010)='#skF_7')), inference(resolution, [status(thm)], [c_38, c_3728])).
% 6.77/2.37  tff(c_3727, plain, (![A_39]: (~r2_hidden(A_39, '#skF_7'))), inference(splitLeft, [status(thm)], [c_3726])).
% 6.77/2.37  tff(c_4381, plain, (![B_1010]: (k2_zfmisc_1('#skF_7', B_1010)='#skF_7')), inference(resolution, [status(thm)], [c_4299, c_3727])).
% 6.77/2.37  tff(c_3551, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 6.77/2.37  tff(c_3560, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3549, c_3551])).
% 6.77/2.37  tff(c_4394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4381, c_3560])).
% 6.77/2.37  tff(c_4395, plain, (![B_40, D_42]: (~r2_hidden(B_40, D_42))), inference(splitRight, [status(thm)], [c_3726])).
% 6.77/2.37  tff(c_4446, plain, (![A_1013, B_1014]: (k2_zfmisc_1(A_1013, B_1014)='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_4395, c_4395, c_38])).
% 6.77/2.37  tff(c_4396, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(A_5, B_6)=C_7)), inference(negUnitSimplification, [status(thm)], [c_4395, c_4395, c_38])).
% 6.77/2.37  tff(c_4568, plain, (![C_1563]: (C_1563='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4446, c_4396])).
% 6.77/2.37  tff(c_3550, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_2486])).
% 6.77/2.37  tff(c_3559, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3549, c_3550])).
% 6.77/2.37  tff(c_4595, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4568, c_3559])).
% 6.77/2.37  tff(c_4596, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 6.77/2.37  tff(c_4621, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3549, c_4596])).
% 6.77/2.37  tff(c_4622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4611, c_4621])).
% 6.77/2.37  tff(c_4624, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_48])).
% 6.77/2.37  tff(c_4626, plain, (![A_4]: (k5_xboole_0(A_4, '#skF_10')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_4624, c_14])).
% 6.77/2.37  tff(c_5670, plain, (![A_2728, C_2729, B_2730]: (~r2_hidden(A_2728, C_2729) | ~r2_hidden(A_2728, B_2730) | ~r2_hidden(A_2728, k5_xboole_0(B_2730, C_2729)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_5676, plain, (![A_2728, A_4]: (~r2_hidden(A_2728, '#skF_10') | ~r2_hidden(A_2728, A_4) | ~r2_hidden(A_2728, A_4))), inference(superposition, [status(thm), theory('equality')], [c_4626, c_5670])).
% 6.77/2.37  tff(c_5739, plain, (![A_2748, D_2749, A_2750]: (~r2_hidden('#skF_6'(A_2748, '#skF_10', k2_zfmisc_1(A_2748, '#skF_10'), D_2749), A_2750) | ~r2_hidden(D_2749, k2_zfmisc_1(A_2748, '#skF_10')))), inference(resolution, [status(thm)], [c_5701, c_5676])).
% 6.77/2.37  tff(c_5755, plain, (![D_2751, A_2752]: (~r2_hidden(D_2751, k2_zfmisc_1(A_2752, '#skF_10')))), inference(resolution, [status(thm)], [c_20, c_5739])).
% 6.77/2.37  tff(c_5770, plain, (![B_40, A_39, C_41]: (~r2_hidden(B_40, '#skF_10') | ~r2_hidden(A_39, C_41))), inference(resolution, [status(thm)], [c_40, c_5755])).
% 6.77/2.37  tff(c_5771, plain, (![A_39, C_41]: (~r2_hidden(A_39, C_41))), inference(splitLeft, [status(thm)], [c_5770])).
% 6.77/2.37  tff(c_5798, plain, (![A_2755, B_2756]: (k2_zfmisc_1(A_2755, B_2756)='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_5771, c_5771, c_38])).
% 6.77/2.37  tff(c_5782, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(A_5, B_6)=C_7)), inference(negUnitSimplification, [status(thm)], [c_5771, c_5771, c_38])).
% 6.77/2.37  tff(c_5906, plain, (![C_2992]: (C_2992='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_5798, c_5782])).
% 6.77/2.37  tff(c_5275, plain, (![A_2693, B_2694, C_2695]: (r2_hidden('#skF_3'(A_2693, B_2694, C_2695), B_2694) | r2_hidden('#skF_4'(A_2693, B_2694, C_2695), C_2695) | k2_zfmisc_1(A_2693, B_2694)=C_2695)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_4708, plain, (![A_1932, B_1933, D_1934]: (r2_hidden('#skF_6'(A_1932, B_1933, k2_zfmisc_1(A_1932, B_1933), D_1934), B_1933) | ~r2_hidden(D_1934, k2_zfmisc_1(A_1932, B_1933)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_4623, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_48])).
% 6.77/2.37  tff(c_4631, plain, ('#skF_7'='#skF_10' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4624, c_4624, c_4623])).
% 6.77/2.37  tff(c_4632, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_4631])).
% 6.77/2.37  tff(c_4649, plain, (![A_4]: (k5_xboole_0(A_4, '#skF_8')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_4632, c_4626])).
% 6.77/2.37  tff(c_4678, plain, (![A_1920, C_1921, B_1922]: (~r2_hidden(A_1920, C_1921) | ~r2_hidden(A_1920, B_1922) | ~r2_hidden(A_1920, k5_xboole_0(B_1922, C_1921)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_4684, plain, (![A_1920, A_4]: (~r2_hidden(A_1920, '#skF_8') | ~r2_hidden(A_1920, A_4) | ~r2_hidden(A_1920, A_4))), inference(superposition, [status(thm), theory('equality')], [c_4649, c_4678])).
% 6.77/2.37  tff(c_4746, plain, (![A_1938, D_1939, A_1940]: (~r2_hidden('#skF_6'(A_1938, '#skF_8', k2_zfmisc_1(A_1938, '#skF_8'), D_1939), A_1940) | ~r2_hidden(D_1939, k2_zfmisc_1(A_1938, '#skF_8')))), inference(resolution, [status(thm)], [c_4708, c_4684])).
% 6.77/2.37  tff(c_4762, plain, (![D_1941, A_1942]: (~r2_hidden(D_1941, k2_zfmisc_1(A_1942, '#skF_8')))), inference(resolution, [status(thm)], [c_20, c_4746])).
% 6.77/2.37  tff(c_4777, plain, (![B_40, A_39, C_41]: (~r2_hidden(B_40, '#skF_8') | ~r2_hidden(A_39, C_41))), inference(resolution, [status(thm)], [c_40, c_4762])).
% 6.77/2.37  tff(c_4778, plain, (![A_39, C_41]: (~r2_hidden(A_39, C_41))), inference(splitLeft, [status(thm)], [c_4777])).
% 6.77/2.37  tff(c_4807, plain, (![A_1945, B_1946]: (k2_zfmisc_1(A_1945, B_1946)='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_4778, c_4778, c_38])).
% 6.77/2.37  tff(c_4791, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(A_5, B_6)=C_7)), inference(negUnitSimplification, [status(thm)], [c_4778, c_4778, c_38])).
% 6.77/2.37  tff(c_4938, plain, (![C_2391]: (C_2391='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4807, c_4791])).
% 6.77/2.37  tff(c_4634, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4632, c_4624])).
% 6.77/2.37  tff(c_46, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.37  tff(c_4639, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4632, c_46])).
% 6.77/2.37  tff(c_4640, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_4639])).
% 6.77/2.37  tff(c_4641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4640, c_4634])).
% 6.77/2.37  tff(c_4642, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_4639])).
% 6.77/2.37  tff(c_4659, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4634, c_4642])).
% 6.77/2.37  tff(c_4953, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4938, c_4659])).
% 6.77/2.37  tff(c_4954, plain, (![B_40]: (~r2_hidden(B_40, '#skF_8'))), inference(splitRight, [status(thm)], [c_4777])).
% 6.77/2.37  tff(c_5539, plain, (![A_2711, B_2712]: (r2_hidden('#skF_3'(A_2711, B_2712, '#skF_8'), B_2712) | k2_zfmisc_1(A_2711, B_2712)='#skF_8')), inference(resolution, [status(thm)], [c_5275, c_4954])).
% 6.77/2.37  tff(c_5621, plain, (![A_2711]: (k2_zfmisc_1(A_2711, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_5539, c_4954])).
% 6.77/2.37  tff(c_5634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5621, c_4659])).
% 6.77/2.37  tff(c_5635, plain, ('#skF_7'='#skF_10'), inference(splitRight, [status(thm)], [c_4631])).
% 6.77/2.37  tff(c_5651, plain, (k2_zfmisc_1('#skF_10', '#skF_8')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_4624, c_5635, c_4624, c_46])).
% 6.77/2.37  tff(c_5935, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5906, c_5651])).
% 6.77/2.37  tff(c_5936, plain, (![B_40]: (~r2_hidden(B_40, '#skF_10'))), inference(splitRight, [status(thm)], [c_5770])).
% 6.77/2.37  tff(c_6863, plain, (![A_3299, B_3300]: (r2_hidden('#skF_2'(A_3299, B_3300, '#skF_10'), A_3299) | k2_zfmisc_1(A_3299, B_3300)='#skF_10')), inference(resolution, [status(thm)], [c_5964, c_5936])).
% 6.77/2.37  tff(c_6891, plain, (![B_3300]: (k2_zfmisc_1('#skF_10', B_3300)='#skF_10')), inference(resolution, [status(thm)], [c_6863, c_5936])).
% 6.77/2.37  tff(c_6923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6891, c_5651])).
% 6.77/2.37  tff(c_6925, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 6.77/2.37  tff(c_6926, plain, (![A_4]: (k5_xboole_0(A_4, '#skF_9')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_6925, c_14])).
% 6.77/2.37  tff(c_8033, plain, (![A_3905, B_3906, C_3907]: (r2_hidden(A_3905, B_3906) | ~r2_hidden(A_3905, C_3907) | r2_hidden(A_3905, k5_xboole_0(B_3906, C_3907)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_8042, plain, (![A_3905, A_4]: (r2_hidden(A_3905, A_4) | ~r2_hidden(A_3905, '#skF_9') | r2_hidden(A_3905, A_4))), inference(superposition, [status(thm), theory('equality')], [c_6926, c_8033])).
% 6.77/2.37  tff(c_8070, plain, (![A_3914, D_3916, A_4]: (r2_hidden('#skF_6'(A_3914, '#skF_9', k2_zfmisc_1(A_3914, '#skF_9'), D_3916), A_4) | ~r2_hidden(D_3916, k2_zfmisc_1(A_3914, '#skF_9')))), inference(resolution, [status(thm)], [c_8055, c_8042])).
% 6.77/2.37  tff(c_8016, plain, (![A_3897, C_3898, B_3899]: (~r2_hidden(A_3897, C_3898) | ~r2_hidden(A_3897, B_3899) | ~r2_hidden(A_3897, k5_xboole_0(B_3899, C_3898)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_8019, plain, (![A_3897, A_4]: (~r2_hidden(A_3897, '#skF_9') | ~r2_hidden(A_3897, A_4) | ~r2_hidden(A_3897, A_4))), inference(superposition, [status(thm), theory('equality')], [c_6926, c_8016])).
% 6.77/2.37  tff(c_8123, plain, (![A_3926, D_3927, A_3928]: (~r2_hidden('#skF_6'(A_3926, '#skF_9', k2_zfmisc_1(A_3926, '#skF_9'), D_3927), A_3928) | ~r2_hidden(D_3927, k2_zfmisc_1(A_3926, '#skF_9')))), inference(resolution, [status(thm)], [c_8055, c_8019])).
% 6.77/2.37  tff(c_8143, plain, (![D_3929, A_3930]: (~r2_hidden(D_3929, k2_zfmisc_1(A_3930, '#skF_9')))), inference(resolution, [status(thm)], [c_8070, c_8123])).
% 6.77/2.37  tff(c_8158, plain, (![B_40, A_39, C_41]: (~r2_hidden(B_40, '#skF_9') | ~r2_hidden(A_39, C_41))), inference(resolution, [status(thm)], [c_40, c_8143])).
% 6.77/2.37  tff(c_8159, plain, (![A_39, C_41]: (~r2_hidden(A_39, C_41))), inference(splitLeft, [status(thm)], [c_8158])).
% 6.77/2.37  tff(c_8213, plain, (![A_3936, B_3937, C_3938]: (k2_zfmisc_1(A_3936, B_3937)=C_3938)), inference(negUnitSimplification, [status(thm)], [c_8159, c_8159, c_38])).
% 6.77/2.37  tff(c_7549, plain, (![A_3853, B_3854, C_3855]: (r2_hidden('#skF_3'(A_3853, B_3854, C_3855), B_3854) | r2_hidden('#skF_4'(A_3853, B_3854, C_3855), C_3855) | k2_zfmisc_1(A_3853, B_3854)=C_3855)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_7005, plain, (![A_3333, B_3334, D_3335]: (r2_hidden('#skF_6'(A_3333, B_3334, k2_zfmisc_1(A_3333, B_3334), D_3335), B_3334) | ~r2_hidden(D_3335, k2_zfmisc_1(A_3333, B_3334)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.77/2.37  tff(c_6924, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_52])).
% 6.77/2.37  tff(c_6931, plain, ('#skF_7'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6925, c_6925, c_6924])).
% 6.77/2.37  tff(c_6932, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_6931])).
% 6.77/2.37  tff(c_6945, plain, (![A_4]: (k5_xboole_0(A_4, '#skF_8')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_6932, c_6926])).
% 6.77/2.37  tff(c_6983, plain, (![A_3324, B_3325, C_3326]: (r2_hidden(A_3324, B_3325) | ~r2_hidden(A_3324, C_3326) | r2_hidden(A_3324, k5_xboole_0(B_3325, C_3326)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_6992, plain, (![A_3324, A_4]: (r2_hidden(A_3324, A_4) | ~r2_hidden(A_3324, '#skF_8') | r2_hidden(A_3324, A_4))), inference(superposition, [status(thm), theory('equality')], [c_6945, c_6983])).
% 6.77/2.37  tff(c_7020, plain, (![A_3333, D_3335, A_4]: (r2_hidden('#skF_6'(A_3333, '#skF_8', k2_zfmisc_1(A_3333, '#skF_8'), D_3335), A_4) | ~r2_hidden(D_3335, k2_zfmisc_1(A_3333, '#skF_8')))), inference(resolution, [status(thm)], [c_7005, c_6992])).
% 6.77/2.37  tff(c_6966, plain, (![A_3316, C_3317, B_3318]: (~r2_hidden(A_3316, C_3317) | ~r2_hidden(A_3316, B_3318) | ~r2_hidden(A_3316, k5_xboole_0(B_3318, C_3317)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.77/2.37  tff(c_6969, plain, (![A_3316, A_4]: (~r2_hidden(A_3316, '#skF_8') | ~r2_hidden(A_3316, A_4) | ~r2_hidden(A_3316, A_4))), inference(superposition, [status(thm), theory('equality')], [c_6945, c_6966])).
% 6.77/2.37  tff(c_7073, plain, (![A_3345, D_3346, A_3347]: (~r2_hidden('#skF_6'(A_3345, '#skF_8', k2_zfmisc_1(A_3345, '#skF_8'), D_3346), A_3347) | ~r2_hidden(D_3346, k2_zfmisc_1(A_3345, '#skF_8')))), inference(resolution, [status(thm)], [c_7005, c_6969])).
% 6.77/2.37  tff(c_7093, plain, (![D_3348, A_3349]: (~r2_hidden(D_3348, k2_zfmisc_1(A_3349, '#skF_8')))), inference(resolution, [status(thm)], [c_7020, c_7073])).
% 6.77/2.37  tff(c_7108, plain, (![B_40, A_39, C_41]: (~r2_hidden(B_40, '#skF_8') | ~r2_hidden(A_39, C_41))), inference(resolution, [status(thm)], [c_40, c_7093])).
% 6.77/2.37  tff(c_7109, plain, (![A_39, C_41]: (~r2_hidden(A_39, C_41))), inference(splitLeft, [status(thm)], [c_7108])).
% 6.77/2.37  tff(c_7163, plain, (![A_3355, B_3356, C_3357]: (k2_zfmisc_1(A_3355, B_3356)=C_3357)), inference(negUnitSimplification, [status(thm)], [c_7109, c_7109, c_38])).
% 6.77/2.37  tff(c_6935, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6932, c_6925])).
% 6.77/2.37  tff(c_50, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.77/2.37  tff(c_6957, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6935, c_6932, c_6935, c_50])).
% 6.77/2.37  tff(c_7225, plain, (![C_3357]: (C_3357!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_7163, c_6957])).
% 6.77/2.37  tff(c_7316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7225, c_6935])).
% 6.77/2.37  tff(c_7317, plain, (![B_40]: (~r2_hidden(B_40, '#skF_8'))), inference(splitRight, [status(thm)], [c_7108])).
% 6.77/2.37  tff(c_7891, plain, (![A_3883, B_3884]: (r2_hidden('#skF_3'(A_3883, B_3884, '#skF_8'), B_3884) | k2_zfmisc_1(A_3883, B_3884)='#skF_8')), inference(resolution, [status(thm)], [c_7549, c_7317])).
% 6.77/2.37  tff(c_7973, plain, (![A_3883]: (k2_zfmisc_1(A_3883, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_7891, c_7317])).
% 6.77/2.37  tff(c_7986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7973, c_6957])).
% 6.77/2.37  tff(c_7987, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_6931])).
% 6.77/2.37  tff(c_8005, plain, (k2_zfmisc_1('#skF_9', '#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6925, c_7987, c_6925, c_50])).
% 6.77/2.37  tff(c_8275, plain, (![C_3938]: (C_3938!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_8213, c_8005])).
% 6.77/2.37  tff(c_8364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8275, c_6925])).
% 6.77/2.37  tff(c_8365, plain, (![B_40]: (~r2_hidden(B_40, '#skF_9'))), inference(splitRight, [status(thm)], [c_8158])).
% 6.77/2.37  tff(c_9301, plain, (![A_4506, B_4507]: (r2_hidden('#skF_2'(A_4506, B_4507, '#skF_9'), A_4506) | k2_zfmisc_1(A_4506, B_4507)='#skF_9')), inference(resolution, [status(thm)], [c_8441, c_8365])).
% 6.77/2.37  tff(c_9329, plain, (![B_4507]: (k2_zfmisc_1('#skF_9', B_4507)='#skF_9')), inference(resolution, [status(thm)], [c_9301, c_8365])).
% 6.77/2.37  tff(c_9341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9329, c_8005])).
% 6.77/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.37  
% 6.77/2.37  Inference rules
% 6.77/2.37  ----------------------
% 6.77/2.37  #Ref     : 0
% 6.77/2.37  #Sup     : 1980
% 6.77/2.37  #Fact    : 0
% 6.77/2.37  #Define  : 0
% 6.77/2.37  #Split   : 17
% 6.77/2.37  #Chain   : 0
% 6.77/2.37  #Close   : 0
% 6.77/2.37  
% 6.77/2.37  Ordering : KBO
% 6.77/2.37  
% 6.77/2.37  Simplification rules
% 6.77/2.37  ----------------------
% 6.77/2.37  #Subsume      : 658
% 6.77/2.37  #Demod        : 452
% 6.77/2.37  #Tautology    : 243
% 6.77/2.37  #SimpNegUnit  : 128
% 6.77/2.37  #BackRed      : 124
% 6.77/2.37  
% 6.77/2.37  #Partial instantiations: 986
% 6.77/2.37  #Strategies tried      : 1
% 6.77/2.37  
% 6.77/2.37  Timing (in seconds)
% 6.77/2.37  ----------------------
% 6.77/2.37  Preprocessing        : 0.31
% 6.77/2.37  Parsing              : 0.15
% 6.77/2.37  CNF conversion       : 0.03
% 6.77/2.37  Main loop            : 1.26
% 6.77/2.37  Inferencing          : 0.53
% 6.77/2.37  Reduction            : 0.32
% 6.77/2.37  Demodulation         : 0.19
% 6.77/2.37  BG Simplification    : 0.06
% 6.77/2.37  Subsumption          : 0.22
% 6.77/2.37  Abstraction          : 0.07
% 6.77/2.37  MUC search           : 0.00
% 6.77/2.37  Cooper               : 0.00
% 6.77/2.37  Total                : 1.63
% 6.77/2.37  Index Insertion      : 0.00
% 6.77/2.38  Index Deletion       : 0.00
% 6.77/2.38  Index Matching       : 0.00
% 6.77/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
