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
% DateTime   : Thu Dec  3 09:53:44 EST 2020

% Result     : Theorem 8.82s
% Output     : CNFRefutation 8.82s
% Verified   : 
% Statistics : Number of formulae       :  226 (6492 expanded)
%              Number of leaves         :   23 (1837 expanded)
%              Depth                    :   19
%              Number of atoms          :  436 (15125 expanded)
%              Number of equality atoms :  157 (9840 expanded)
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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_11844,plain,(
    ! [A_1232,B_1233,C_1234] :
      ( r2_hidden('#skF_2'(A_1232,B_1233,C_1234),A_1232)
      | r2_hidden('#skF_4'(A_1232,B_1233,C_1234),C_1234)
      | k2_zfmisc_1(A_1232,B_1233) = C_1234 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8784,plain,(
    ! [A_895,B_896,C_897] :
      ( r2_hidden('#skF_2'(A_895,B_896,C_897),A_895)
      | r2_hidden('#skF_4'(A_895,B_896,C_897),C_897)
      | k2_zfmisc_1(A_895,B_896) = C_897 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5084,plain,(
    ! [A_506,B_507,C_508] :
      ( r2_hidden('#skF_2'(A_506,B_507,C_508),A_506)
      | r2_hidden('#skF_4'(A_506,B_507,C_508),C_508)
      | k2_zfmisc_1(A_506,B_507) = C_508 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_3'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_4'(A_5,B_6,C_7),C_7)
      | k2_zfmisc_1(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2702,plain,(
    ! [A_272,B_273,C_274] :
      ( r2_hidden('#skF_2'(A_272,B_273,C_274),A_272)
      | r2_hidden('#skF_4'(A_272,B_273,C_274),C_274)
      | k2_zfmisc_1(A_272,B_273) = C_274 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1863,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_hidden('#skF_2'(A_194,B_195,C_196),A_194)
      | r2_hidden('#skF_4'(A_194,B_195,C_196),C_196)
      | k2_zfmisc_1(A_194,B_195) = C_196 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1073,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden('#skF_3'(A_150,B_151,C_152),B_151)
      | r2_hidden('#skF_4'(A_150,B_151,C_152),C_152)
      | k2_zfmisc_1(A_150,B_151) = C_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_115,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( r2_hidden(k4_tarski(A_70,B_71),k2_zfmisc_1(C_72,D_73))
      | ~ r2_hidden(B_71,D_73)
      | ~ r2_hidden(A_70,C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(k4_tarski(A_70,B_71),k1_xboole_0)
      | ~ r2_hidden(B_71,'#skF_10')
      | ~ r2_hidden(A_70,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_115])).

tff(c_137,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski(A_76,B_77),k1_xboole_0)
      | ~ r2_hidden(B_77,'#skF_10')
      | ~ r2_hidden(A_76,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_115])).

tff(c_14,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_103,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ r2_hidden(A_67,C_68)
      | ~ r2_hidden(A_67,B_69)
      | ~ r2_hidden(A_67,k5_xboole_0(B_69,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [A_67,A_4] :
      ( ~ r2_hidden(A_67,A_4)
      | ~ r2_hidden(A_67,A_4)
      | ~ r2_hidden(A_67,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_103])).

tff(c_152,plain,(
    ! [A_78,B_79] :
      ( ~ r2_hidden(k4_tarski(A_78,B_79),k1_xboole_0)
      | ~ r2_hidden(B_79,'#skF_10')
      | ~ r2_hidden(A_78,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_137,c_112])).

tff(c_156,plain,(
    ! [B_71,A_70] :
      ( ~ r2_hidden(B_71,'#skF_10')
      | ~ r2_hidden(A_70,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_124,c_152])).

tff(c_157,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_1655,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_3'(A_165,B_166,'#skF_9'),B_166)
      | k2_zfmisc_1(A_165,B_166) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1073,c_157])).

tff(c_1673,plain,(
    ! [A_165] : k2_zfmisc_1(A_165,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1655,c_157])).

tff(c_247,plain,(
    ! [A_107,B_108,D_109] :
      ( r2_hidden('#skF_5'(A_107,B_108,k2_zfmisc_1(A_107,B_108),D_109),A_107)
      | ~ r2_hidden(D_109,k2_zfmisc_1(A_107,B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_287,plain,(
    ! [D_109] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_10',k1_xboole_0,D_109),'#skF_9')
      | ~ r2_hidden(D_109,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_247])).

tff(c_298,plain,(
    ! [D_109] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_10',k1_xboole_0,D_109),'#skF_9')
      | ~ r2_hidden(D_109,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_287])).

tff(c_299,plain,(
    ! [D_109] : ~ r2_hidden(D_109,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_298])).

tff(c_1432,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_3'(A_158,B_159,k1_xboole_0),B_159)
      | k2_zfmisc_1(A_158,B_159) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1073,c_299])).

tff(c_1485,plain,(
    ! [A_158] : k2_zfmisc_1(A_158,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1432,c_157])).

tff(c_1676,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1673,c_1485])).

tff(c_1678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1676])).

tff(c_1679,plain,(
    ! [B_71] : ~ r2_hidden(B_71,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_2385,plain,(
    ! [A_217,B_218] :
      ( r2_hidden('#skF_2'(A_217,B_218,'#skF_10'),A_217)
      | k2_zfmisc_1(A_217,B_218) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1863,c_1679])).

tff(c_1683,plain,(
    ! [A_170,B_171,D_172] :
      ( r2_hidden('#skF_6'(A_170,B_171,k2_zfmisc_1(A_170,B_171),D_172),B_171)
      | ~ r2_hidden(D_172,k2_zfmisc_1(A_170,B_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1703,plain,(
    ! [D_172] :
      ( r2_hidden('#skF_6'('#skF_9','#skF_10',k1_xboole_0,D_172),'#skF_10')
      | ~ r2_hidden(D_172,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1683])).

tff(c_1709,plain,(
    ! [D_172] :
      ( r2_hidden('#skF_6'('#skF_9','#skF_10',k1_xboole_0,D_172),'#skF_10')
      | ~ r2_hidden(D_172,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1703])).

tff(c_1710,plain,(
    ! [D_172] : ~ r2_hidden(D_172,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1679,c_1709])).

tff(c_2422,plain,(
    ! [B_218] : k2_zfmisc_1(k1_xboole_0,B_218) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2385,c_1710])).

tff(c_2050,plain,(
    ! [A_206,B_207] :
      ( r2_hidden('#skF_2'(A_206,B_207,k1_xboole_0),A_206)
      | k2_zfmisc_1(A_206,B_207) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1863,c_1710])).

tff(c_2117,plain,(
    ! [B_207] : k2_zfmisc_1(k1_xboole_0,B_207) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2050,c_1710])).

tff(c_2426,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_2117])).

tff(c_2428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_2426])).

tff(c_2429,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2431,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2429])).

tff(c_2434,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_14])).

tff(c_2451,plain,(
    ! [A_228,B_229,C_230] :
      ( r2_hidden(A_228,B_229)
      | r2_hidden(A_228,C_230)
      | ~ r2_hidden(A_228,k5_xboole_0(B_229,C_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2454,plain,(
    ! [A_228,A_4] :
      ( r2_hidden(A_228,A_4)
      | r2_hidden(A_228,A_4)
      | ~ r2_hidden(A_228,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2434,c_2451])).

tff(c_2752,plain,(
    ! [A_272,B_273,A_4] :
      ( r2_hidden('#skF_4'(A_272,B_273,'#skF_8'),A_4)
      | r2_hidden('#skF_2'(A_272,B_273,'#skF_8'),A_272)
      | k2_zfmisc_1(A_272,B_273) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_2702,c_2454])).

tff(c_2464,plain,(
    ! [A_236,C_237,B_238] :
      ( ~ r2_hidden(A_236,C_237)
      | ~ r2_hidden(A_236,B_238)
      | ~ r2_hidden(A_236,k5_xboole_0(B_238,C_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2470,plain,(
    ! [A_236,A_4] :
      ( ~ r2_hidden(A_236,A_4)
      | ~ r2_hidden(A_236,A_4)
      | ~ r2_hidden(A_236,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2434,c_2464])).

tff(c_3177,plain,(
    ! [A_330,B_331,C_332] :
      ( ~ r2_hidden('#skF_4'(A_330,B_331,C_332),C_332)
      | ~ r2_hidden('#skF_4'(A_330,B_331,C_332),'#skF_8')
      | r2_hidden('#skF_2'(A_330,B_331,C_332),A_330)
      | k2_zfmisc_1(A_330,B_331) = C_332 ) ),
    inference(resolution,[status(thm)],[c_2702,c_2470])).

tff(c_3214,plain,(
    ! [A_333,B_334] :
      ( ~ r2_hidden('#skF_4'(A_333,B_334,'#skF_8'),'#skF_8')
      | r2_hidden('#skF_2'(A_333,B_334,'#skF_8'),A_333)
      | k2_zfmisc_1(A_333,B_334) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_2752,c_3177])).

tff(c_3243,plain,(
    ! [A_272,B_273] :
      ( r2_hidden('#skF_2'(A_272,B_273,'#skF_8'),A_272)
      | k2_zfmisc_1(A_272,B_273) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_2752,c_3214])).

tff(c_3247,plain,(
    ! [A_335,B_336] :
      ( r2_hidden('#skF_2'(A_335,B_336,'#skF_8'),A_335)
      | k2_zfmisc_1(A_335,B_336) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_2752,c_3214])).

tff(c_3281,plain,(
    ! [B_336,A_4] :
      ( r2_hidden('#skF_2'('#skF_8',B_336,'#skF_8'),A_4)
      | k2_zfmisc_1('#skF_8',B_336) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3247,c_2454])).

tff(c_3375,plain,(
    ! [A_350,B_351] :
      ( ~ r2_hidden('#skF_2'(A_350,B_351,'#skF_8'),A_350)
      | ~ r2_hidden('#skF_2'(A_350,B_351,'#skF_8'),'#skF_8')
      | k2_zfmisc_1(A_350,B_351) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3247,c_2470])).

tff(c_3395,plain,(
    ! [B_352] :
      ( ~ r2_hidden('#skF_2'('#skF_8',B_352,'#skF_8'),'#skF_8')
      | k2_zfmisc_1('#skF_8',B_352) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3281,c_3375])).

tff(c_3416,plain,(
    ! [B_358] : k2_zfmisc_1('#skF_8',B_358) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3281,c_3395])).

tff(c_40,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( r2_hidden(k4_tarski(A_39,B_40),k2_zfmisc_1(C_41,D_42))
      | ~ r2_hidden(B_40,D_42)
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3590,plain,(
    ! [A_378,B_379,B_380] :
      ( r2_hidden(k4_tarski(A_378,B_379),'#skF_8')
      | ~ r2_hidden(B_379,B_380)
      | ~ r2_hidden(A_378,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3416,c_40])).

tff(c_4319,plain,(
    ! [A_423,A_424,B_425] :
      ( r2_hidden(k4_tarski(A_423,'#skF_2'(A_424,B_425,'#skF_8')),'#skF_8')
      | ~ r2_hidden(A_423,'#skF_8')
      | k2_zfmisc_1(A_424,B_425) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3243,c_3590])).

tff(c_42,plain,(
    ! [B_40,D_42,A_39,C_41] :
      ( r2_hidden(B_40,D_42)
      | ~ r2_hidden(k4_tarski(A_39,B_40),k2_zfmisc_1(C_41,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3444,plain,(
    ! [B_40,B_358,A_39] :
      ( r2_hidden(B_40,B_358)
      | ~ r2_hidden(k4_tarski(A_39,B_40),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3416,c_42])).

tff(c_4335,plain,(
    ! [A_424,B_425,B_358,A_423] :
      ( r2_hidden('#skF_2'(A_424,B_425,'#skF_8'),B_358)
      | ~ r2_hidden(A_423,'#skF_8')
      | k2_zfmisc_1(A_424,B_425) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_4319,c_3444])).

tff(c_4344,plain,(
    ! [A_426] : ~ r2_hidden(A_426,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4335])).

tff(c_4733,plain,(
    ! [A_446,B_447] :
      ( r2_hidden('#skF_3'(A_446,B_447,'#skF_8'),B_447)
      | k2_zfmisc_1(A_446,B_447) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_36,c_4344])).

tff(c_4339,plain,(
    ! [A_423] : ~ r2_hidden(A_423,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4335])).

tff(c_4767,plain,(
    ! [A_446] : k2_zfmisc_1(A_446,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4733,c_4339])).

tff(c_2430,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2446,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2430])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2447,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8'
    | k2_zfmisc_1('#skF_9','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_54])).

tff(c_2448,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_2446,c_2447])).

tff(c_4781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4767,c_2448])).

tff(c_4783,plain,(
    ! [A_448,B_449,B_450] :
      ( r2_hidden('#skF_2'(A_448,B_449,'#skF_8'),B_450)
      | k2_zfmisc_1(A_448,B_449) = '#skF_8' ) ),
    inference(splitRight,[status(thm)],[c_4335])).

tff(c_3391,plain,(
    ! [A_272,B_273] :
      ( ~ r2_hidden('#skF_2'(A_272,B_273,'#skF_8'),'#skF_8')
      | k2_zfmisc_1(A_272,B_273) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3243,c_3375])).

tff(c_4818,plain,(
    ! [A_448,B_449] : k2_zfmisc_1(A_448,B_449) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4783,c_3391])).

tff(c_4862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4818,c_2448])).

tff(c_4863,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2429])).

tff(c_4867,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4863,c_14])).

tff(c_4885,plain,(
    ! [A_465,B_466,C_467] :
      ( r2_hidden(A_465,B_466)
      | r2_hidden(A_465,C_467)
      | ~ r2_hidden(A_465,k5_xboole_0(B_466,C_467)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4888,plain,(
    ! [A_465,A_4] :
      ( r2_hidden(A_465,A_4)
      | r2_hidden(A_465,A_4)
      | ~ r2_hidden(A_465,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4867,c_4885])).

tff(c_5134,plain,(
    ! [A_506,B_507,A_4] :
      ( r2_hidden('#skF_4'(A_506,B_507,'#skF_7'),A_4)
      | r2_hidden('#skF_2'(A_506,B_507,'#skF_7'),A_506)
      | k2_zfmisc_1(A_506,B_507) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5084,c_4888])).

tff(c_38,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_4'(A_5,B_6,C_7),C_7)
      | k2_zfmisc_1(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4906,plain,(
    ! [A_476,C_477,B_478] :
      ( ~ r2_hidden(A_476,C_477)
      | ~ r2_hidden(A_476,B_478)
      | ~ r2_hidden(A_476,k5_xboole_0(B_478,C_477)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4915,plain,(
    ! [A_476,A_4] :
      ( ~ r2_hidden(A_476,A_4)
      | ~ r2_hidden(A_476,A_4)
      | ~ r2_hidden(A_476,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4867,c_4906])).

tff(c_5624,plain,(
    ! [A_565,B_566,C_567] :
      ( ~ r2_hidden('#skF_4'(A_565,B_566,C_567),C_567)
      | ~ r2_hidden('#skF_4'(A_565,B_566,C_567),'#skF_7')
      | r2_hidden('#skF_2'(A_565,B_566,C_567),A_565)
      | k2_zfmisc_1(A_565,B_566) = C_567 ) ),
    inference(resolution,[status(thm)],[c_5084,c_4915])).

tff(c_5666,plain,(
    ! [A_573,B_574,C_575] :
      ( ~ r2_hidden('#skF_4'(A_573,B_574,C_575),'#skF_7')
      | r2_hidden('#skF_2'(A_573,B_574,C_575),A_573)
      | k2_zfmisc_1(A_573,B_574) = C_575 ) ),
    inference(resolution,[status(thm)],[c_38,c_5624])).

tff(c_5699,plain,(
    ! [A_576,B_577] :
      ( r2_hidden('#skF_2'(A_576,B_577,'#skF_7'),A_576)
      | k2_zfmisc_1(A_576,B_577) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5134,c_5666])).

tff(c_5733,plain,(
    ! [B_577,A_4] :
      ( r2_hidden('#skF_2'('#skF_7',B_577,'#skF_7'),A_4)
      | k2_zfmisc_1('#skF_7',B_577) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5699,c_4888])).

tff(c_5785,plain,(
    ! [A_590,B_591] :
      ( ~ r2_hidden('#skF_2'(A_590,B_591,'#skF_7'),A_590)
      | ~ r2_hidden('#skF_2'(A_590,B_591,'#skF_7'),'#skF_7')
      | k2_zfmisc_1(A_590,B_591) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5699,c_4915])).

tff(c_5805,plain,(
    ! [B_592] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_592,'#skF_7'),'#skF_7')
      | k2_zfmisc_1('#skF_7',B_592) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_5733,c_5785])).

tff(c_5816,plain,(
    ! [B_577] : k2_zfmisc_1('#skF_7',B_577) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5733,c_5805])).

tff(c_4873,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != '#skF_7'
    | k2_zfmisc_1('#skF_9','#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4863,c_4863,c_54])).

tff(c_4874,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4873])).

tff(c_5823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5816,c_4874])).

tff(c_5824,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4873])).

tff(c_5842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5824,c_4863,c_2430])).

tff(c_5844,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5846,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5844,c_14])).

tff(c_8564,plain,(
    ! [A_863,B_864,C_865] :
      ( r2_hidden(A_863,B_864)
      | r2_hidden(A_863,C_865)
      | ~ r2_hidden(A_863,k5_xboole_0(B_864,C_865)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8573,plain,(
    ! [A_863,A_4] :
      ( r2_hidden(A_863,A_4)
      | r2_hidden(A_863,A_4)
      | ~ r2_hidden(A_863,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5846,c_8564])).

tff(c_8832,plain,(
    ! [A_895,B_896,A_4] :
      ( r2_hidden('#skF_4'(A_895,B_896,'#skF_10'),A_4)
      | r2_hidden('#skF_2'(A_895,B_896,'#skF_10'),A_895)
      | k2_zfmisc_1(A_895,B_896) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_8784,c_8573])).

tff(c_8552,plain,(
    ! [A_860,C_861,B_862] :
      ( ~ r2_hidden(A_860,C_861)
      | ~ r2_hidden(A_860,B_862)
      | ~ r2_hidden(A_860,k5_xboole_0(B_862,C_861)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8561,plain,(
    ! [A_860,A_4] :
      ( ~ r2_hidden(A_860,A_4)
      | ~ r2_hidden(A_860,A_4)
      | ~ r2_hidden(A_860,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5846,c_8552])).

tff(c_9104,plain,(
    ! [A_931,B_932,C_933] :
      ( ~ r2_hidden('#skF_4'(A_931,B_932,C_933),C_933)
      | ~ r2_hidden('#skF_4'(A_931,B_932,C_933),'#skF_10')
      | r2_hidden('#skF_2'(A_931,B_932,C_933),A_931)
      | k2_zfmisc_1(A_931,B_932) = C_933 ) ),
    inference(resolution,[status(thm)],[c_8784,c_8561])).

tff(c_9127,plain,(
    ! [A_934,B_935] :
      ( ~ r2_hidden('#skF_4'(A_934,B_935,'#skF_10'),'#skF_10')
      | r2_hidden('#skF_2'(A_934,B_935,'#skF_10'),A_934)
      | k2_zfmisc_1(A_934,B_935) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_8832,c_9104])).

tff(c_9144,plain,(
    ! [A_936,B_937] :
      ( r2_hidden('#skF_2'(A_936,B_937,'#skF_10'),A_936)
      | k2_zfmisc_1(A_936,B_937) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_8832,c_9127])).

tff(c_9176,plain,(
    ! [B_937,A_4] :
      ( r2_hidden('#skF_2'('#skF_10',B_937,'#skF_10'),A_4)
      | k2_zfmisc_1('#skF_10',B_937) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_9144,c_8573])).

tff(c_9243,plain,(
    ! [A_953,B_954] :
      ( ~ r2_hidden('#skF_2'(A_953,B_954,'#skF_10'),A_953)
      | ~ r2_hidden('#skF_2'(A_953,B_954,'#skF_10'),'#skF_10')
      | k2_zfmisc_1(A_953,B_954) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_9144,c_8561])).

tff(c_9263,plain,(
    ! [B_955] :
      ( ~ r2_hidden('#skF_2'('#skF_10',B_955,'#skF_10'),'#skF_10')
      | k2_zfmisc_1('#skF_10',B_955) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_9176,c_9243])).

tff(c_9274,plain,(
    ! [B_937] : k2_zfmisc_1('#skF_10',B_937) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_9176,c_9263])).

tff(c_6129,plain,(
    ! [A_647,B_648,C_649] :
      ( r2_hidden('#skF_2'(A_647,B_648,C_649),A_647)
      | r2_hidden('#skF_4'(A_647,B_648,C_649),C_649)
      | k2_zfmisc_1(A_647,B_648) = C_649 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5843,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5851,plain,
    ( '#skF_7' = '#skF_10'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5844,c_5844,c_5843])).

tff(c_5852,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5851])).

tff(c_5863,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5852,c_5846])).

tff(c_5905,plain,(
    ! [A_614,B_615,C_616] :
      ( r2_hidden(A_614,B_615)
      | r2_hidden(A_614,C_616)
      | ~ r2_hidden(A_614,k5_xboole_0(B_615,C_616)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5914,plain,(
    ! [A_614,A_4] :
      ( r2_hidden(A_614,A_4)
      | r2_hidden(A_614,A_4)
      | ~ r2_hidden(A_614,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5863,c_5905])).

tff(c_6177,plain,(
    ! [A_647,B_648,A_4] :
      ( r2_hidden('#skF_4'(A_647,B_648,'#skF_8'),A_4)
      | r2_hidden('#skF_2'(A_647,B_648,'#skF_8'),A_647)
      | k2_zfmisc_1(A_647,B_648) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6129,c_5914])).

tff(c_5886,plain,(
    ! [A_609,C_610,B_611] :
      ( ~ r2_hidden(A_609,C_610)
      | ~ r2_hidden(A_609,B_611)
      | ~ r2_hidden(A_609,k5_xboole_0(B_611,C_610)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5895,plain,(
    ! [A_609,A_4] :
      ( ~ r2_hidden(A_609,A_4)
      | ~ r2_hidden(A_609,A_4)
      | ~ r2_hidden(A_609,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5863,c_5886])).

tff(c_6617,plain,(
    ! [A_703,B_704,C_705] :
      ( ~ r2_hidden('#skF_4'(A_703,B_704,C_705),C_705)
      | ~ r2_hidden('#skF_4'(A_703,B_704,C_705),'#skF_8')
      | r2_hidden('#skF_2'(A_703,B_704,C_705),A_703)
      | k2_zfmisc_1(A_703,B_704) = C_705 ) ),
    inference(resolution,[status(thm)],[c_6129,c_5895])).

tff(c_6663,plain,(
    ! [A_711,B_712] :
      ( ~ r2_hidden('#skF_4'(A_711,B_712,'#skF_8'),'#skF_8')
      | r2_hidden('#skF_2'(A_711,B_712,'#skF_8'),A_711)
      | k2_zfmisc_1(A_711,B_712) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6177,c_6617])).

tff(c_6692,plain,(
    ! [A_647,B_648] :
      ( r2_hidden('#skF_2'(A_647,B_648,'#skF_8'),A_647)
      | k2_zfmisc_1(A_647,B_648) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6177,c_6663])).

tff(c_6696,plain,(
    ! [A_713,B_714] :
      ( r2_hidden('#skF_2'(A_713,B_714,'#skF_8'),A_713)
      | k2_zfmisc_1(A_713,B_714) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6177,c_6663])).

tff(c_6728,plain,(
    ! [B_714,A_4] :
      ( r2_hidden('#skF_2'('#skF_8',B_714,'#skF_8'),A_4)
      | k2_zfmisc_1('#skF_8',B_714) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6696,c_5914])).

tff(c_6807,plain,(
    ! [A_730,B_731] :
      ( ~ r2_hidden('#skF_2'(A_730,B_731,'#skF_8'),A_730)
      | ~ r2_hidden('#skF_2'(A_730,B_731,'#skF_8'),'#skF_8')
      | k2_zfmisc_1(A_730,B_731) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6696,c_5895])).

tff(c_6827,plain,(
    ! [B_732] :
      ( ~ r2_hidden('#skF_2'('#skF_8',B_732,'#skF_8'),'#skF_8')
      | k2_zfmisc_1('#skF_8',B_732) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6728,c_6807])).

tff(c_6861,plain,(
    ! [B_736] : k2_zfmisc_1('#skF_8',B_736) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6728,c_6827])).

tff(c_6965,plain,(
    ! [A_752,B_753,B_754] :
      ( r2_hidden(k4_tarski(A_752,B_753),'#skF_8')
      | ~ r2_hidden(B_753,B_754)
      | ~ r2_hidden(A_752,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6861,c_40])).

tff(c_7878,plain,(
    ! [A_813,A_814,B_815] :
      ( r2_hidden(k4_tarski(A_813,'#skF_2'(A_814,B_815,'#skF_8')),'#skF_8')
      | ~ r2_hidden(A_813,'#skF_8')
      | k2_zfmisc_1(A_814,B_815) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6692,c_6965])).

tff(c_6889,plain,(
    ! [B_40,B_736,A_39] :
      ( r2_hidden(B_40,B_736)
      | ~ r2_hidden(k4_tarski(A_39,B_40),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6861,c_42])).

tff(c_7897,plain,(
    ! [A_814,B_815,B_736,A_813] :
      ( r2_hidden('#skF_2'(A_814,B_815,'#skF_8'),B_736)
      | ~ r2_hidden(A_813,'#skF_8')
      | k2_zfmisc_1(A_814,B_815) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_7878,c_6889])).

tff(c_7907,plain,(
    ! [A_816] : ~ r2_hidden(A_816,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_7897])).

tff(c_8311,plain,(
    ! [A_835,B_836] :
      ( r2_hidden('#skF_3'(A_835,B_836,'#skF_8'),B_836)
      | k2_zfmisc_1(A_835,B_836) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_36,c_7907])).

tff(c_7901,plain,(
    ! [A_813] : ~ r2_hidden(A_813,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_7897])).

tff(c_8345,plain,(
    ! [A_835] : k2_zfmisc_1(A_835,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8311,c_7901])).

tff(c_5854,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5852,c_5844])).

tff(c_46,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5872,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5854,c_5852,c_5854,c_46])).

tff(c_8442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8345,c_5872])).

tff(c_8444,plain,(
    ! [A_842,B_843,B_844] :
      ( r2_hidden('#skF_2'(A_842,B_843,'#skF_8'),B_844)
      | k2_zfmisc_1(A_842,B_843) = '#skF_8' ) ),
    inference(splitRight,[status(thm)],[c_7897])).

tff(c_6823,plain,(
    ! [A_647,B_648] :
      ( ~ r2_hidden('#skF_2'(A_647,B_648,'#skF_8'),'#skF_8')
      | k2_zfmisc_1(A_647,B_648) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_6692,c_6807])).

tff(c_8482,plain,(
    ! [A_842,B_843] : k2_zfmisc_1(A_842,B_843) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8444,c_6823])).

tff(c_8522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8482,c_5872])).

tff(c_8523,plain,(
    '#skF_7' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_5851])).

tff(c_8537,plain,(
    k2_zfmisc_1('#skF_10','#skF_8') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5844,c_8523,c_5844,c_46])).

tff(c_9281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9274,c_8537])).

tff(c_9283,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9285,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9283,c_14])).

tff(c_11645,plain,(
    ! [A_1191,B_1192,C_1193] :
      ( r2_hidden(A_1191,B_1192)
      | r2_hidden(A_1191,C_1193)
      | ~ r2_hidden(A_1191,k5_xboole_0(B_1192,C_1193)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_11648,plain,(
    ! [A_1191,A_4] :
      ( r2_hidden(A_1191,A_4)
      | r2_hidden(A_1191,A_4)
      | ~ r2_hidden(A_1191,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9285,c_11645])).

tff(c_11893,plain,(
    ! [A_1232,B_1233,A_4] :
      ( r2_hidden('#skF_4'(A_1232,B_1233,'#skF_9'),A_4)
      | r2_hidden('#skF_2'(A_1232,B_1233,'#skF_9'),A_1232)
      | k2_zfmisc_1(A_1232,B_1233) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_11844,c_11648])).

tff(c_11649,plain,(
    ! [A_1194,C_1195,B_1196] :
      ( ~ r2_hidden(A_1194,C_1195)
      | ~ r2_hidden(A_1194,B_1196)
      | ~ r2_hidden(A_1194,k5_xboole_0(B_1196,C_1195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_11652,plain,(
    ! [A_1194,A_4] :
      ( ~ r2_hidden(A_1194,A_4)
      | ~ r2_hidden(A_1194,A_4)
      | ~ r2_hidden(A_1194,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9285,c_11649])).

tff(c_12386,plain,(
    ! [A_1296,B_1297,C_1298] :
      ( ~ r2_hidden('#skF_4'(A_1296,B_1297,C_1298),C_1298)
      | ~ r2_hidden('#skF_4'(A_1296,B_1297,C_1298),'#skF_9')
      | r2_hidden('#skF_2'(A_1296,B_1297,C_1298),A_1296)
      | k2_zfmisc_1(A_1296,B_1297) = C_1298 ) ),
    inference(resolution,[status(thm)],[c_11844,c_11652])).

tff(c_12423,plain,(
    ! [A_1299,B_1300] :
      ( ~ r2_hidden('#skF_4'(A_1299,B_1300,'#skF_9'),'#skF_9')
      | r2_hidden('#skF_2'(A_1299,B_1300,'#skF_9'),A_1299)
      | k2_zfmisc_1(A_1299,B_1300) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_11893,c_12386])).

tff(c_12456,plain,(
    ! [A_1301,B_1302] :
      ( r2_hidden('#skF_2'(A_1301,B_1302,'#skF_9'),A_1301)
      | k2_zfmisc_1(A_1301,B_1302) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_11893,c_12423])).

tff(c_12489,plain,(
    ! [B_1302,A_4] :
      ( r2_hidden('#skF_2'('#skF_9',B_1302,'#skF_9'),A_4)
      | k2_zfmisc_1('#skF_9',B_1302) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_12456,c_11648])).

tff(c_12501,plain,(
    ! [B_1308,A_1309] :
      ( r2_hidden('#skF_2'('#skF_9',B_1308,'#skF_9'),A_1309)
      | k2_zfmisc_1('#skF_9',B_1308) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_12456,c_11648])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( ~ r2_hidden(A_1,C_3)
      | ~ r2_hidden(A_1,B_2)
      | ~ r2_hidden(A_1,k5_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12571,plain,(
    ! [B_1318,C_1319,B_1320] :
      ( ~ r2_hidden('#skF_2'('#skF_9',B_1318,'#skF_9'),C_1319)
      | ~ r2_hidden('#skF_2'('#skF_9',B_1318,'#skF_9'),B_1320)
      | k2_zfmisc_1('#skF_9',B_1318) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_12501,c_2])).

tff(c_12588,plain,(
    ! [B_1321,B_1322] :
      ( ~ r2_hidden('#skF_2'('#skF_9',B_1321,'#skF_9'),B_1322)
      | k2_zfmisc_1('#skF_9',B_1321) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_12489,c_12571])).

tff(c_12606,plain,(
    ! [B_1302] : k2_zfmisc_1('#skF_9',B_1302) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_12489,c_12588])).

tff(c_9517,plain,(
    ! [A_1006,B_1007,C_1008] :
      ( r2_hidden('#skF_2'(A_1006,B_1007,C_1008),A_1006)
      | r2_hidden('#skF_4'(A_1006,B_1007,C_1008),C_1008)
      | k2_zfmisc_1(A_1006,B_1007) = C_1008 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9282,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9291,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9283,c_9283,c_9282])).

tff(c_9292,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_9291])).

tff(c_9303,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9292,c_9285])).

tff(c_9323,plain,(
    ! [A_970,B_971,C_972] :
      ( r2_hidden(A_970,B_971)
      | r2_hidden(A_970,C_972)
      | ~ r2_hidden(A_970,k5_xboole_0(B_971,C_972)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9326,plain,(
    ! [A_970,A_4] :
      ( r2_hidden(A_970,A_4)
      | r2_hidden(A_970,A_4)
      | ~ r2_hidden(A_970,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9303,c_9323])).

tff(c_9565,plain,(
    ! [A_1006,B_1007,A_4] :
      ( r2_hidden('#skF_4'(A_1006,B_1007,'#skF_8'),A_4)
      | r2_hidden('#skF_2'(A_1006,B_1007,'#skF_8'),A_1006)
      | k2_zfmisc_1(A_1006,B_1007) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9517,c_9326])).

tff(c_9318,plain,(
    ! [A_965,C_966,B_967] :
      ( ~ r2_hidden(A_965,C_966)
      | ~ r2_hidden(A_965,B_967)
      | ~ r2_hidden(A_965,k5_xboole_0(B_967,C_966)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9321,plain,(
    ! [A_965,A_4] :
      ( ~ r2_hidden(A_965,A_4)
      | ~ r2_hidden(A_965,A_4)
      | ~ r2_hidden(A_965,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9303,c_9318])).

tff(c_9970,plain,(
    ! [A_1056,B_1057,C_1058] :
      ( ~ r2_hidden('#skF_4'(A_1056,B_1057,C_1058),C_1058)
      | ~ r2_hidden('#skF_4'(A_1056,B_1057,C_1058),'#skF_8')
      | r2_hidden('#skF_2'(A_1056,B_1057,C_1058),A_1056)
      | k2_zfmisc_1(A_1056,B_1057) = C_1058 ) ),
    inference(resolution,[status(thm)],[c_9517,c_9321])).

tff(c_10000,plain,(
    ! [A_1059,B_1060] :
      ( ~ r2_hidden('#skF_4'(A_1059,B_1060,'#skF_8'),'#skF_8')
      | r2_hidden('#skF_2'(A_1059,B_1060,'#skF_8'),A_1059)
      | k2_zfmisc_1(A_1059,B_1060) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9565,c_9970])).

tff(c_10022,plain,(
    ! [A_1006,B_1007] :
      ( r2_hidden('#skF_2'(A_1006,B_1007,'#skF_8'),A_1006)
      | k2_zfmisc_1(A_1006,B_1007) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9565,c_10000])).

tff(c_10025,plain,(
    ! [A_1061,B_1062] :
      ( r2_hidden('#skF_2'(A_1061,B_1062,'#skF_8'),A_1061)
      | k2_zfmisc_1(A_1061,B_1062) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9565,c_10000])).

tff(c_10057,plain,(
    ! [B_1062,A_4] :
      ( r2_hidden('#skF_2'('#skF_8',B_1062,'#skF_8'),A_4)
      | k2_zfmisc_1('#skF_8',B_1062) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_10025,c_9326])).

tff(c_10132,plain,(
    ! [A_1078,B_1079] :
      ( ~ r2_hidden('#skF_2'(A_1078,B_1079,'#skF_8'),A_1078)
      | ~ r2_hidden('#skF_2'(A_1078,B_1079,'#skF_8'),'#skF_8')
      | k2_zfmisc_1(A_1078,B_1079) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_10025,c_9321])).

tff(c_10152,plain,(
    ! [B_1080] :
      ( ~ r2_hidden('#skF_2'('#skF_8',B_1080,'#skF_8'),'#skF_8')
      | k2_zfmisc_1('#skF_8',B_1080) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_10057,c_10132])).

tff(c_10168,plain,(
    ! [B_1081] : k2_zfmisc_1('#skF_8',B_1081) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10057,c_10152])).

tff(c_10227,plain,(
    ! [A_1092,B_1093,B_1094] :
      ( r2_hidden(k4_tarski(A_1092,B_1093),'#skF_8')
      | ~ r2_hidden(B_1093,B_1094)
      | ~ r2_hidden(A_1092,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10168,c_40])).

tff(c_11067,plain,(
    ! [A_1154,A_1155,B_1156] :
      ( r2_hidden(k4_tarski(A_1154,'#skF_2'(A_1155,B_1156,'#skF_8')),'#skF_8')
      | ~ r2_hidden(A_1154,'#skF_8')
      | k2_zfmisc_1(A_1155,B_1156) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_10022,c_10227])).

tff(c_10196,plain,(
    ! [B_40,B_1081,A_39] :
      ( r2_hidden(B_40,B_1081)
      | ~ r2_hidden(k4_tarski(A_39,B_40),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10168,c_42])).

tff(c_11082,plain,(
    ! [A_1155,B_1156,B_1081,A_1154] :
      ( r2_hidden('#skF_2'(A_1155,B_1156,'#skF_8'),B_1081)
      | ~ r2_hidden(A_1154,'#skF_8')
      | k2_zfmisc_1(A_1155,B_1156) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_11067,c_10196])).

tff(c_11094,plain,(
    ! [A_1157] : ~ r2_hidden(A_1157,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_11082])).

tff(c_11501,plain,(
    ! [A_1177,B_1178] :
      ( r2_hidden('#skF_3'(A_1177,B_1178,'#skF_8'),B_1178)
      | k2_zfmisc_1(A_1177,B_1178) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_36,c_11094])).

tff(c_11088,plain,(
    ! [A_1154] : ~ r2_hidden(A_1154,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_11082])).

tff(c_11535,plain,(
    ! [A_1177] : k2_zfmisc_1(A_1177,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_11501,c_11088])).

tff(c_9294,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9292,c_9283])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9312,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9294,c_9292,c_9294,c_50])).

tff(c_11549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11535,c_9312])).

tff(c_11551,plain,(
    ! [A_1179,B_1180,B_1181] :
      ( r2_hidden('#skF_2'(A_1179,B_1180,'#skF_8'),B_1181)
      | k2_zfmisc_1(A_1179,B_1180) = '#skF_8' ) ),
    inference(splitRight,[status(thm)],[c_11082])).

tff(c_10148,plain,(
    ! [A_1006,B_1007] :
      ( ~ r2_hidden('#skF_2'(A_1006,B_1007,'#skF_8'),'#skF_8')
      | k2_zfmisc_1(A_1006,B_1007) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_10022,c_10132])).

tff(c_11585,plain,(
    ! [A_1179,B_1180] : k2_zfmisc_1(A_1179,B_1180) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_11551,c_10148])).

tff(c_11623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11585,c_9312])).

tff(c_11624,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_9291])).

tff(c_11638,plain,(
    k2_zfmisc_1('#skF_9','#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9283,c_11624,c_9283,c_50])).

tff(c_12615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12606,c_11638])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.82/2.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.82/2.95  
% 8.82/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.82/2.96  %$ r2_hidden > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 8.82/2.96  
% 8.82/2.96  %Foreground sorts:
% 8.82/2.96  
% 8.82/2.96  
% 8.82/2.96  %Background operators:
% 8.82/2.96  
% 8.82/2.96  
% 8.82/2.96  %Foreground operators:
% 8.82/2.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.82/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.82/2.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.82/2.96  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.82/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.82/2.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.82/2.96  tff('#skF_7', type, '#skF_7': $i).
% 8.82/2.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.82/2.96  tff('#skF_10', type, '#skF_10': $i).
% 8.82/2.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.82/2.96  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 8.82/2.96  tff('#skF_9', type, '#skF_9': $i).
% 8.82/2.96  tff('#skF_8', type, '#skF_8': $i).
% 8.82/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.82/2.96  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 8.82/2.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.82/2.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.82/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.82/2.96  
% 8.82/2.99  tff(f_46, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.82/2.99  tff(f_59, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.82/2.99  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.82/2.99  tff(f_34, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.82/2.99  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.82/2.99  tff(c_11844, plain, (![A_1232, B_1233, C_1234]: (r2_hidden('#skF_2'(A_1232, B_1233, C_1234), A_1232) | r2_hidden('#skF_4'(A_1232, B_1233, C_1234), C_1234) | k2_zfmisc_1(A_1232, B_1233)=C_1234)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_8784, plain, (![A_895, B_896, C_897]: (r2_hidden('#skF_2'(A_895, B_896, C_897), A_895) | r2_hidden('#skF_4'(A_895, B_896, C_897), C_897) | k2_zfmisc_1(A_895, B_896)=C_897)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_5084, plain, (![A_506, B_507, C_508]: (r2_hidden('#skF_2'(A_506, B_507, C_508), A_506) | r2_hidden('#skF_4'(A_506, B_507, C_508), C_508) | k2_zfmisc_1(A_506, B_507)=C_508)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_36, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_3'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_4'(A_5, B_6, C_7), C_7) | k2_zfmisc_1(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_2702, plain, (![A_272, B_273, C_274]: (r2_hidden('#skF_2'(A_272, B_273, C_274), A_272) | r2_hidden('#skF_4'(A_272, B_273, C_274), C_274) | k2_zfmisc_1(A_272, B_273)=C_274)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_48, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.82/2.99  tff(c_65, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_48])).
% 8.82/2.99  tff(c_1863, plain, (![A_194, B_195, C_196]: (r2_hidden('#skF_2'(A_194, B_195, C_196), A_194) | r2_hidden('#skF_4'(A_194, B_195, C_196), C_196) | k2_zfmisc_1(A_194, B_195)=C_196)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_52, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.82/2.99  tff(c_64, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_52])).
% 8.82/2.99  tff(c_1073, plain, (![A_150, B_151, C_152]: (r2_hidden('#skF_3'(A_150, B_151, C_152), B_151) | r2_hidden('#skF_4'(A_150, B_151, C_152), C_152) | k2_zfmisc_1(A_150, B_151)=C_152)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_56, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.82/2.99  tff(c_66, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 8.82/2.99  tff(c_115, plain, (![A_70, B_71, C_72, D_73]: (r2_hidden(k4_tarski(A_70, B_71), k2_zfmisc_1(C_72, D_73)) | ~r2_hidden(B_71, D_73) | ~r2_hidden(A_70, C_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.82/2.99  tff(c_124, plain, (![A_70, B_71]: (r2_hidden(k4_tarski(A_70, B_71), k1_xboole_0) | ~r2_hidden(B_71, '#skF_10') | ~r2_hidden(A_70, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_115])).
% 8.82/2.99  tff(c_137, plain, (![A_76, B_77]: (r2_hidden(k4_tarski(A_76, B_77), k1_xboole_0) | ~r2_hidden(B_77, '#skF_10') | ~r2_hidden(A_76, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_115])).
% 8.82/2.99  tff(c_14, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.82/2.99  tff(c_103, plain, (![A_67, C_68, B_69]: (~r2_hidden(A_67, C_68) | ~r2_hidden(A_67, B_69) | ~r2_hidden(A_67, k5_xboole_0(B_69, C_68)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_112, plain, (![A_67, A_4]: (~r2_hidden(A_67, A_4) | ~r2_hidden(A_67, A_4) | ~r2_hidden(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_103])).
% 8.82/2.99  tff(c_152, plain, (![A_78, B_79]: (~r2_hidden(k4_tarski(A_78, B_79), k1_xboole_0) | ~r2_hidden(B_79, '#skF_10') | ~r2_hidden(A_78, '#skF_9'))), inference(resolution, [status(thm)], [c_137, c_112])).
% 8.82/2.99  tff(c_156, plain, (![B_71, A_70]: (~r2_hidden(B_71, '#skF_10') | ~r2_hidden(A_70, '#skF_9'))), inference(resolution, [status(thm)], [c_124, c_152])).
% 8.82/2.99  tff(c_157, plain, (![A_70]: (~r2_hidden(A_70, '#skF_9'))), inference(splitLeft, [status(thm)], [c_156])).
% 8.82/2.99  tff(c_1655, plain, (![A_165, B_166]: (r2_hidden('#skF_3'(A_165, B_166, '#skF_9'), B_166) | k2_zfmisc_1(A_165, B_166)='#skF_9')), inference(resolution, [status(thm)], [c_1073, c_157])).
% 8.82/2.99  tff(c_1673, plain, (![A_165]: (k2_zfmisc_1(A_165, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_1655, c_157])).
% 8.82/2.99  tff(c_247, plain, (![A_107, B_108, D_109]: (r2_hidden('#skF_5'(A_107, B_108, k2_zfmisc_1(A_107, B_108), D_109), A_107) | ~r2_hidden(D_109, k2_zfmisc_1(A_107, B_108)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_287, plain, (![D_109]: (r2_hidden('#skF_5'('#skF_9', '#skF_10', k1_xboole_0, D_109), '#skF_9') | ~r2_hidden(D_109, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_247])).
% 8.82/2.99  tff(c_298, plain, (![D_109]: (r2_hidden('#skF_5'('#skF_9', '#skF_10', k1_xboole_0, D_109), '#skF_9') | ~r2_hidden(D_109, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_287])).
% 8.82/2.99  tff(c_299, plain, (![D_109]: (~r2_hidden(D_109, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_157, c_298])).
% 8.82/2.99  tff(c_1432, plain, (![A_158, B_159]: (r2_hidden('#skF_3'(A_158, B_159, k1_xboole_0), B_159) | k2_zfmisc_1(A_158, B_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1073, c_299])).
% 8.82/2.99  tff(c_1485, plain, (![A_158]: (k2_zfmisc_1(A_158, '#skF_9')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1432, c_157])).
% 8.82/2.99  tff(c_1676, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1673, c_1485])).
% 8.82/2.99  tff(c_1678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1676])).
% 8.82/2.99  tff(c_1679, plain, (![B_71]: (~r2_hidden(B_71, '#skF_10'))), inference(splitRight, [status(thm)], [c_156])).
% 8.82/2.99  tff(c_2385, plain, (![A_217, B_218]: (r2_hidden('#skF_2'(A_217, B_218, '#skF_10'), A_217) | k2_zfmisc_1(A_217, B_218)='#skF_10')), inference(resolution, [status(thm)], [c_1863, c_1679])).
% 8.82/2.99  tff(c_1683, plain, (![A_170, B_171, D_172]: (r2_hidden('#skF_6'(A_170, B_171, k2_zfmisc_1(A_170, B_171), D_172), B_171) | ~r2_hidden(D_172, k2_zfmisc_1(A_170, B_171)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_1703, plain, (![D_172]: (r2_hidden('#skF_6'('#skF_9', '#skF_10', k1_xboole_0, D_172), '#skF_10') | ~r2_hidden(D_172, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1683])).
% 8.82/2.99  tff(c_1709, plain, (![D_172]: (r2_hidden('#skF_6'('#skF_9', '#skF_10', k1_xboole_0, D_172), '#skF_10') | ~r2_hidden(D_172, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1703])).
% 8.82/2.99  tff(c_1710, plain, (![D_172]: (~r2_hidden(D_172, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1679, c_1709])).
% 8.82/2.99  tff(c_2422, plain, (![B_218]: (k2_zfmisc_1(k1_xboole_0, B_218)='#skF_10')), inference(resolution, [status(thm)], [c_2385, c_1710])).
% 8.82/2.99  tff(c_2050, plain, (![A_206, B_207]: (r2_hidden('#skF_2'(A_206, B_207, k1_xboole_0), A_206) | k2_zfmisc_1(A_206, B_207)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1863, c_1710])).
% 8.82/2.99  tff(c_2117, plain, (![B_207]: (k2_zfmisc_1(k1_xboole_0, B_207)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2050, c_1710])).
% 8.82/2.99  tff(c_2426, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_2117])).
% 8.82/2.99  tff(c_2428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_2426])).
% 8.82/2.99  tff(c_2429, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_56])).
% 8.82/2.99  tff(c_2431, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_2429])).
% 8.82/2.99  tff(c_2434, plain, (![A_4]: (k5_xboole_0(A_4, A_4)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_14])).
% 8.82/2.99  tff(c_2451, plain, (![A_228, B_229, C_230]: (r2_hidden(A_228, B_229) | r2_hidden(A_228, C_230) | ~r2_hidden(A_228, k5_xboole_0(B_229, C_230)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_2454, plain, (![A_228, A_4]: (r2_hidden(A_228, A_4) | r2_hidden(A_228, A_4) | ~r2_hidden(A_228, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2434, c_2451])).
% 8.82/2.99  tff(c_2752, plain, (![A_272, B_273, A_4]: (r2_hidden('#skF_4'(A_272, B_273, '#skF_8'), A_4) | r2_hidden('#skF_2'(A_272, B_273, '#skF_8'), A_272) | k2_zfmisc_1(A_272, B_273)='#skF_8')), inference(resolution, [status(thm)], [c_2702, c_2454])).
% 8.82/2.99  tff(c_2464, plain, (![A_236, C_237, B_238]: (~r2_hidden(A_236, C_237) | ~r2_hidden(A_236, B_238) | ~r2_hidden(A_236, k5_xboole_0(B_238, C_237)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_2470, plain, (![A_236, A_4]: (~r2_hidden(A_236, A_4) | ~r2_hidden(A_236, A_4) | ~r2_hidden(A_236, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2434, c_2464])).
% 8.82/2.99  tff(c_3177, plain, (![A_330, B_331, C_332]: (~r2_hidden('#skF_4'(A_330, B_331, C_332), C_332) | ~r2_hidden('#skF_4'(A_330, B_331, C_332), '#skF_8') | r2_hidden('#skF_2'(A_330, B_331, C_332), A_330) | k2_zfmisc_1(A_330, B_331)=C_332)), inference(resolution, [status(thm)], [c_2702, c_2470])).
% 8.82/2.99  tff(c_3214, plain, (![A_333, B_334]: (~r2_hidden('#skF_4'(A_333, B_334, '#skF_8'), '#skF_8') | r2_hidden('#skF_2'(A_333, B_334, '#skF_8'), A_333) | k2_zfmisc_1(A_333, B_334)='#skF_8')), inference(resolution, [status(thm)], [c_2752, c_3177])).
% 8.82/2.99  tff(c_3243, plain, (![A_272, B_273]: (r2_hidden('#skF_2'(A_272, B_273, '#skF_8'), A_272) | k2_zfmisc_1(A_272, B_273)='#skF_8')), inference(resolution, [status(thm)], [c_2752, c_3214])).
% 8.82/2.99  tff(c_3247, plain, (![A_335, B_336]: (r2_hidden('#skF_2'(A_335, B_336, '#skF_8'), A_335) | k2_zfmisc_1(A_335, B_336)='#skF_8')), inference(resolution, [status(thm)], [c_2752, c_3214])).
% 8.82/2.99  tff(c_3281, plain, (![B_336, A_4]: (r2_hidden('#skF_2'('#skF_8', B_336, '#skF_8'), A_4) | k2_zfmisc_1('#skF_8', B_336)='#skF_8')), inference(resolution, [status(thm)], [c_3247, c_2454])).
% 8.82/2.99  tff(c_3375, plain, (![A_350, B_351]: (~r2_hidden('#skF_2'(A_350, B_351, '#skF_8'), A_350) | ~r2_hidden('#skF_2'(A_350, B_351, '#skF_8'), '#skF_8') | k2_zfmisc_1(A_350, B_351)='#skF_8')), inference(resolution, [status(thm)], [c_3247, c_2470])).
% 8.82/2.99  tff(c_3395, plain, (![B_352]: (~r2_hidden('#skF_2'('#skF_8', B_352, '#skF_8'), '#skF_8') | k2_zfmisc_1('#skF_8', B_352)='#skF_8')), inference(resolution, [status(thm)], [c_3281, c_3375])).
% 8.82/2.99  tff(c_3416, plain, (![B_358]: (k2_zfmisc_1('#skF_8', B_358)='#skF_8')), inference(resolution, [status(thm)], [c_3281, c_3395])).
% 8.82/2.99  tff(c_40, plain, (![A_39, B_40, C_41, D_42]: (r2_hidden(k4_tarski(A_39, B_40), k2_zfmisc_1(C_41, D_42)) | ~r2_hidden(B_40, D_42) | ~r2_hidden(A_39, C_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.82/2.99  tff(c_3590, plain, (![A_378, B_379, B_380]: (r2_hidden(k4_tarski(A_378, B_379), '#skF_8') | ~r2_hidden(B_379, B_380) | ~r2_hidden(A_378, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3416, c_40])).
% 8.82/2.99  tff(c_4319, plain, (![A_423, A_424, B_425]: (r2_hidden(k4_tarski(A_423, '#skF_2'(A_424, B_425, '#skF_8')), '#skF_8') | ~r2_hidden(A_423, '#skF_8') | k2_zfmisc_1(A_424, B_425)='#skF_8')), inference(resolution, [status(thm)], [c_3243, c_3590])).
% 8.82/2.99  tff(c_42, plain, (![B_40, D_42, A_39, C_41]: (r2_hidden(B_40, D_42) | ~r2_hidden(k4_tarski(A_39, B_40), k2_zfmisc_1(C_41, D_42)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.82/2.99  tff(c_3444, plain, (![B_40, B_358, A_39]: (r2_hidden(B_40, B_358) | ~r2_hidden(k4_tarski(A_39, B_40), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3416, c_42])).
% 8.82/2.99  tff(c_4335, plain, (![A_424, B_425, B_358, A_423]: (r2_hidden('#skF_2'(A_424, B_425, '#skF_8'), B_358) | ~r2_hidden(A_423, '#skF_8') | k2_zfmisc_1(A_424, B_425)='#skF_8')), inference(resolution, [status(thm)], [c_4319, c_3444])).
% 8.82/2.99  tff(c_4344, plain, (![A_426]: (~r2_hidden(A_426, '#skF_8'))), inference(splitLeft, [status(thm)], [c_4335])).
% 8.82/2.99  tff(c_4733, plain, (![A_446, B_447]: (r2_hidden('#skF_3'(A_446, B_447, '#skF_8'), B_447) | k2_zfmisc_1(A_446, B_447)='#skF_8')), inference(resolution, [status(thm)], [c_36, c_4344])).
% 8.82/2.99  tff(c_4339, plain, (![A_423]: (~r2_hidden(A_423, '#skF_8'))), inference(splitLeft, [status(thm)], [c_4335])).
% 8.82/2.99  tff(c_4767, plain, (![A_446]: (k2_zfmisc_1(A_446, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_4733, c_4339])).
% 8.82/2.99  tff(c_2430, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 8.82/2.99  tff(c_2446, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2430])).
% 8.82/2.99  tff(c_54, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.82/2.99  tff(c_2447, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8' | k2_zfmisc_1('#skF_9', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_54])).
% 8.82/2.99  tff(c_2448, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_2446, c_2447])).
% 8.82/2.99  tff(c_4781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4767, c_2448])).
% 8.82/2.99  tff(c_4783, plain, (![A_448, B_449, B_450]: (r2_hidden('#skF_2'(A_448, B_449, '#skF_8'), B_450) | k2_zfmisc_1(A_448, B_449)='#skF_8')), inference(splitRight, [status(thm)], [c_4335])).
% 8.82/2.99  tff(c_3391, plain, (![A_272, B_273]: (~r2_hidden('#skF_2'(A_272, B_273, '#skF_8'), '#skF_8') | k2_zfmisc_1(A_272, B_273)='#skF_8')), inference(resolution, [status(thm)], [c_3243, c_3375])).
% 8.82/2.99  tff(c_4818, plain, (![A_448, B_449]: (k2_zfmisc_1(A_448, B_449)='#skF_8')), inference(resolution, [status(thm)], [c_4783, c_3391])).
% 8.82/2.99  tff(c_4862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4818, c_2448])).
% 8.82/2.99  tff(c_4863, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2429])).
% 8.82/2.99  tff(c_4867, plain, (![A_4]: (k5_xboole_0(A_4, A_4)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4863, c_14])).
% 8.82/2.99  tff(c_4885, plain, (![A_465, B_466, C_467]: (r2_hidden(A_465, B_466) | r2_hidden(A_465, C_467) | ~r2_hidden(A_465, k5_xboole_0(B_466, C_467)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_4888, plain, (![A_465, A_4]: (r2_hidden(A_465, A_4) | r2_hidden(A_465, A_4) | ~r2_hidden(A_465, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4867, c_4885])).
% 8.82/2.99  tff(c_5134, plain, (![A_506, B_507, A_4]: (r2_hidden('#skF_4'(A_506, B_507, '#skF_7'), A_4) | r2_hidden('#skF_2'(A_506, B_507, '#skF_7'), A_506) | k2_zfmisc_1(A_506, B_507)='#skF_7')), inference(resolution, [status(thm)], [c_5084, c_4888])).
% 8.82/2.99  tff(c_38, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_4'(A_5, B_6, C_7), C_7) | k2_zfmisc_1(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_4906, plain, (![A_476, C_477, B_478]: (~r2_hidden(A_476, C_477) | ~r2_hidden(A_476, B_478) | ~r2_hidden(A_476, k5_xboole_0(B_478, C_477)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_4915, plain, (![A_476, A_4]: (~r2_hidden(A_476, A_4) | ~r2_hidden(A_476, A_4) | ~r2_hidden(A_476, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4867, c_4906])).
% 8.82/2.99  tff(c_5624, plain, (![A_565, B_566, C_567]: (~r2_hidden('#skF_4'(A_565, B_566, C_567), C_567) | ~r2_hidden('#skF_4'(A_565, B_566, C_567), '#skF_7') | r2_hidden('#skF_2'(A_565, B_566, C_567), A_565) | k2_zfmisc_1(A_565, B_566)=C_567)), inference(resolution, [status(thm)], [c_5084, c_4915])).
% 8.82/2.99  tff(c_5666, plain, (![A_573, B_574, C_575]: (~r2_hidden('#skF_4'(A_573, B_574, C_575), '#skF_7') | r2_hidden('#skF_2'(A_573, B_574, C_575), A_573) | k2_zfmisc_1(A_573, B_574)=C_575)), inference(resolution, [status(thm)], [c_38, c_5624])).
% 8.82/2.99  tff(c_5699, plain, (![A_576, B_577]: (r2_hidden('#skF_2'(A_576, B_577, '#skF_7'), A_576) | k2_zfmisc_1(A_576, B_577)='#skF_7')), inference(resolution, [status(thm)], [c_5134, c_5666])).
% 8.82/2.99  tff(c_5733, plain, (![B_577, A_4]: (r2_hidden('#skF_2'('#skF_7', B_577, '#skF_7'), A_4) | k2_zfmisc_1('#skF_7', B_577)='#skF_7')), inference(resolution, [status(thm)], [c_5699, c_4888])).
% 8.82/2.99  tff(c_5785, plain, (![A_590, B_591]: (~r2_hidden('#skF_2'(A_590, B_591, '#skF_7'), A_590) | ~r2_hidden('#skF_2'(A_590, B_591, '#skF_7'), '#skF_7') | k2_zfmisc_1(A_590, B_591)='#skF_7')), inference(resolution, [status(thm)], [c_5699, c_4915])).
% 8.82/2.99  tff(c_5805, plain, (![B_592]: (~r2_hidden('#skF_2'('#skF_7', B_592, '#skF_7'), '#skF_7') | k2_zfmisc_1('#skF_7', B_592)='#skF_7')), inference(resolution, [status(thm)], [c_5733, c_5785])).
% 8.82/2.99  tff(c_5816, plain, (![B_577]: (k2_zfmisc_1('#skF_7', B_577)='#skF_7')), inference(resolution, [status(thm)], [c_5733, c_5805])).
% 8.82/2.99  tff(c_4873, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_7' | k2_zfmisc_1('#skF_9', '#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4863, c_4863, c_54])).
% 8.82/2.99  tff(c_4874, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_4873])).
% 8.82/2.99  tff(c_5823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5816, c_4874])).
% 8.82/2.99  tff(c_5824, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_7'), inference(splitRight, [status(thm)], [c_4873])).
% 8.82/2.99  tff(c_5842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5824, c_4863, c_2430])).
% 8.82/2.99  tff(c_5844, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_48])).
% 8.82/2.99  tff(c_5846, plain, (![A_4]: (k5_xboole_0(A_4, A_4)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_5844, c_14])).
% 8.82/2.99  tff(c_8564, plain, (![A_863, B_864, C_865]: (r2_hidden(A_863, B_864) | r2_hidden(A_863, C_865) | ~r2_hidden(A_863, k5_xboole_0(B_864, C_865)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_8573, plain, (![A_863, A_4]: (r2_hidden(A_863, A_4) | r2_hidden(A_863, A_4) | ~r2_hidden(A_863, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5846, c_8564])).
% 8.82/2.99  tff(c_8832, plain, (![A_895, B_896, A_4]: (r2_hidden('#skF_4'(A_895, B_896, '#skF_10'), A_4) | r2_hidden('#skF_2'(A_895, B_896, '#skF_10'), A_895) | k2_zfmisc_1(A_895, B_896)='#skF_10')), inference(resolution, [status(thm)], [c_8784, c_8573])).
% 8.82/2.99  tff(c_8552, plain, (![A_860, C_861, B_862]: (~r2_hidden(A_860, C_861) | ~r2_hidden(A_860, B_862) | ~r2_hidden(A_860, k5_xboole_0(B_862, C_861)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_8561, plain, (![A_860, A_4]: (~r2_hidden(A_860, A_4) | ~r2_hidden(A_860, A_4) | ~r2_hidden(A_860, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5846, c_8552])).
% 8.82/2.99  tff(c_9104, plain, (![A_931, B_932, C_933]: (~r2_hidden('#skF_4'(A_931, B_932, C_933), C_933) | ~r2_hidden('#skF_4'(A_931, B_932, C_933), '#skF_10') | r2_hidden('#skF_2'(A_931, B_932, C_933), A_931) | k2_zfmisc_1(A_931, B_932)=C_933)), inference(resolution, [status(thm)], [c_8784, c_8561])).
% 8.82/2.99  tff(c_9127, plain, (![A_934, B_935]: (~r2_hidden('#skF_4'(A_934, B_935, '#skF_10'), '#skF_10') | r2_hidden('#skF_2'(A_934, B_935, '#skF_10'), A_934) | k2_zfmisc_1(A_934, B_935)='#skF_10')), inference(resolution, [status(thm)], [c_8832, c_9104])).
% 8.82/2.99  tff(c_9144, plain, (![A_936, B_937]: (r2_hidden('#skF_2'(A_936, B_937, '#skF_10'), A_936) | k2_zfmisc_1(A_936, B_937)='#skF_10')), inference(resolution, [status(thm)], [c_8832, c_9127])).
% 8.82/2.99  tff(c_9176, plain, (![B_937, A_4]: (r2_hidden('#skF_2'('#skF_10', B_937, '#skF_10'), A_4) | k2_zfmisc_1('#skF_10', B_937)='#skF_10')), inference(resolution, [status(thm)], [c_9144, c_8573])).
% 8.82/2.99  tff(c_9243, plain, (![A_953, B_954]: (~r2_hidden('#skF_2'(A_953, B_954, '#skF_10'), A_953) | ~r2_hidden('#skF_2'(A_953, B_954, '#skF_10'), '#skF_10') | k2_zfmisc_1(A_953, B_954)='#skF_10')), inference(resolution, [status(thm)], [c_9144, c_8561])).
% 8.82/2.99  tff(c_9263, plain, (![B_955]: (~r2_hidden('#skF_2'('#skF_10', B_955, '#skF_10'), '#skF_10') | k2_zfmisc_1('#skF_10', B_955)='#skF_10')), inference(resolution, [status(thm)], [c_9176, c_9243])).
% 8.82/2.99  tff(c_9274, plain, (![B_937]: (k2_zfmisc_1('#skF_10', B_937)='#skF_10')), inference(resolution, [status(thm)], [c_9176, c_9263])).
% 8.82/2.99  tff(c_6129, plain, (![A_647, B_648, C_649]: (r2_hidden('#skF_2'(A_647, B_648, C_649), A_647) | r2_hidden('#skF_4'(A_647, B_648, C_649), C_649) | k2_zfmisc_1(A_647, B_648)=C_649)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_5843, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_48])).
% 8.82/2.99  tff(c_5851, plain, ('#skF_7'='#skF_10' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5844, c_5844, c_5843])).
% 8.82/2.99  tff(c_5852, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_5851])).
% 8.82/2.99  tff(c_5863, plain, (![A_4]: (k5_xboole_0(A_4, A_4)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5852, c_5846])).
% 8.82/2.99  tff(c_5905, plain, (![A_614, B_615, C_616]: (r2_hidden(A_614, B_615) | r2_hidden(A_614, C_616) | ~r2_hidden(A_614, k5_xboole_0(B_615, C_616)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_5914, plain, (![A_614, A_4]: (r2_hidden(A_614, A_4) | r2_hidden(A_614, A_4) | ~r2_hidden(A_614, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5863, c_5905])).
% 8.82/2.99  tff(c_6177, plain, (![A_647, B_648, A_4]: (r2_hidden('#skF_4'(A_647, B_648, '#skF_8'), A_4) | r2_hidden('#skF_2'(A_647, B_648, '#skF_8'), A_647) | k2_zfmisc_1(A_647, B_648)='#skF_8')), inference(resolution, [status(thm)], [c_6129, c_5914])).
% 8.82/2.99  tff(c_5886, plain, (![A_609, C_610, B_611]: (~r2_hidden(A_609, C_610) | ~r2_hidden(A_609, B_611) | ~r2_hidden(A_609, k5_xboole_0(B_611, C_610)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_5895, plain, (![A_609, A_4]: (~r2_hidden(A_609, A_4) | ~r2_hidden(A_609, A_4) | ~r2_hidden(A_609, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5863, c_5886])).
% 8.82/2.99  tff(c_6617, plain, (![A_703, B_704, C_705]: (~r2_hidden('#skF_4'(A_703, B_704, C_705), C_705) | ~r2_hidden('#skF_4'(A_703, B_704, C_705), '#skF_8') | r2_hidden('#skF_2'(A_703, B_704, C_705), A_703) | k2_zfmisc_1(A_703, B_704)=C_705)), inference(resolution, [status(thm)], [c_6129, c_5895])).
% 8.82/2.99  tff(c_6663, plain, (![A_711, B_712]: (~r2_hidden('#skF_4'(A_711, B_712, '#skF_8'), '#skF_8') | r2_hidden('#skF_2'(A_711, B_712, '#skF_8'), A_711) | k2_zfmisc_1(A_711, B_712)='#skF_8')), inference(resolution, [status(thm)], [c_6177, c_6617])).
% 8.82/2.99  tff(c_6692, plain, (![A_647, B_648]: (r2_hidden('#skF_2'(A_647, B_648, '#skF_8'), A_647) | k2_zfmisc_1(A_647, B_648)='#skF_8')), inference(resolution, [status(thm)], [c_6177, c_6663])).
% 8.82/2.99  tff(c_6696, plain, (![A_713, B_714]: (r2_hidden('#skF_2'(A_713, B_714, '#skF_8'), A_713) | k2_zfmisc_1(A_713, B_714)='#skF_8')), inference(resolution, [status(thm)], [c_6177, c_6663])).
% 8.82/2.99  tff(c_6728, plain, (![B_714, A_4]: (r2_hidden('#skF_2'('#skF_8', B_714, '#skF_8'), A_4) | k2_zfmisc_1('#skF_8', B_714)='#skF_8')), inference(resolution, [status(thm)], [c_6696, c_5914])).
% 8.82/2.99  tff(c_6807, plain, (![A_730, B_731]: (~r2_hidden('#skF_2'(A_730, B_731, '#skF_8'), A_730) | ~r2_hidden('#skF_2'(A_730, B_731, '#skF_8'), '#skF_8') | k2_zfmisc_1(A_730, B_731)='#skF_8')), inference(resolution, [status(thm)], [c_6696, c_5895])).
% 8.82/2.99  tff(c_6827, plain, (![B_732]: (~r2_hidden('#skF_2'('#skF_8', B_732, '#skF_8'), '#skF_8') | k2_zfmisc_1('#skF_8', B_732)='#skF_8')), inference(resolution, [status(thm)], [c_6728, c_6807])).
% 8.82/2.99  tff(c_6861, plain, (![B_736]: (k2_zfmisc_1('#skF_8', B_736)='#skF_8')), inference(resolution, [status(thm)], [c_6728, c_6827])).
% 8.82/2.99  tff(c_6965, plain, (![A_752, B_753, B_754]: (r2_hidden(k4_tarski(A_752, B_753), '#skF_8') | ~r2_hidden(B_753, B_754) | ~r2_hidden(A_752, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6861, c_40])).
% 8.82/2.99  tff(c_7878, plain, (![A_813, A_814, B_815]: (r2_hidden(k4_tarski(A_813, '#skF_2'(A_814, B_815, '#skF_8')), '#skF_8') | ~r2_hidden(A_813, '#skF_8') | k2_zfmisc_1(A_814, B_815)='#skF_8')), inference(resolution, [status(thm)], [c_6692, c_6965])).
% 8.82/2.99  tff(c_6889, plain, (![B_40, B_736, A_39]: (r2_hidden(B_40, B_736) | ~r2_hidden(k4_tarski(A_39, B_40), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6861, c_42])).
% 8.82/2.99  tff(c_7897, plain, (![A_814, B_815, B_736, A_813]: (r2_hidden('#skF_2'(A_814, B_815, '#skF_8'), B_736) | ~r2_hidden(A_813, '#skF_8') | k2_zfmisc_1(A_814, B_815)='#skF_8')), inference(resolution, [status(thm)], [c_7878, c_6889])).
% 8.82/2.99  tff(c_7907, plain, (![A_816]: (~r2_hidden(A_816, '#skF_8'))), inference(splitLeft, [status(thm)], [c_7897])).
% 8.82/2.99  tff(c_8311, plain, (![A_835, B_836]: (r2_hidden('#skF_3'(A_835, B_836, '#skF_8'), B_836) | k2_zfmisc_1(A_835, B_836)='#skF_8')), inference(resolution, [status(thm)], [c_36, c_7907])).
% 8.82/2.99  tff(c_7901, plain, (![A_813]: (~r2_hidden(A_813, '#skF_8'))), inference(splitLeft, [status(thm)], [c_7897])).
% 8.82/2.99  tff(c_8345, plain, (![A_835]: (k2_zfmisc_1(A_835, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_8311, c_7901])).
% 8.82/2.99  tff(c_5854, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5852, c_5844])).
% 8.82/2.99  tff(c_46, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.82/2.99  tff(c_5872, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5854, c_5852, c_5854, c_46])).
% 8.82/2.99  tff(c_8442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8345, c_5872])).
% 8.82/2.99  tff(c_8444, plain, (![A_842, B_843, B_844]: (r2_hidden('#skF_2'(A_842, B_843, '#skF_8'), B_844) | k2_zfmisc_1(A_842, B_843)='#skF_8')), inference(splitRight, [status(thm)], [c_7897])).
% 8.82/2.99  tff(c_6823, plain, (![A_647, B_648]: (~r2_hidden('#skF_2'(A_647, B_648, '#skF_8'), '#skF_8') | k2_zfmisc_1(A_647, B_648)='#skF_8')), inference(resolution, [status(thm)], [c_6692, c_6807])).
% 8.82/2.99  tff(c_8482, plain, (![A_842, B_843]: (k2_zfmisc_1(A_842, B_843)='#skF_8')), inference(resolution, [status(thm)], [c_8444, c_6823])).
% 8.82/2.99  tff(c_8522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8482, c_5872])).
% 8.82/2.99  tff(c_8523, plain, ('#skF_7'='#skF_10'), inference(splitRight, [status(thm)], [c_5851])).
% 8.82/2.99  tff(c_8537, plain, (k2_zfmisc_1('#skF_10', '#skF_8')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_5844, c_8523, c_5844, c_46])).
% 8.82/2.99  tff(c_9281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9274, c_8537])).
% 8.82/2.99  tff(c_9283, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 8.82/2.99  tff(c_9285, plain, (![A_4]: (k5_xboole_0(A_4, A_4)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9283, c_14])).
% 8.82/2.99  tff(c_11645, plain, (![A_1191, B_1192, C_1193]: (r2_hidden(A_1191, B_1192) | r2_hidden(A_1191, C_1193) | ~r2_hidden(A_1191, k5_xboole_0(B_1192, C_1193)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_11648, plain, (![A_1191, A_4]: (r2_hidden(A_1191, A_4) | r2_hidden(A_1191, A_4) | ~r2_hidden(A_1191, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9285, c_11645])).
% 8.82/2.99  tff(c_11893, plain, (![A_1232, B_1233, A_4]: (r2_hidden('#skF_4'(A_1232, B_1233, '#skF_9'), A_4) | r2_hidden('#skF_2'(A_1232, B_1233, '#skF_9'), A_1232) | k2_zfmisc_1(A_1232, B_1233)='#skF_9')), inference(resolution, [status(thm)], [c_11844, c_11648])).
% 8.82/2.99  tff(c_11649, plain, (![A_1194, C_1195, B_1196]: (~r2_hidden(A_1194, C_1195) | ~r2_hidden(A_1194, B_1196) | ~r2_hidden(A_1194, k5_xboole_0(B_1196, C_1195)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_11652, plain, (![A_1194, A_4]: (~r2_hidden(A_1194, A_4) | ~r2_hidden(A_1194, A_4) | ~r2_hidden(A_1194, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9285, c_11649])).
% 8.82/2.99  tff(c_12386, plain, (![A_1296, B_1297, C_1298]: (~r2_hidden('#skF_4'(A_1296, B_1297, C_1298), C_1298) | ~r2_hidden('#skF_4'(A_1296, B_1297, C_1298), '#skF_9') | r2_hidden('#skF_2'(A_1296, B_1297, C_1298), A_1296) | k2_zfmisc_1(A_1296, B_1297)=C_1298)), inference(resolution, [status(thm)], [c_11844, c_11652])).
% 8.82/2.99  tff(c_12423, plain, (![A_1299, B_1300]: (~r2_hidden('#skF_4'(A_1299, B_1300, '#skF_9'), '#skF_9') | r2_hidden('#skF_2'(A_1299, B_1300, '#skF_9'), A_1299) | k2_zfmisc_1(A_1299, B_1300)='#skF_9')), inference(resolution, [status(thm)], [c_11893, c_12386])).
% 8.82/2.99  tff(c_12456, plain, (![A_1301, B_1302]: (r2_hidden('#skF_2'(A_1301, B_1302, '#skF_9'), A_1301) | k2_zfmisc_1(A_1301, B_1302)='#skF_9')), inference(resolution, [status(thm)], [c_11893, c_12423])).
% 8.82/2.99  tff(c_12489, plain, (![B_1302, A_4]: (r2_hidden('#skF_2'('#skF_9', B_1302, '#skF_9'), A_4) | k2_zfmisc_1('#skF_9', B_1302)='#skF_9')), inference(resolution, [status(thm)], [c_12456, c_11648])).
% 8.82/2.99  tff(c_12501, plain, (![B_1308, A_1309]: (r2_hidden('#skF_2'('#skF_9', B_1308, '#skF_9'), A_1309) | k2_zfmisc_1('#skF_9', B_1308)='#skF_9')), inference(resolution, [status(thm)], [c_12456, c_11648])).
% 8.82/2.99  tff(c_2, plain, (![A_1, C_3, B_2]: (~r2_hidden(A_1, C_3) | ~r2_hidden(A_1, B_2) | ~r2_hidden(A_1, k5_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_12571, plain, (![B_1318, C_1319, B_1320]: (~r2_hidden('#skF_2'('#skF_9', B_1318, '#skF_9'), C_1319) | ~r2_hidden('#skF_2'('#skF_9', B_1318, '#skF_9'), B_1320) | k2_zfmisc_1('#skF_9', B_1318)='#skF_9')), inference(resolution, [status(thm)], [c_12501, c_2])).
% 8.82/2.99  tff(c_12588, plain, (![B_1321, B_1322]: (~r2_hidden('#skF_2'('#skF_9', B_1321, '#skF_9'), B_1322) | k2_zfmisc_1('#skF_9', B_1321)='#skF_9')), inference(resolution, [status(thm)], [c_12489, c_12571])).
% 8.82/2.99  tff(c_12606, plain, (![B_1302]: (k2_zfmisc_1('#skF_9', B_1302)='#skF_9')), inference(resolution, [status(thm)], [c_12489, c_12588])).
% 8.82/2.99  tff(c_9517, plain, (![A_1006, B_1007, C_1008]: (r2_hidden('#skF_2'(A_1006, B_1007, C_1008), A_1006) | r2_hidden('#skF_4'(A_1006, B_1007, C_1008), C_1008) | k2_zfmisc_1(A_1006, B_1007)=C_1008)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.82/2.99  tff(c_9282, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_52])).
% 8.82/2.99  tff(c_9291, plain, ('#skF_7'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9283, c_9283, c_9282])).
% 8.82/2.99  tff(c_9292, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_9291])).
% 8.82/2.99  tff(c_9303, plain, (![A_4]: (k5_xboole_0(A_4, A_4)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9292, c_9285])).
% 8.82/2.99  tff(c_9323, plain, (![A_970, B_971, C_972]: (r2_hidden(A_970, B_971) | r2_hidden(A_970, C_972) | ~r2_hidden(A_970, k5_xboole_0(B_971, C_972)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_9326, plain, (![A_970, A_4]: (r2_hidden(A_970, A_4) | r2_hidden(A_970, A_4) | ~r2_hidden(A_970, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9303, c_9323])).
% 8.82/2.99  tff(c_9565, plain, (![A_1006, B_1007, A_4]: (r2_hidden('#skF_4'(A_1006, B_1007, '#skF_8'), A_4) | r2_hidden('#skF_2'(A_1006, B_1007, '#skF_8'), A_1006) | k2_zfmisc_1(A_1006, B_1007)='#skF_8')), inference(resolution, [status(thm)], [c_9517, c_9326])).
% 8.82/2.99  tff(c_9318, plain, (![A_965, C_966, B_967]: (~r2_hidden(A_965, C_966) | ~r2_hidden(A_965, B_967) | ~r2_hidden(A_965, k5_xboole_0(B_967, C_966)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.82/2.99  tff(c_9321, plain, (![A_965, A_4]: (~r2_hidden(A_965, A_4) | ~r2_hidden(A_965, A_4) | ~r2_hidden(A_965, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9303, c_9318])).
% 8.82/2.99  tff(c_9970, plain, (![A_1056, B_1057, C_1058]: (~r2_hidden('#skF_4'(A_1056, B_1057, C_1058), C_1058) | ~r2_hidden('#skF_4'(A_1056, B_1057, C_1058), '#skF_8') | r2_hidden('#skF_2'(A_1056, B_1057, C_1058), A_1056) | k2_zfmisc_1(A_1056, B_1057)=C_1058)), inference(resolution, [status(thm)], [c_9517, c_9321])).
% 8.82/2.99  tff(c_10000, plain, (![A_1059, B_1060]: (~r2_hidden('#skF_4'(A_1059, B_1060, '#skF_8'), '#skF_8') | r2_hidden('#skF_2'(A_1059, B_1060, '#skF_8'), A_1059) | k2_zfmisc_1(A_1059, B_1060)='#skF_8')), inference(resolution, [status(thm)], [c_9565, c_9970])).
% 8.82/2.99  tff(c_10022, plain, (![A_1006, B_1007]: (r2_hidden('#skF_2'(A_1006, B_1007, '#skF_8'), A_1006) | k2_zfmisc_1(A_1006, B_1007)='#skF_8')), inference(resolution, [status(thm)], [c_9565, c_10000])).
% 8.82/2.99  tff(c_10025, plain, (![A_1061, B_1062]: (r2_hidden('#skF_2'(A_1061, B_1062, '#skF_8'), A_1061) | k2_zfmisc_1(A_1061, B_1062)='#skF_8')), inference(resolution, [status(thm)], [c_9565, c_10000])).
% 8.82/2.99  tff(c_10057, plain, (![B_1062, A_4]: (r2_hidden('#skF_2'('#skF_8', B_1062, '#skF_8'), A_4) | k2_zfmisc_1('#skF_8', B_1062)='#skF_8')), inference(resolution, [status(thm)], [c_10025, c_9326])).
% 8.82/2.99  tff(c_10132, plain, (![A_1078, B_1079]: (~r2_hidden('#skF_2'(A_1078, B_1079, '#skF_8'), A_1078) | ~r2_hidden('#skF_2'(A_1078, B_1079, '#skF_8'), '#skF_8') | k2_zfmisc_1(A_1078, B_1079)='#skF_8')), inference(resolution, [status(thm)], [c_10025, c_9321])).
% 8.82/2.99  tff(c_10152, plain, (![B_1080]: (~r2_hidden('#skF_2'('#skF_8', B_1080, '#skF_8'), '#skF_8') | k2_zfmisc_1('#skF_8', B_1080)='#skF_8')), inference(resolution, [status(thm)], [c_10057, c_10132])).
% 8.82/2.99  tff(c_10168, plain, (![B_1081]: (k2_zfmisc_1('#skF_8', B_1081)='#skF_8')), inference(resolution, [status(thm)], [c_10057, c_10152])).
% 8.82/2.99  tff(c_10227, plain, (![A_1092, B_1093, B_1094]: (r2_hidden(k4_tarski(A_1092, B_1093), '#skF_8') | ~r2_hidden(B_1093, B_1094) | ~r2_hidden(A_1092, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10168, c_40])).
% 8.82/2.99  tff(c_11067, plain, (![A_1154, A_1155, B_1156]: (r2_hidden(k4_tarski(A_1154, '#skF_2'(A_1155, B_1156, '#skF_8')), '#skF_8') | ~r2_hidden(A_1154, '#skF_8') | k2_zfmisc_1(A_1155, B_1156)='#skF_8')), inference(resolution, [status(thm)], [c_10022, c_10227])).
% 8.82/2.99  tff(c_10196, plain, (![B_40, B_1081, A_39]: (r2_hidden(B_40, B_1081) | ~r2_hidden(k4_tarski(A_39, B_40), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10168, c_42])).
% 8.82/2.99  tff(c_11082, plain, (![A_1155, B_1156, B_1081, A_1154]: (r2_hidden('#skF_2'(A_1155, B_1156, '#skF_8'), B_1081) | ~r2_hidden(A_1154, '#skF_8') | k2_zfmisc_1(A_1155, B_1156)='#skF_8')), inference(resolution, [status(thm)], [c_11067, c_10196])).
% 8.82/2.99  tff(c_11094, plain, (![A_1157]: (~r2_hidden(A_1157, '#skF_8'))), inference(splitLeft, [status(thm)], [c_11082])).
% 8.82/2.99  tff(c_11501, plain, (![A_1177, B_1178]: (r2_hidden('#skF_3'(A_1177, B_1178, '#skF_8'), B_1178) | k2_zfmisc_1(A_1177, B_1178)='#skF_8')), inference(resolution, [status(thm)], [c_36, c_11094])).
% 8.82/2.99  tff(c_11088, plain, (![A_1154]: (~r2_hidden(A_1154, '#skF_8'))), inference(splitLeft, [status(thm)], [c_11082])).
% 8.82/2.99  tff(c_11535, plain, (![A_1177]: (k2_zfmisc_1(A_1177, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_11501, c_11088])).
% 8.82/2.99  tff(c_9294, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9292, c_9283])).
% 8.82/2.99  tff(c_50, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.82/2.99  tff(c_9312, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9294, c_9292, c_9294, c_50])).
% 8.82/2.99  tff(c_11549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11535, c_9312])).
% 8.82/2.99  tff(c_11551, plain, (![A_1179, B_1180, B_1181]: (r2_hidden('#skF_2'(A_1179, B_1180, '#skF_8'), B_1181) | k2_zfmisc_1(A_1179, B_1180)='#skF_8')), inference(splitRight, [status(thm)], [c_11082])).
% 8.82/2.99  tff(c_10148, plain, (![A_1006, B_1007]: (~r2_hidden('#skF_2'(A_1006, B_1007, '#skF_8'), '#skF_8') | k2_zfmisc_1(A_1006, B_1007)='#skF_8')), inference(resolution, [status(thm)], [c_10022, c_10132])).
% 8.82/2.99  tff(c_11585, plain, (![A_1179, B_1180]: (k2_zfmisc_1(A_1179, B_1180)='#skF_8')), inference(resolution, [status(thm)], [c_11551, c_10148])).
% 8.82/2.99  tff(c_11623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11585, c_9312])).
% 8.82/2.99  tff(c_11624, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_9291])).
% 8.82/2.99  tff(c_11638, plain, (k2_zfmisc_1('#skF_9', '#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9283, c_11624, c_9283, c_50])).
% 8.82/2.99  tff(c_12615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12606, c_11638])).
% 8.82/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.82/2.99  
% 8.82/2.99  Inference rules
% 8.82/2.99  ----------------------
% 8.82/2.99  #Ref     : 0
% 8.82/2.99  #Sup     : 2937
% 8.82/2.99  #Fact    : 0
% 8.82/2.99  #Define  : 0
% 8.82/2.99  #Split   : 15
% 8.82/2.99  #Chain   : 0
% 8.82/2.99  #Close   : 0
% 8.82/2.99  
% 8.82/2.99  Ordering : KBO
% 8.82/2.99  
% 8.82/2.99  Simplification rules
% 8.82/2.99  ----------------------
% 8.82/2.99  #Subsume      : 1122
% 8.82/2.99  #Demod        : 695
% 8.82/2.99  #Tautology    : 418
% 8.82/2.99  #SimpNegUnit  : 127
% 8.82/2.99  #BackRed      : 156
% 8.82/2.99  
% 8.82/2.99  #Partial instantiations: 0
% 8.82/2.99  #Strategies tried      : 1
% 8.82/2.99  
% 8.82/2.99  Timing (in seconds)
% 8.82/2.99  ----------------------
% 8.82/2.99  Preprocessing        : 0.32
% 8.82/2.99  Parsing              : 0.16
% 8.82/2.99  CNF conversion       : 0.03
% 8.82/2.99  Main loop            : 1.86
% 8.82/2.99  Inferencing          : 0.69
% 8.82/2.99  Reduction            : 0.48
% 8.82/2.99  Demodulation         : 0.30
% 8.82/2.99  BG Simplification    : 0.09
% 8.82/2.99  Subsumption          : 0.43
% 8.82/2.99  Abstraction          : 0.10
% 8.82/2.99  MUC search           : 0.00
% 8.82/2.99  Cooper               : 0.00
% 8.82/2.99  Total                : 2.25
% 8.82/2.99  Index Insertion      : 0.00
% 8.82/2.99  Index Deletion       : 0.00
% 8.82/2.99  Index Matching       : 0.00
% 8.82/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
