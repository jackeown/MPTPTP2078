%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:41 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 6.26s
% Verified   : 
% Statistics : Number of formulae       :  217 (1172 expanded)
%              Number of leaves         :   27 ( 359 expanded)
%              Depth                    :   15
%              Number of atoms          :  356 (2730 expanded)
%              Number of equality atoms :  108 (1186 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_1 > #skF_12

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

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),B_10)
      | r2_hidden('#skF_3'(A_9,B_10),A_9)
      | B_10 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7144,plain,(
    ! [A_835,B_836] :
      ( r2_hidden('#skF_2'(A_835,B_836),B_836)
      | r2_hidden('#skF_3'(A_835,B_836),A_835)
      | B_836 = A_835 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5699,plain,(
    ! [A_642,B_643] :
      ( r2_hidden('#skF_2'(A_642,B_643),B_643)
      | r2_hidden('#skF_3'(A_642,B_643),A_642)
      | B_643 = A_642 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_1694,plain,(
    ! [A_252,B_253] :
      ( r2_hidden('#skF_2'(A_252,B_253),B_253)
      | r2_hidden('#skF_3'(A_252,B_253),A_252)
      | B_253 = A_252 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_756,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_2'(A_146,B_147),B_147)
      | r2_hidden('#skF_3'(A_146,B_147),A_146)
      | B_147 = A_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_272,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_2'(A_88,B_89),B_89)
      | r2_hidden('#skF_3'(A_88,B_89),A_88)
      | B_89 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_127,plain,(
    ! [A_66,C_67,B_68] :
      ( ~ r2_hidden(A_66,C_67)
      | ~ r2_hidden(A_66,B_68)
      | ~ r2_hidden(A_66,k5_xboole_0(B_68,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_140,plain,(
    ! [A_66,A_13] :
      ( ~ r2_hidden(A_66,k1_xboole_0)
      | ~ r2_hidden(A_66,A_13)
      | ~ r2_hidden(A_66,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_127])).

tff(c_340,plain,(
    ! [B_93,A_94] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_93),A_94)
      | r2_hidden('#skF_2'(k1_xboole_0,B_93),B_93)
      | k1_xboole_0 = B_93 ) ),
    inference(resolution,[status(thm)],[c_272,c_140])).

tff(c_353,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_10),B_10)
      | k1_xboole_0 = B_10 ) ),
    inference(resolution,[status(thm)],[c_26,c_340])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_88,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_392,plain,(
    ! [E_96,F_97,A_98,B_99] :
      ( r2_hidden(k4_tarski(E_96,F_97),k2_zfmisc_1(A_98,B_99))
      | ~ r2_hidden(F_97,B_99)
      | ~ r2_hidden(E_96,A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_397,plain,(
    ! [E_96,F_97] :
      ( r2_hidden(k4_tarski(E_96,F_97),k1_xboole_0)
      | ~ r2_hidden(F_97,'#skF_13')
      | ~ r2_hidden(E_96,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_392])).

tff(c_443,plain,(
    ! [E_103,F_104] :
      ( r2_hidden(k4_tarski(E_103,F_104),k1_xboole_0)
      | ~ r2_hidden(F_104,'#skF_13')
      | ~ r2_hidden(E_103,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_392])).

tff(c_455,plain,(
    ! [E_105,F_106,A_107] :
      ( ~ r2_hidden(k4_tarski(E_105,F_106),A_107)
      | ~ r2_hidden(F_106,'#skF_13')
      | ~ r2_hidden(E_105,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_443,c_140])).

tff(c_470,plain,(
    ! [F_97,E_96] :
      ( ~ r2_hidden(F_97,'#skF_13')
      | ~ r2_hidden(E_96,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_397,c_455])).

tff(c_475,plain,(
    ! [E_108] : ~ r2_hidden(E_108,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_483,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_353,c_475])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_483])).

tff(c_534,plain,(
    ! [F_112] : ~ r2_hidden(F_112,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_546,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_353,c_534])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_546])).

tff(c_571,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_573,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_577,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_11') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_30])).

tff(c_616,plain,(
    ! [A_123,C_124,B_125] :
      ( ~ r2_hidden(A_123,C_124)
      | ~ r2_hidden(A_123,B_125)
      | ~ r2_hidden(A_123,k5_xboole_0(B_125,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_622,plain,(
    ! [A_123,A_13] :
      ( ~ r2_hidden(A_123,'#skF_11')
      | ~ r2_hidden(A_123,A_13)
      | ~ r2_hidden(A_123,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_616])).

tff(c_817,plain,(
    ! [B_150,A_151] :
      ( ~ r2_hidden('#skF_3'('#skF_11',B_150),A_151)
      | r2_hidden('#skF_2'('#skF_11',B_150),B_150)
      | B_150 = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_756,c_622])).

tff(c_830,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2'('#skF_11',B_10),B_10)
      | B_10 = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_26,c_817])).

tff(c_36,plain,(
    ! [A_14,B_15,D_41] :
      ( r2_hidden('#skF_9'(A_14,B_15,k2_zfmisc_1(A_14,B_15),D_41),B_15)
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [A_14,B_15,D_41] :
      ( r2_hidden('#skF_8'(A_14,B_15,k2_zfmisc_1(A_14,B_15),D_41),A_14)
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1044,plain,(
    ! [A_171,B_172,D_173] :
      ( r2_hidden('#skF_8'(A_171,B_172,k2_zfmisc_1(A_171,B_172),D_173),A_171)
      | ~ r2_hidden(D_173,k2_zfmisc_1(A_171,B_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1254,plain,(
    ! [B_207,D_208,A_209] :
      ( ~ r2_hidden('#skF_8'('#skF_11',B_207,k2_zfmisc_1('#skF_11',B_207),D_208),A_209)
      | ~ r2_hidden(D_208,k2_zfmisc_1('#skF_11',B_207)) ) ),
    inference(resolution,[status(thm)],[c_1044,c_622])).

tff(c_1270,plain,(
    ! [D_210,B_211] : ~ r2_hidden(D_210,k2_zfmisc_1('#skF_11',B_211)) ),
    inference(resolution,[status(thm)],[c_38,c_1254])).

tff(c_1335,plain,(
    ! [B_211] : k2_zfmisc_1('#skF_11',B_211) = '#skF_11' ),
    inference(resolution,[status(thm)],[c_830,c_1270])).

tff(c_1269,plain,(
    ! [D_41,B_15] : ~ r2_hidden(D_41,k2_zfmisc_1('#skF_11',B_15)) ),
    inference(resolution,[status(thm)],[c_38,c_1254])).

tff(c_1360,plain,(
    ! [D_213] : ~ r2_hidden(D_213,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1335,c_1269])).

tff(c_1442,plain,(
    ! [D_217,A_218] : ~ r2_hidden(D_217,k2_zfmisc_1(A_218,'#skF_11')) ),
    inference(resolution,[status(thm)],[c_36,c_1360])).

tff(c_1510,plain,(
    ! [A_218] : k2_zfmisc_1(A_218,'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_830,c_1442])).

tff(c_64,plain,
    ( k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0
    | k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_80,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_574,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_80])).

tff(c_1519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_574])).

tff(c_1520,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_1527,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_10') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_30])).

tff(c_1556,plain,(
    ! [A_227,B_228,C_229] :
      ( r2_hidden(A_227,B_228)
      | ~ r2_hidden(A_227,C_229)
      | r2_hidden(A_227,k5_xboole_0(B_228,C_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1568,plain,(
    ! [A_227,A_13] :
      ( r2_hidden(A_227,A_13)
      | ~ r2_hidden(A_227,'#skF_10')
      | r2_hidden(A_227,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_1556])).

tff(c_1766,plain,(
    ! [B_256,A_257] :
      ( r2_hidden('#skF_3'('#skF_10',B_256),A_257)
      | r2_hidden('#skF_2'('#skF_10',B_256),B_256)
      | B_256 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1694,c_1568])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),B_10)
      | ~ r2_hidden('#skF_3'(A_9,B_10),B_10)
      | B_10 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1800,plain,(
    ! [A_257] :
      ( r2_hidden('#skF_2'('#skF_10',A_257),A_257)
      | A_257 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1766,c_22])).

tff(c_1894,plain,(
    ! [A_266,B_267,D_268] :
      ( r2_hidden('#skF_8'(A_266,B_267,k2_zfmisc_1(A_266,B_267),D_268),A_266)
      | ~ r2_hidden(D_268,k2_zfmisc_1(A_266,B_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1913,plain,(
    ! [B_267,D_268,A_13] :
      ( r2_hidden('#skF_8'('#skF_10',B_267,k2_zfmisc_1('#skF_10',B_267),D_268),A_13)
      | ~ r2_hidden(D_268,k2_zfmisc_1('#skF_10',B_267)) ) ),
    inference(resolution,[status(thm)],[c_1894,c_1568])).

tff(c_1953,plain,(
    ! [A_272,B_273,D_274] :
      ( r2_hidden('#skF_9'(A_272,B_273,k2_zfmisc_1(A_272,B_273),D_274),B_273)
      | ~ r2_hidden(D_274,k2_zfmisc_1(A_272,B_273)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1594,plain,(
    ! [A_235,C_236,B_237] :
      ( ~ r2_hidden(A_235,C_236)
      | ~ r2_hidden(A_235,B_237)
      | ~ r2_hidden(A_235,k5_xboole_0(B_237,C_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1603,plain,(
    ! [A_235,A_13] :
      ( ~ r2_hidden(A_235,'#skF_10')
      | ~ r2_hidden(A_235,A_13)
      | ~ r2_hidden(A_235,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_1594])).

tff(c_2251,plain,(
    ! [A_316,D_317,A_318] :
      ( ~ r2_hidden('#skF_9'(A_316,'#skF_10',k2_zfmisc_1(A_316,'#skF_10'),D_317),A_318)
      | ~ r2_hidden(D_317,k2_zfmisc_1(A_316,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1953,c_1603])).

tff(c_2279,plain,(
    ! [D_322,A_323] : ~ r2_hidden(D_322,k2_zfmisc_1(A_323,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_36,c_2251])).

tff(c_2455,plain,(
    ! [D_331,B_332] : ~ r2_hidden(D_331,k2_zfmisc_1('#skF_10',B_332)) ),
    inference(resolution,[status(thm)],[c_1913,c_2279])).

tff(c_2522,plain,(
    ! [B_332] : k2_zfmisc_1('#skF_10',B_332) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1800,c_2455])).

tff(c_1524,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_80])).

tff(c_2532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2522,c_1524])).

tff(c_2534,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2795,plain,(
    ! [E_373,F_374,A_375,B_376] :
      ( r2_hidden(k4_tarski(E_373,F_374),k2_zfmisc_1(A_375,B_376))
      | ~ r2_hidden(F_374,B_376)
      | ~ r2_hidden(E_373,A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2800,plain,(
    ! [E_373,F_374] :
      ( r2_hidden(k4_tarski(E_373,F_374),k1_xboole_0)
      | ~ r2_hidden(F_374,'#skF_11')
      | ~ r2_hidden(E_373,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2534,c_2795])).

tff(c_2808,plain,(
    ! [E_378,F_379] :
      ( r2_hidden(k4_tarski(E_378,F_379),k1_xboole_0)
      | ~ r2_hidden(F_379,'#skF_11')
      | ~ r2_hidden(E_378,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2534,c_2795])).

tff(c_2586,plain,(
    ! [A_347,C_348,B_349] :
      ( ~ r2_hidden(A_347,C_348)
      | ~ r2_hidden(A_347,B_349)
      | ~ r2_hidden(A_347,k5_xboole_0(B_349,C_348)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2596,plain,(
    ! [A_347,A_13] :
      ( ~ r2_hidden(A_347,k1_xboole_0)
      | ~ r2_hidden(A_347,A_13)
      | ~ r2_hidden(A_347,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2586])).

tff(c_2832,plain,(
    ! [E_382,F_383,A_384] :
      ( ~ r2_hidden(k4_tarski(E_382,F_383),A_384)
      | ~ r2_hidden(F_383,'#skF_11')
      | ~ r2_hidden(E_382,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2808,c_2596])).

tff(c_2851,plain,(
    ! [F_374,E_373] :
      ( ~ r2_hidden(F_374,'#skF_11')
      | ~ r2_hidden(E_373,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_2800,c_2832])).

tff(c_2856,plain,(
    ! [E_385] : ~ r2_hidden(E_385,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2851])).

tff(c_2875,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2'('#skF_10',B_10),B_10)
      | B_10 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_26,c_2856])).

tff(c_2901,plain,(
    ! [B_389] :
      ( r2_hidden('#skF_2'('#skF_10',B_389),B_389)
      | B_389 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_26,c_2856])).

tff(c_2928,plain,(
    ! [A_13] :
      ( ~ r2_hidden('#skF_2'('#skF_10',k1_xboole_0),A_13)
      | k1_xboole_0 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_2901,c_2596])).

tff(c_3032,plain,(
    ! [A_397] : ~ r2_hidden('#skF_2'('#skF_10',k1_xboole_0),A_397) ),
    inference(splitLeft,[status(thm)],[c_2928])).

tff(c_3047,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2875,c_3032])).

tff(c_3061,plain,(
    '#skF_10' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_78])).

tff(c_3062,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_77])).

tff(c_2855,plain,(
    ! [E_373] : ~ r2_hidden(E_373,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2851])).

tff(c_2533,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2803,plain,(
    ! [E_373,F_374] :
      ( r2_hidden(k4_tarski(E_373,F_374),k1_xboole_0)
      | ~ r2_hidden(F_374,'#skF_13')
      | ~ r2_hidden(E_373,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2533,c_2795])).

tff(c_3054,plain,(
    ! [E_373,F_374] :
      ( r2_hidden(k4_tarski(E_373,F_374),'#skF_10')
      | ~ r2_hidden(F_374,'#skF_13')
      | ~ r2_hidden(E_373,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_2803])).

tff(c_3065,plain,(
    ! [F_374,E_373] :
      ( ~ r2_hidden(F_374,'#skF_13')
      | ~ r2_hidden(E_373,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2855,c_3054])).

tff(c_3266,plain,(
    ! [E_409] : ~ r2_hidden(E_409,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_3065])).

tff(c_3278,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2875,c_3266])).

tff(c_3302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3062,c_3278])).

tff(c_3304,plain,(
    ! [F_410] : ~ r2_hidden(F_410,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_3065])).

tff(c_3316,plain,(
    '#skF_10' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_2875,c_3304])).

tff(c_3340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3061,c_3316])).

tff(c_3341,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_2928])).

tff(c_3350,plain,(
    '#skF_10' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3341,c_78])).

tff(c_3351,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3341,c_77])).

tff(c_3343,plain,(
    ! [E_373,F_374] :
      ( r2_hidden(k4_tarski(E_373,F_374),'#skF_10')
      | ~ r2_hidden(F_374,'#skF_13')
      | ~ r2_hidden(E_373,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3341,c_2803])).

tff(c_3354,plain,(
    ! [F_374,E_373] :
      ( ~ r2_hidden(F_374,'#skF_13')
      | ~ r2_hidden(E_373,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2855,c_3343])).

tff(c_3440,plain,(
    ! [E_415] : ~ r2_hidden(E_415,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_3354])).

tff(c_3452,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2875,c_3440])).

tff(c_3476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3351,c_3452])).

tff(c_3478,plain,(
    ! [F_416] : ~ r2_hidden(F_416,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_3354])).

tff(c_3486,plain,(
    '#skF_10' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_2875,c_3478])).

tff(c_3509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3350,c_3486])).

tff(c_3510,plain,(
    ! [F_374] : ~ r2_hidden(F_374,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_2851])).

tff(c_4177,plain,(
    ! [A_461,B_462,D_463] :
      ( r2_hidden('#skF_9'(A_461,B_462,k2_zfmisc_1(A_461,B_462),D_463),B_462)
      | ~ r2_hidden(D_463,k2_zfmisc_1(A_461,B_462)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4204,plain,(
    ! [D_463] :
      ( r2_hidden('#skF_9'('#skF_10','#skF_11',k1_xboole_0,D_463),'#skF_11')
      | ~ r2_hidden(D_463,k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2534,c_4177])).

tff(c_4215,plain,(
    ! [D_463] :
      ( r2_hidden('#skF_9'('#skF_10','#skF_11',k1_xboole_0,D_463),'#skF_11')
      | ~ r2_hidden(D_463,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2534,c_4204])).

tff(c_4219,plain,(
    ! [D_464] : ~ r2_hidden(D_464,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_3510,c_4215])).

tff(c_4696,plain,(
    ! [B_500] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_500),B_500)
      | k1_xboole_0 = B_500 ) ),
    inference(resolution,[status(thm)],[c_26,c_4219])).

tff(c_3610,plain,(
    ! [A_426,B_427,D_428] :
      ( r2_hidden('#skF_9'(A_426,B_427,k2_zfmisc_1(A_426,B_427),D_428),B_427)
      | ~ r2_hidden(D_428,k2_zfmisc_1(A_426,B_427)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3637,plain,(
    ! [D_428] :
      ( r2_hidden('#skF_9'('#skF_10','#skF_11',k1_xboole_0,D_428),'#skF_11')
      | ~ r2_hidden(D_428,k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2534,c_3610])).

tff(c_3648,plain,(
    ! [D_428] :
      ( r2_hidden('#skF_9'('#skF_10','#skF_11',k1_xboole_0,D_428),'#skF_11')
      | ~ r2_hidden(D_428,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2534,c_3637])).

tff(c_3651,plain,(
    ! [D_429] : ~ r2_hidden(D_429,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_3510,c_3648])).

tff(c_4091,plain,(
    ! [B_459] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_459),B_459)
      | k1_xboole_0 = B_459 ) ),
    inference(resolution,[status(thm)],[c_26,c_3651])).

tff(c_2820,plain,(
    ! [E_380,F_381] :
      ( r2_hidden(k4_tarski(E_380,F_381),k1_xboole_0)
      | ~ r2_hidden(F_381,'#skF_13')
      | ~ r2_hidden(E_380,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2533,c_2795])).

tff(c_3534,plain,(
    ! [E_418,F_419,A_420] :
      ( ~ r2_hidden(k4_tarski(E_418,F_419),A_420)
      | ~ r2_hidden(F_419,'#skF_13')
      | ~ r2_hidden(E_418,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_2820,c_2596])).

tff(c_3549,plain,(
    ! [F_374,E_373] :
      ( ~ r2_hidden(F_374,'#skF_13')
      | ~ r2_hidden(E_373,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_2803,c_3534])).

tff(c_3559,plain,(
    ! [E_373] : ~ r2_hidden(E_373,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_3549])).

tff(c_4123,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_4091,c_3559])).

tff(c_4152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_4123])).

tff(c_4153,plain,(
    ! [F_374] : ~ r2_hidden(F_374,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_3549])).

tff(c_4728,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_4696,c_4153])).

tff(c_4757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4728])).

tff(c_4759,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4761,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_13') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_30])).

tff(c_5571,plain,(
    ! [A_623,C_624,B_625] :
      ( ~ r2_hidden(A_623,C_624)
      | ~ r2_hidden(A_623,B_625)
      | ~ r2_hidden(A_623,k5_xboole_0(B_625,C_624)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5584,plain,(
    ! [A_623,A_13] :
      ( ~ r2_hidden(A_623,'#skF_13')
      | ~ r2_hidden(A_623,A_13)
      | ~ r2_hidden(A_623,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4761,c_5571])).

tff(c_5771,plain,(
    ! [B_651,A_652] :
      ( ~ r2_hidden('#skF_3'('#skF_13',B_651),A_652)
      | r2_hidden('#skF_2'('#skF_13',B_651),B_651)
      | B_651 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_5699,c_5584])).

tff(c_5784,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2'('#skF_13',B_10),B_10)
      | B_10 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_26,c_5771])).

tff(c_5889,plain,(
    ! [A_660,B_661,D_662] :
      ( r2_hidden('#skF_8'(A_660,B_661,k2_zfmisc_1(A_660,B_661),D_662),A_660)
      | ~ r2_hidden(D_662,k2_zfmisc_1(A_660,B_661)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6078,plain,(
    ! [B_693,D_694,A_695] :
      ( ~ r2_hidden('#skF_8'('#skF_13',B_693,k2_zfmisc_1('#skF_13',B_693),D_694),A_695)
      | ~ r2_hidden(D_694,k2_zfmisc_1('#skF_13',B_693)) ) ),
    inference(resolution,[status(thm)],[c_5889,c_5584])).

tff(c_6094,plain,(
    ! [D_696,B_697] : ~ r2_hidden(D_696,k2_zfmisc_1('#skF_13',B_697)) ),
    inference(resolution,[status(thm)],[c_38,c_6078])).

tff(c_6158,plain,(
    ! [B_697] : k2_zfmisc_1('#skF_13',B_697) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_5784,c_6094])).

tff(c_4984,plain,(
    ! [A_541,B_542] :
      ( r2_hidden('#skF_2'(A_541,B_542),B_542)
      | r2_hidden('#skF_3'(A_541,B_542),A_541)
      | B_542 = A_541 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4826,plain,(
    ! [A_517,C_518,B_519] :
      ( ~ r2_hidden(A_517,C_518)
      | ~ r2_hidden(A_517,B_519)
      | ~ r2_hidden(A_517,k5_xboole_0(B_519,C_518)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4836,plain,(
    ! [A_517,A_13] :
      ( ~ r2_hidden(A_517,'#skF_13')
      | ~ r2_hidden(A_517,A_13)
      | ~ r2_hidden(A_517,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4761,c_4826])).

tff(c_5056,plain,(
    ! [B_550,A_551] :
      ( ~ r2_hidden('#skF_3'('#skF_13',B_550),A_551)
      | r2_hidden('#skF_2'('#skF_13',B_550),B_550)
      | B_550 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_4984,c_4836])).

tff(c_5069,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2'('#skF_13',B_10),B_10)
      | B_10 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_26,c_5056])).

tff(c_5174,plain,(
    ! [A_559,B_560,D_561] :
      ( r2_hidden('#skF_9'(A_559,B_560,k2_zfmisc_1(A_559,B_560),D_561),B_560)
      | ~ r2_hidden(D_561,k2_zfmisc_1(A_559,B_560)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4845,plain,(
    ! [A_522,B_523,C_524] :
      ( r2_hidden(A_522,B_523)
      | ~ r2_hidden(A_522,C_524)
      | r2_hidden(A_522,k5_xboole_0(B_523,C_524)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4860,plain,(
    ! [A_522,A_13] :
      ( r2_hidden(A_522,A_13)
      | ~ r2_hidden(A_522,'#skF_13')
      | r2_hidden(A_522,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4761,c_4845])).

tff(c_5191,plain,(
    ! [A_559,D_561,A_13] :
      ( r2_hidden('#skF_9'(A_559,'#skF_13',k2_zfmisc_1(A_559,'#skF_13'),D_561),A_13)
      | ~ r2_hidden(D_561,k2_zfmisc_1(A_559,'#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_5174,c_4860])).

tff(c_5385,plain,(
    ! [A_595,D_596,A_597] :
      ( ~ r2_hidden('#skF_9'(A_595,'#skF_13',k2_zfmisc_1(A_595,'#skF_13'),D_596),A_597)
      | ~ r2_hidden(D_596,k2_zfmisc_1(A_595,'#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_5174,c_4836])).

tff(c_5405,plain,(
    ! [D_598,A_599] : ~ r2_hidden(D_598,k2_zfmisc_1(A_599,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_5191,c_5385])).

tff(c_5469,plain,(
    ! [A_599] : k2_zfmisc_1(A_599,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_5069,c_5405])).

tff(c_4758,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4770,plain,
    ( '#skF_10' = '#skF_13'
    | '#skF_11' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_4759,c_4758])).

tff(c_4771,plain,(
    '#skF_11' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_4770])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0
    | k1_xboole_0 != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4768,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_4759,c_56])).

tff(c_4772,plain,(
    k2_zfmisc_1('#skF_10','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4771,c_4768])).

tff(c_5490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5469,c_4772])).

tff(c_5491,plain,(
    '#skF_10' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_4770])).

tff(c_5493,plain,(
    k2_zfmisc_1('#skF_13','#skF_11') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5491,c_4768])).

tff(c_6179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6158,c_5493])).

tff(c_6181,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6182,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_12') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6181,c_30])).

tff(c_7047,plain,(
    ! [A_819,C_820,B_821] :
      ( ~ r2_hidden(A_819,C_820)
      | ~ r2_hidden(A_819,B_821)
      | ~ r2_hidden(A_819,k5_xboole_0(B_821,C_820)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7060,plain,(
    ! [A_819,A_13] :
      ( ~ r2_hidden(A_819,'#skF_12')
      | ~ r2_hidden(A_819,A_13)
      | ~ r2_hidden(A_819,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6182,c_7047])).

tff(c_7236,plain,(
    ! [B_843,A_844] :
      ( ~ r2_hidden('#skF_3'('#skF_12',B_843),A_844)
      | r2_hidden('#skF_2'('#skF_12',B_843),B_843)
      | B_843 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_7144,c_7060])).

tff(c_7250,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2'('#skF_12',B_10),B_10)
      | B_10 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_26,c_7236])).

tff(c_7432,plain,(
    ! [A_862,B_863,D_864] :
      ( r2_hidden('#skF_8'(A_862,B_863,k2_zfmisc_1(A_862,B_863),D_864),A_862)
      | ~ r2_hidden(D_864,k2_zfmisc_1(A_862,B_863)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7561,plain,(
    ! [B_888,D_889,A_890] :
      ( ~ r2_hidden('#skF_8'('#skF_12',B_888,k2_zfmisc_1('#skF_12',B_888),D_889),A_890)
      | ~ r2_hidden(D_889,k2_zfmisc_1('#skF_12',B_888)) ) ),
    inference(resolution,[status(thm)],[c_7432,c_7060])).

tff(c_7614,plain,(
    ! [D_894,B_895] : ~ r2_hidden(D_894,k2_zfmisc_1('#skF_12',B_895)) ),
    inference(resolution,[status(thm)],[c_38,c_7561])).

tff(c_7669,plain,(
    ! [B_895] : k2_zfmisc_1('#skF_12',B_895) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_7250,c_7614])).

tff(c_7576,plain,(
    ! [D_41,B_15] : ~ r2_hidden(D_41,k2_zfmisc_1('#skF_12',B_15)) ),
    inference(resolution,[status(thm)],[c_38,c_7561])).

tff(c_7694,plain,(
    ! [D_897] : ~ r2_hidden(D_897,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7669,c_7576])).

tff(c_7783,plain,(
    ! [D_901,A_902] : ~ r2_hidden(D_901,k2_zfmisc_1(A_902,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_36,c_7694])).

tff(c_7851,plain,(
    ! [A_902] : k2_zfmisc_1(A_902,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_7250,c_7783])).

tff(c_6382,plain,(
    ! [A_739,B_740] :
      ( r2_hidden('#skF_2'(A_739,B_740),B_740)
      | r2_hidden('#skF_3'(A_739,B_740),A_739)
      | B_740 = A_739 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6242,plain,(
    ! [A_716,C_717,B_718] :
      ( ~ r2_hidden(A_716,C_717)
      | ~ r2_hidden(A_716,B_718)
      | ~ r2_hidden(A_716,k5_xboole_0(B_718,C_717)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6252,plain,(
    ! [A_716,A_13] :
      ( ~ r2_hidden(A_716,'#skF_12')
      | ~ r2_hidden(A_716,A_13)
      | ~ r2_hidden(A_716,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6182,c_6242])).

tff(c_6443,plain,(
    ! [B_743,A_744] :
      ( ~ r2_hidden('#skF_3'('#skF_12',B_743),A_744)
      | r2_hidden('#skF_2'('#skF_12',B_743),B_743)
      | B_743 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_6382,c_6252])).

tff(c_6456,plain,(
    ! [B_10] :
      ( r2_hidden('#skF_2'('#skF_12',B_10),B_10)
      | B_10 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_26,c_6443])).

tff(c_6599,plain,(
    ! [A_757,B_758,D_759] :
      ( r2_hidden('#skF_8'(A_757,B_758,k2_zfmisc_1(A_757,B_758),D_759),A_757)
      | ~ r2_hidden(D_759,k2_zfmisc_1(A_757,B_758)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6903,plain,(
    ! [B_798,D_799,A_800] :
      ( ~ r2_hidden('#skF_8'('#skF_12',B_798,k2_zfmisc_1('#skF_12',B_798),D_799),A_800)
      | ~ r2_hidden(D_799,k2_zfmisc_1('#skF_12',B_798)) ) ),
    inference(resolution,[status(thm)],[c_6599,c_6252])).

tff(c_6919,plain,(
    ! [D_801,B_802] : ~ r2_hidden(D_801,k2_zfmisc_1('#skF_12',B_802)) ),
    inference(resolution,[status(thm)],[c_38,c_6903])).

tff(c_6984,plain,(
    ! [B_802] : k2_zfmisc_1('#skF_12',B_802) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6456,c_6919])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6202,plain,
    ( '#skF_11' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6181,c_6181,c_6181,c_62])).

tff(c_6203,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_6202])).

tff(c_6180,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6189,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6181,c_6180])).

tff(c_6204,plain,(
    k2_zfmisc_1('#skF_12','#skF_11') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6203,c_6189])).

tff(c_6993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6984,c_6204])).

tff(c_6994,plain,(
    '#skF_11' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_6202])).

tff(c_6996,plain,(
    k2_zfmisc_1('#skF_10','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6994,c_6189])).

tff(c_7860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7851,c_6996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.20  
% 5.94/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.20  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_1 > #skF_12
% 5.94/2.20  
% 5.94/2.20  %Foreground sorts:
% 5.94/2.20  
% 5.94/2.20  
% 5.94/2.20  %Background operators:
% 5.94/2.20  
% 5.94/2.20  
% 5.94/2.20  %Foreground operators:
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.94/2.20  tff('#skF_11', type, '#skF_11': $i).
% 5.94/2.20  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.94/2.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.94/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.20  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 5.94/2.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.94/2.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.94/2.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.94/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.20  tff('#skF_10', type, '#skF_10': $i).
% 5.94/2.20  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.94/2.20  tff('#skF_13', type, '#skF_13': $i).
% 5.94/2.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.94/2.20  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.94/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.94/2.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.94/2.20  tff('#skF_12', type, '#skF_12': $i).
% 5.94/2.20  
% 6.26/2.23  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 6.26/2.23  tff(f_69, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.26/2.23  tff(f_50, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.26/2.23  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.26/2.23  tff(f_62, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.26/2.23  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), B_10) | r2_hidden('#skF_3'(A_9, B_10), A_9) | B_10=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_7144, plain, (![A_835, B_836]: (r2_hidden('#skF_2'(A_835, B_836), B_836) | r2_hidden('#skF_3'(A_835, B_836), A_835) | B_836=A_835)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_5699, plain, (![A_642, B_643]: (r2_hidden('#skF_2'(A_642, B_643), B_643) | r2_hidden('#skF_3'(A_642, B_643), A_642) | B_643=A_642)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_58, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.26/2.23  tff(c_78, plain, (k1_xboole_0!='#skF_13'), inference(splitLeft, [status(thm)], [c_58])).
% 6.26/2.23  tff(c_1694, plain, (![A_252, B_253]: (r2_hidden('#skF_2'(A_252, B_253), B_253) | r2_hidden('#skF_3'(A_252, B_253), A_252) | B_253=A_252)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_756, plain, (![A_146, B_147]: (r2_hidden('#skF_2'(A_146, B_147), B_147) | r2_hidden('#skF_3'(A_146, B_147), A_146) | B_147=A_146)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_272, plain, (![A_88, B_89]: (r2_hidden('#skF_2'(A_88, B_89), B_89) | r2_hidden('#skF_3'(A_88, B_89), A_88) | B_89=A_88)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_30, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.26/2.23  tff(c_127, plain, (![A_66, C_67, B_68]: (~r2_hidden(A_66, C_67) | ~r2_hidden(A_66, B_68) | ~r2_hidden(A_66, k5_xboole_0(B_68, C_67)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_140, plain, (![A_66, A_13]: (~r2_hidden(A_66, k1_xboole_0) | ~r2_hidden(A_66, A_13) | ~r2_hidden(A_66, A_13))), inference(superposition, [status(thm), theory('equality')], [c_30, c_127])).
% 6.26/2.23  tff(c_340, plain, (![B_93, A_94]: (~r2_hidden('#skF_3'(k1_xboole_0, B_93), A_94) | r2_hidden('#skF_2'(k1_xboole_0, B_93), B_93) | k1_xboole_0=B_93)), inference(resolution, [status(thm)], [c_272, c_140])).
% 6.26/2.23  tff(c_353, plain, (![B_10]: (r2_hidden('#skF_2'(k1_xboole_0, B_10), B_10) | k1_xboole_0=B_10)), inference(resolution, [status(thm)], [c_26, c_340])).
% 6.26/2.23  tff(c_60, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.26/2.23  tff(c_77, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_60])).
% 6.26/2.23  tff(c_66, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.26/2.23  tff(c_88, plain, (k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 6.26/2.23  tff(c_392, plain, (![E_96, F_97, A_98, B_99]: (r2_hidden(k4_tarski(E_96, F_97), k2_zfmisc_1(A_98, B_99)) | ~r2_hidden(F_97, B_99) | ~r2_hidden(E_96, A_98))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_397, plain, (![E_96, F_97]: (r2_hidden(k4_tarski(E_96, F_97), k1_xboole_0) | ~r2_hidden(F_97, '#skF_13') | ~r2_hidden(E_96, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_392])).
% 6.26/2.23  tff(c_443, plain, (![E_103, F_104]: (r2_hidden(k4_tarski(E_103, F_104), k1_xboole_0) | ~r2_hidden(F_104, '#skF_13') | ~r2_hidden(E_103, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_392])).
% 6.26/2.23  tff(c_455, plain, (![E_105, F_106, A_107]: (~r2_hidden(k4_tarski(E_105, F_106), A_107) | ~r2_hidden(F_106, '#skF_13') | ~r2_hidden(E_105, '#skF_12'))), inference(resolution, [status(thm)], [c_443, c_140])).
% 6.26/2.23  tff(c_470, plain, (![F_97, E_96]: (~r2_hidden(F_97, '#skF_13') | ~r2_hidden(E_96, '#skF_12'))), inference(resolution, [status(thm)], [c_397, c_455])).
% 6.26/2.23  tff(c_475, plain, (![E_108]: (~r2_hidden(E_108, '#skF_12'))), inference(splitLeft, [status(thm)], [c_470])).
% 6.26/2.23  tff(c_483, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_353, c_475])).
% 6.26/2.23  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_483])).
% 6.26/2.23  tff(c_534, plain, (![F_112]: (~r2_hidden(F_112, '#skF_13'))), inference(splitRight, [status(thm)], [c_470])).
% 6.26/2.23  tff(c_546, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_353, c_534])).
% 6.26/2.23  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_546])).
% 6.26/2.23  tff(c_571, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_66])).
% 6.26/2.23  tff(c_573, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_571])).
% 6.26/2.23  tff(c_577, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_11')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_573, c_30])).
% 6.26/2.23  tff(c_616, plain, (![A_123, C_124, B_125]: (~r2_hidden(A_123, C_124) | ~r2_hidden(A_123, B_125) | ~r2_hidden(A_123, k5_xboole_0(B_125, C_124)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_622, plain, (![A_123, A_13]: (~r2_hidden(A_123, '#skF_11') | ~r2_hidden(A_123, A_13) | ~r2_hidden(A_123, A_13))), inference(superposition, [status(thm), theory('equality')], [c_577, c_616])).
% 6.26/2.23  tff(c_817, plain, (![B_150, A_151]: (~r2_hidden('#skF_3'('#skF_11', B_150), A_151) | r2_hidden('#skF_2'('#skF_11', B_150), B_150) | B_150='#skF_11')), inference(resolution, [status(thm)], [c_756, c_622])).
% 6.26/2.23  tff(c_830, plain, (![B_10]: (r2_hidden('#skF_2'('#skF_11', B_10), B_10) | B_10='#skF_11')), inference(resolution, [status(thm)], [c_26, c_817])).
% 6.26/2.23  tff(c_36, plain, (![A_14, B_15, D_41]: (r2_hidden('#skF_9'(A_14, B_15, k2_zfmisc_1(A_14, B_15), D_41), B_15) | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_38, plain, (![A_14, B_15, D_41]: (r2_hidden('#skF_8'(A_14, B_15, k2_zfmisc_1(A_14, B_15), D_41), A_14) | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_1044, plain, (![A_171, B_172, D_173]: (r2_hidden('#skF_8'(A_171, B_172, k2_zfmisc_1(A_171, B_172), D_173), A_171) | ~r2_hidden(D_173, k2_zfmisc_1(A_171, B_172)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_1254, plain, (![B_207, D_208, A_209]: (~r2_hidden('#skF_8'('#skF_11', B_207, k2_zfmisc_1('#skF_11', B_207), D_208), A_209) | ~r2_hidden(D_208, k2_zfmisc_1('#skF_11', B_207)))), inference(resolution, [status(thm)], [c_1044, c_622])).
% 6.26/2.23  tff(c_1270, plain, (![D_210, B_211]: (~r2_hidden(D_210, k2_zfmisc_1('#skF_11', B_211)))), inference(resolution, [status(thm)], [c_38, c_1254])).
% 6.26/2.23  tff(c_1335, plain, (![B_211]: (k2_zfmisc_1('#skF_11', B_211)='#skF_11')), inference(resolution, [status(thm)], [c_830, c_1270])).
% 6.26/2.23  tff(c_1269, plain, (![D_41, B_15]: (~r2_hidden(D_41, k2_zfmisc_1('#skF_11', B_15)))), inference(resolution, [status(thm)], [c_38, c_1254])).
% 6.26/2.23  tff(c_1360, plain, (![D_213]: (~r2_hidden(D_213, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1335, c_1269])).
% 6.26/2.23  tff(c_1442, plain, (![D_217, A_218]: (~r2_hidden(D_217, k2_zfmisc_1(A_218, '#skF_11')))), inference(resolution, [status(thm)], [c_36, c_1360])).
% 6.26/2.23  tff(c_1510, plain, (![A_218]: (k2_zfmisc_1(A_218, '#skF_11')='#skF_11')), inference(resolution, [status(thm)], [c_830, c_1442])).
% 6.26/2.23  tff(c_64, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0 | k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.26/2.23  tff(c_80, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 6.26/2.23  tff(c_574, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_573, c_80])).
% 6.26/2.23  tff(c_1519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1510, c_574])).
% 6.26/2.23  tff(c_1520, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_571])).
% 6.26/2.23  tff(c_1527, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_10')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_30])).
% 6.26/2.23  tff(c_1556, plain, (![A_227, B_228, C_229]: (r2_hidden(A_227, B_228) | ~r2_hidden(A_227, C_229) | r2_hidden(A_227, k5_xboole_0(B_228, C_229)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_1568, plain, (![A_227, A_13]: (r2_hidden(A_227, A_13) | ~r2_hidden(A_227, '#skF_10') | r2_hidden(A_227, A_13))), inference(superposition, [status(thm), theory('equality')], [c_1527, c_1556])).
% 6.26/2.23  tff(c_1766, plain, (![B_256, A_257]: (r2_hidden('#skF_3'('#skF_10', B_256), A_257) | r2_hidden('#skF_2'('#skF_10', B_256), B_256) | B_256='#skF_10')), inference(resolution, [status(thm)], [c_1694, c_1568])).
% 6.26/2.23  tff(c_22, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), B_10) | ~r2_hidden('#skF_3'(A_9, B_10), B_10) | B_10=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_1800, plain, (![A_257]: (r2_hidden('#skF_2'('#skF_10', A_257), A_257) | A_257='#skF_10')), inference(resolution, [status(thm)], [c_1766, c_22])).
% 6.26/2.23  tff(c_1894, plain, (![A_266, B_267, D_268]: (r2_hidden('#skF_8'(A_266, B_267, k2_zfmisc_1(A_266, B_267), D_268), A_266) | ~r2_hidden(D_268, k2_zfmisc_1(A_266, B_267)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_1913, plain, (![B_267, D_268, A_13]: (r2_hidden('#skF_8'('#skF_10', B_267, k2_zfmisc_1('#skF_10', B_267), D_268), A_13) | ~r2_hidden(D_268, k2_zfmisc_1('#skF_10', B_267)))), inference(resolution, [status(thm)], [c_1894, c_1568])).
% 6.26/2.23  tff(c_1953, plain, (![A_272, B_273, D_274]: (r2_hidden('#skF_9'(A_272, B_273, k2_zfmisc_1(A_272, B_273), D_274), B_273) | ~r2_hidden(D_274, k2_zfmisc_1(A_272, B_273)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_1594, plain, (![A_235, C_236, B_237]: (~r2_hidden(A_235, C_236) | ~r2_hidden(A_235, B_237) | ~r2_hidden(A_235, k5_xboole_0(B_237, C_236)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_1603, plain, (![A_235, A_13]: (~r2_hidden(A_235, '#skF_10') | ~r2_hidden(A_235, A_13) | ~r2_hidden(A_235, A_13))), inference(superposition, [status(thm), theory('equality')], [c_1527, c_1594])).
% 6.26/2.23  tff(c_2251, plain, (![A_316, D_317, A_318]: (~r2_hidden('#skF_9'(A_316, '#skF_10', k2_zfmisc_1(A_316, '#skF_10'), D_317), A_318) | ~r2_hidden(D_317, k2_zfmisc_1(A_316, '#skF_10')))), inference(resolution, [status(thm)], [c_1953, c_1603])).
% 6.26/2.23  tff(c_2279, plain, (![D_322, A_323]: (~r2_hidden(D_322, k2_zfmisc_1(A_323, '#skF_10')))), inference(resolution, [status(thm)], [c_36, c_2251])).
% 6.26/2.23  tff(c_2455, plain, (![D_331, B_332]: (~r2_hidden(D_331, k2_zfmisc_1('#skF_10', B_332)))), inference(resolution, [status(thm)], [c_1913, c_2279])).
% 6.26/2.23  tff(c_2522, plain, (![B_332]: (k2_zfmisc_1('#skF_10', B_332)='#skF_10')), inference(resolution, [status(thm)], [c_1800, c_2455])).
% 6.26/2.23  tff(c_1524, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_80])).
% 6.26/2.23  tff(c_2532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2522, c_1524])).
% 6.26/2.23  tff(c_2534, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 6.26/2.23  tff(c_2795, plain, (![E_373, F_374, A_375, B_376]: (r2_hidden(k4_tarski(E_373, F_374), k2_zfmisc_1(A_375, B_376)) | ~r2_hidden(F_374, B_376) | ~r2_hidden(E_373, A_375))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_2800, plain, (![E_373, F_374]: (r2_hidden(k4_tarski(E_373, F_374), k1_xboole_0) | ~r2_hidden(F_374, '#skF_11') | ~r2_hidden(E_373, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2534, c_2795])).
% 6.26/2.23  tff(c_2808, plain, (![E_378, F_379]: (r2_hidden(k4_tarski(E_378, F_379), k1_xboole_0) | ~r2_hidden(F_379, '#skF_11') | ~r2_hidden(E_378, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2534, c_2795])).
% 6.26/2.23  tff(c_2586, plain, (![A_347, C_348, B_349]: (~r2_hidden(A_347, C_348) | ~r2_hidden(A_347, B_349) | ~r2_hidden(A_347, k5_xboole_0(B_349, C_348)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_2596, plain, (![A_347, A_13]: (~r2_hidden(A_347, k1_xboole_0) | ~r2_hidden(A_347, A_13) | ~r2_hidden(A_347, A_13))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2586])).
% 6.26/2.23  tff(c_2832, plain, (![E_382, F_383, A_384]: (~r2_hidden(k4_tarski(E_382, F_383), A_384) | ~r2_hidden(F_383, '#skF_11') | ~r2_hidden(E_382, '#skF_10'))), inference(resolution, [status(thm)], [c_2808, c_2596])).
% 6.26/2.23  tff(c_2851, plain, (![F_374, E_373]: (~r2_hidden(F_374, '#skF_11') | ~r2_hidden(E_373, '#skF_10'))), inference(resolution, [status(thm)], [c_2800, c_2832])).
% 6.26/2.23  tff(c_2856, plain, (![E_385]: (~r2_hidden(E_385, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2851])).
% 6.26/2.23  tff(c_2875, plain, (![B_10]: (r2_hidden('#skF_2'('#skF_10', B_10), B_10) | B_10='#skF_10')), inference(resolution, [status(thm)], [c_26, c_2856])).
% 6.26/2.23  tff(c_2901, plain, (![B_389]: (r2_hidden('#skF_2'('#skF_10', B_389), B_389) | B_389='#skF_10')), inference(resolution, [status(thm)], [c_26, c_2856])).
% 6.26/2.23  tff(c_2928, plain, (![A_13]: (~r2_hidden('#skF_2'('#skF_10', k1_xboole_0), A_13) | k1_xboole_0='#skF_10')), inference(resolution, [status(thm)], [c_2901, c_2596])).
% 6.26/2.23  tff(c_3032, plain, (![A_397]: (~r2_hidden('#skF_2'('#skF_10', k1_xboole_0), A_397))), inference(splitLeft, [status(thm)], [c_2928])).
% 6.26/2.23  tff(c_3047, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_2875, c_3032])).
% 6.26/2.23  tff(c_3061, plain, ('#skF_10'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_78])).
% 6.26/2.23  tff(c_3062, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_77])).
% 6.26/2.23  tff(c_2855, plain, (![E_373]: (~r2_hidden(E_373, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2851])).
% 6.26/2.23  tff(c_2533, plain, (k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 6.26/2.23  tff(c_2803, plain, (![E_373, F_374]: (r2_hidden(k4_tarski(E_373, F_374), k1_xboole_0) | ~r2_hidden(F_374, '#skF_13') | ~r2_hidden(E_373, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2533, c_2795])).
% 6.26/2.23  tff(c_3054, plain, (![E_373, F_374]: (r2_hidden(k4_tarski(E_373, F_374), '#skF_10') | ~r2_hidden(F_374, '#skF_13') | ~r2_hidden(E_373, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_2803])).
% 6.26/2.23  tff(c_3065, plain, (![F_374, E_373]: (~r2_hidden(F_374, '#skF_13') | ~r2_hidden(E_373, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_2855, c_3054])).
% 6.26/2.23  tff(c_3266, plain, (![E_409]: (~r2_hidden(E_409, '#skF_12'))), inference(splitLeft, [status(thm)], [c_3065])).
% 6.26/2.23  tff(c_3278, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_2875, c_3266])).
% 6.26/2.23  tff(c_3302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3062, c_3278])).
% 6.26/2.23  tff(c_3304, plain, (![F_410]: (~r2_hidden(F_410, '#skF_13'))), inference(splitRight, [status(thm)], [c_3065])).
% 6.26/2.23  tff(c_3316, plain, ('#skF_10'='#skF_13'), inference(resolution, [status(thm)], [c_2875, c_3304])).
% 6.26/2.23  tff(c_3340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3061, c_3316])).
% 6.26/2.23  tff(c_3341, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_2928])).
% 6.26/2.23  tff(c_3350, plain, ('#skF_10'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3341, c_78])).
% 6.26/2.23  tff(c_3351, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3341, c_77])).
% 6.26/2.23  tff(c_3343, plain, (![E_373, F_374]: (r2_hidden(k4_tarski(E_373, F_374), '#skF_10') | ~r2_hidden(F_374, '#skF_13') | ~r2_hidden(E_373, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3341, c_2803])).
% 6.26/2.23  tff(c_3354, plain, (![F_374, E_373]: (~r2_hidden(F_374, '#skF_13') | ~r2_hidden(E_373, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_2855, c_3343])).
% 6.26/2.23  tff(c_3440, plain, (![E_415]: (~r2_hidden(E_415, '#skF_12'))), inference(splitLeft, [status(thm)], [c_3354])).
% 6.26/2.23  tff(c_3452, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_2875, c_3440])).
% 6.26/2.23  tff(c_3476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3351, c_3452])).
% 6.26/2.23  tff(c_3478, plain, (![F_416]: (~r2_hidden(F_416, '#skF_13'))), inference(splitRight, [status(thm)], [c_3354])).
% 6.26/2.23  tff(c_3486, plain, ('#skF_10'='#skF_13'), inference(resolution, [status(thm)], [c_2875, c_3478])).
% 6.26/2.23  tff(c_3509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3350, c_3486])).
% 6.26/2.23  tff(c_3510, plain, (![F_374]: (~r2_hidden(F_374, '#skF_11'))), inference(splitRight, [status(thm)], [c_2851])).
% 6.26/2.23  tff(c_4177, plain, (![A_461, B_462, D_463]: (r2_hidden('#skF_9'(A_461, B_462, k2_zfmisc_1(A_461, B_462), D_463), B_462) | ~r2_hidden(D_463, k2_zfmisc_1(A_461, B_462)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_4204, plain, (![D_463]: (r2_hidden('#skF_9'('#skF_10', '#skF_11', k1_xboole_0, D_463), '#skF_11') | ~r2_hidden(D_463, k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_2534, c_4177])).
% 6.26/2.23  tff(c_4215, plain, (![D_463]: (r2_hidden('#skF_9'('#skF_10', '#skF_11', k1_xboole_0, D_463), '#skF_11') | ~r2_hidden(D_463, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2534, c_4204])).
% 6.26/2.23  tff(c_4219, plain, (![D_464]: (~r2_hidden(D_464, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_3510, c_4215])).
% 6.26/2.23  tff(c_4696, plain, (![B_500]: (r2_hidden('#skF_2'(k1_xboole_0, B_500), B_500) | k1_xboole_0=B_500)), inference(resolution, [status(thm)], [c_26, c_4219])).
% 6.26/2.23  tff(c_3610, plain, (![A_426, B_427, D_428]: (r2_hidden('#skF_9'(A_426, B_427, k2_zfmisc_1(A_426, B_427), D_428), B_427) | ~r2_hidden(D_428, k2_zfmisc_1(A_426, B_427)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_3637, plain, (![D_428]: (r2_hidden('#skF_9'('#skF_10', '#skF_11', k1_xboole_0, D_428), '#skF_11') | ~r2_hidden(D_428, k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_2534, c_3610])).
% 6.26/2.23  tff(c_3648, plain, (![D_428]: (r2_hidden('#skF_9'('#skF_10', '#skF_11', k1_xboole_0, D_428), '#skF_11') | ~r2_hidden(D_428, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2534, c_3637])).
% 6.26/2.23  tff(c_3651, plain, (![D_429]: (~r2_hidden(D_429, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_3510, c_3648])).
% 6.26/2.23  tff(c_4091, plain, (![B_459]: (r2_hidden('#skF_2'(k1_xboole_0, B_459), B_459) | k1_xboole_0=B_459)), inference(resolution, [status(thm)], [c_26, c_3651])).
% 6.26/2.23  tff(c_2820, plain, (![E_380, F_381]: (r2_hidden(k4_tarski(E_380, F_381), k1_xboole_0) | ~r2_hidden(F_381, '#skF_13') | ~r2_hidden(E_380, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2533, c_2795])).
% 6.26/2.23  tff(c_3534, plain, (![E_418, F_419, A_420]: (~r2_hidden(k4_tarski(E_418, F_419), A_420) | ~r2_hidden(F_419, '#skF_13') | ~r2_hidden(E_418, '#skF_12'))), inference(resolution, [status(thm)], [c_2820, c_2596])).
% 6.26/2.23  tff(c_3549, plain, (![F_374, E_373]: (~r2_hidden(F_374, '#skF_13') | ~r2_hidden(E_373, '#skF_12'))), inference(resolution, [status(thm)], [c_2803, c_3534])).
% 6.26/2.23  tff(c_3559, plain, (![E_373]: (~r2_hidden(E_373, '#skF_12'))), inference(splitLeft, [status(thm)], [c_3549])).
% 6.26/2.23  tff(c_4123, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_4091, c_3559])).
% 6.26/2.23  tff(c_4152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_4123])).
% 6.26/2.23  tff(c_4153, plain, (![F_374]: (~r2_hidden(F_374, '#skF_13'))), inference(splitRight, [status(thm)], [c_3549])).
% 6.26/2.23  tff(c_4728, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_4696, c_4153])).
% 6.26/2.23  tff(c_4757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4728])).
% 6.26/2.23  tff(c_4759, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_58])).
% 6.26/2.23  tff(c_4761, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_13')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_30])).
% 6.26/2.23  tff(c_5571, plain, (![A_623, C_624, B_625]: (~r2_hidden(A_623, C_624) | ~r2_hidden(A_623, B_625) | ~r2_hidden(A_623, k5_xboole_0(B_625, C_624)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_5584, plain, (![A_623, A_13]: (~r2_hidden(A_623, '#skF_13') | ~r2_hidden(A_623, A_13) | ~r2_hidden(A_623, A_13))), inference(superposition, [status(thm), theory('equality')], [c_4761, c_5571])).
% 6.26/2.23  tff(c_5771, plain, (![B_651, A_652]: (~r2_hidden('#skF_3'('#skF_13', B_651), A_652) | r2_hidden('#skF_2'('#skF_13', B_651), B_651) | B_651='#skF_13')), inference(resolution, [status(thm)], [c_5699, c_5584])).
% 6.26/2.23  tff(c_5784, plain, (![B_10]: (r2_hidden('#skF_2'('#skF_13', B_10), B_10) | B_10='#skF_13')), inference(resolution, [status(thm)], [c_26, c_5771])).
% 6.26/2.23  tff(c_5889, plain, (![A_660, B_661, D_662]: (r2_hidden('#skF_8'(A_660, B_661, k2_zfmisc_1(A_660, B_661), D_662), A_660) | ~r2_hidden(D_662, k2_zfmisc_1(A_660, B_661)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_6078, plain, (![B_693, D_694, A_695]: (~r2_hidden('#skF_8'('#skF_13', B_693, k2_zfmisc_1('#skF_13', B_693), D_694), A_695) | ~r2_hidden(D_694, k2_zfmisc_1('#skF_13', B_693)))), inference(resolution, [status(thm)], [c_5889, c_5584])).
% 6.26/2.23  tff(c_6094, plain, (![D_696, B_697]: (~r2_hidden(D_696, k2_zfmisc_1('#skF_13', B_697)))), inference(resolution, [status(thm)], [c_38, c_6078])).
% 6.26/2.23  tff(c_6158, plain, (![B_697]: (k2_zfmisc_1('#skF_13', B_697)='#skF_13')), inference(resolution, [status(thm)], [c_5784, c_6094])).
% 6.26/2.23  tff(c_4984, plain, (![A_541, B_542]: (r2_hidden('#skF_2'(A_541, B_542), B_542) | r2_hidden('#skF_3'(A_541, B_542), A_541) | B_542=A_541)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_4826, plain, (![A_517, C_518, B_519]: (~r2_hidden(A_517, C_518) | ~r2_hidden(A_517, B_519) | ~r2_hidden(A_517, k5_xboole_0(B_519, C_518)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_4836, plain, (![A_517, A_13]: (~r2_hidden(A_517, '#skF_13') | ~r2_hidden(A_517, A_13) | ~r2_hidden(A_517, A_13))), inference(superposition, [status(thm), theory('equality')], [c_4761, c_4826])).
% 6.26/2.23  tff(c_5056, plain, (![B_550, A_551]: (~r2_hidden('#skF_3'('#skF_13', B_550), A_551) | r2_hidden('#skF_2'('#skF_13', B_550), B_550) | B_550='#skF_13')), inference(resolution, [status(thm)], [c_4984, c_4836])).
% 6.26/2.23  tff(c_5069, plain, (![B_10]: (r2_hidden('#skF_2'('#skF_13', B_10), B_10) | B_10='#skF_13')), inference(resolution, [status(thm)], [c_26, c_5056])).
% 6.26/2.23  tff(c_5174, plain, (![A_559, B_560, D_561]: (r2_hidden('#skF_9'(A_559, B_560, k2_zfmisc_1(A_559, B_560), D_561), B_560) | ~r2_hidden(D_561, k2_zfmisc_1(A_559, B_560)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_4845, plain, (![A_522, B_523, C_524]: (r2_hidden(A_522, B_523) | ~r2_hidden(A_522, C_524) | r2_hidden(A_522, k5_xboole_0(B_523, C_524)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_4860, plain, (![A_522, A_13]: (r2_hidden(A_522, A_13) | ~r2_hidden(A_522, '#skF_13') | r2_hidden(A_522, A_13))), inference(superposition, [status(thm), theory('equality')], [c_4761, c_4845])).
% 6.26/2.23  tff(c_5191, plain, (![A_559, D_561, A_13]: (r2_hidden('#skF_9'(A_559, '#skF_13', k2_zfmisc_1(A_559, '#skF_13'), D_561), A_13) | ~r2_hidden(D_561, k2_zfmisc_1(A_559, '#skF_13')))), inference(resolution, [status(thm)], [c_5174, c_4860])).
% 6.26/2.23  tff(c_5385, plain, (![A_595, D_596, A_597]: (~r2_hidden('#skF_9'(A_595, '#skF_13', k2_zfmisc_1(A_595, '#skF_13'), D_596), A_597) | ~r2_hidden(D_596, k2_zfmisc_1(A_595, '#skF_13')))), inference(resolution, [status(thm)], [c_5174, c_4836])).
% 6.26/2.23  tff(c_5405, plain, (![D_598, A_599]: (~r2_hidden(D_598, k2_zfmisc_1(A_599, '#skF_13')))), inference(resolution, [status(thm)], [c_5191, c_5385])).
% 6.26/2.23  tff(c_5469, plain, (![A_599]: (k2_zfmisc_1(A_599, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_5069, c_5405])).
% 6.26/2.23  tff(c_4758, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_58])).
% 6.26/2.23  tff(c_4770, plain, ('#skF_10'='#skF_13' | '#skF_11'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_4759, c_4758])).
% 6.26/2.23  tff(c_4771, plain, ('#skF_11'='#skF_13'), inference(splitLeft, [status(thm)], [c_4770])).
% 6.26/2.23  tff(c_56, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0 | k1_xboole_0!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.26/2.23  tff(c_4768, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_4759, c_56])).
% 6.26/2.23  tff(c_4772, plain, (k2_zfmisc_1('#skF_10', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4771, c_4768])).
% 6.26/2.23  tff(c_5490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5469, c_4772])).
% 6.26/2.23  tff(c_5491, plain, ('#skF_10'='#skF_13'), inference(splitRight, [status(thm)], [c_4770])).
% 6.26/2.23  tff(c_5493, plain, (k2_zfmisc_1('#skF_13', '#skF_11')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5491, c_4768])).
% 6.26/2.23  tff(c_6179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6158, c_5493])).
% 6.26/2.23  tff(c_6181, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_60])).
% 6.26/2.23  tff(c_6182, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_12')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_6181, c_30])).
% 6.26/2.23  tff(c_7047, plain, (![A_819, C_820, B_821]: (~r2_hidden(A_819, C_820) | ~r2_hidden(A_819, B_821) | ~r2_hidden(A_819, k5_xboole_0(B_821, C_820)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_7060, plain, (![A_819, A_13]: (~r2_hidden(A_819, '#skF_12') | ~r2_hidden(A_819, A_13) | ~r2_hidden(A_819, A_13))), inference(superposition, [status(thm), theory('equality')], [c_6182, c_7047])).
% 6.26/2.23  tff(c_7236, plain, (![B_843, A_844]: (~r2_hidden('#skF_3'('#skF_12', B_843), A_844) | r2_hidden('#skF_2'('#skF_12', B_843), B_843) | B_843='#skF_12')), inference(resolution, [status(thm)], [c_7144, c_7060])).
% 6.26/2.23  tff(c_7250, plain, (![B_10]: (r2_hidden('#skF_2'('#skF_12', B_10), B_10) | B_10='#skF_12')), inference(resolution, [status(thm)], [c_26, c_7236])).
% 6.26/2.23  tff(c_7432, plain, (![A_862, B_863, D_864]: (r2_hidden('#skF_8'(A_862, B_863, k2_zfmisc_1(A_862, B_863), D_864), A_862) | ~r2_hidden(D_864, k2_zfmisc_1(A_862, B_863)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_7561, plain, (![B_888, D_889, A_890]: (~r2_hidden('#skF_8'('#skF_12', B_888, k2_zfmisc_1('#skF_12', B_888), D_889), A_890) | ~r2_hidden(D_889, k2_zfmisc_1('#skF_12', B_888)))), inference(resolution, [status(thm)], [c_7432, c_7060])).
% 6.26/2.23  tff(c_7614, plain, (![D_894, B_895]: (~r2_hidden(D_894, k2_zfmisc_1('#skF_12', B_895)))), inference(resolution, [status(thm)], [c_38, c_7561])).
% 6.26/2.23  tff(c_7669, plain, (![B_895]: (k2_zfmisc_1('#skF_12', B_895)='#skF_12')), inference(resolution, [status(thm)], [c_7250, c_7614])).
% 6.26/2.23  tff(c_7576, plain, (![D_41, B_15]: (~r2_hidden(D_41, k2_zfmisc_1('#skF_12', B_15)))), inference(resolution, [status(thm)], [c_38, c_7561])).
% 6.26/2.23  tff(c_7694, plain, (![D_897]: (~r2_hidden(D_897, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_7669, c_7576])).
% 6.26/2.23  tff(c_7783, plain, (![D_901, A_902]: (~r2_hidden(D_901, k2_zfmisc_1(A_902, '#skF_12')))), inference(resolution, [status(thm)], [c_36, c_7694])).
% 6.26/2.23  tff(c_7851, plain, (![A_902]: (k2_zfmisc_1(A_902, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_7250, c_7783])).
% 6.26/2.23  tff(c_6382, plain, (![A_739, B_740]: (r2_hidden('#skF_2'(A_739, B_740), B_740) | r2_hidden('#skF_3'(A_739, B_740), A_739) | B_740=A_739)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.23  tff(c_6242, plain, (![A_716, C_717, B_718]: (~r2_hidden(A_716, C_717) | ~r2_hidden(A_716, B_718) | ~r2_hidden(A_716, k5_xboole_0(B_718, C_717)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.26/2.23  tff(c_6252, plain, (![A_716, A_13]: (~r2_hidden(A_716, '#skF_12') | ~r2_hidden(A_716, A_13) | ~r2_hidden(A_716, A_13))), inference(superposition, [status(thm), theory('equality')], [c_6182, c_6242])).
% 6.26/2.23  tff(c_6443, plain, (![B_743, A_744]: (~r2_hidden('#skF_3'('#skF_12', B_743), A_744) | r2_hidden('#skF_2'('#skF_12', B_743), B_743) | B_743='#skF_12')), inference(resolution, [status(thm)], [c_6382, c_6252])).
% 6.26/2.23  tff(c_6456, plain, (![B_10]: (r2_hidden('#skF_2'('#skF_12', B_10), B_10) | B_10='#skF_12')), inference(resolution, [status(thm)], [c_26, c_6443])).
% 6.26/2.23  tff(c_6599, plain, (![A_757, B_758, D_759]: (r2_hidden('#skF_8'(A_757, B_758, k2_zfmisc_1(A_757, B_758), D_759), A_757) | ~r2_hidden(D_759, k2_zfmisc_1(A_757, B_758)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.26/2.23  tff(c_6903, plain, (![B_798, D_799, A_800]: (~r2_hidden('#skF_8'('#skF_12', B_798, k2_zfmisc_1('#skF_12', B_798), D_799), A_800) | ~r2_hidden(D_799, k2_zfmisc_1('#skF_12', B_798)))), inference(resolution, [status(thm)], [c_6599, c_6252])).
% 6.26/2.23  tff(c_6919, plain, (![D_801, B_802]: (~r2_hidden(D_801, k2_zfmisc_1('#skF_12', B_802)))), inference(resolution, [status(thm)], [c_38, c_6903])).
% 6.26/2.23  tff(c_6984, plain, (![B_802]: (k2_zfmisc_1('#skF_12', B_802)='#skF_12')), inference(resolution, [status(thm)], [c_6456, c_6919])).
% 6.26/2.23  tff(c_62, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.26/2.23  tff(c_6202, plain, ('#skF_11'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_6181, c_6181, c_6181, c_62])).
% 6.26/2.23  tff(c_6203, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_6202])).
% 6.26/2.23  tff(c_6180, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 6.26/2.23  tff(c_6189, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_6181, c_6180])).
% 6.26/2.23  tff(c_6204, plain, (k2_zfmisc_1('#skF_12', '#skF_11')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_6203, c_6189])).
% 6.26/2.23  tff(c_6993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6984, c_6204])).
% 6.26/2.23  tff(c_6994, plain, ('#skF_11'='#skF_12'), inference(splitRight, [status(thm)], [c_6202])).
% 6.26/2.23  tff(c_6996, plain, (k2_zfmisc_1('#skF_10', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_6994, c_6189])).
% 6.26/2.23  tff(c_7860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7851, c_6996])).
% 6.26/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.26/2.23  
% 6.26/2.23  Inference rules
% 6.26/2.23  ----------------------
% 6.26/2.23  #Ref     : 0
% 6.26/2.23  #Sup     : 1626
% 6.26/2.23  #Fact    : 0
% 6.26/2.23  #Define  : 0
% 6.26/2.23  #Split   : 14
% 6.26/2.23  #Chain   : 0
% 6.26/2.23  #Close   : 0
% 6.26/2.23  
% 6.26/2.23  Ordering : KBO
% 6.26/2.23  
% 6.26/2.23  Simplification rules
% 6.26/2.23  ----------------------
% 6.26/2.23  #Subsume      : 440
% 6.26/2.23  #Demod        : 295
% 6.26/2.23  #Tautology    : 346
% 6.26/2.23  #SimpNegUnit  : 35
% 6.26/2.23  #BackRed      : 63
% 6.26/2.23  
% 6.26/2.23  #Partial instantiations: 0
% 6.26/2.23  #Strategies tried      : 1
% 6.26/2.23  
% 6.26/2.23  Timing (in seconds)
% 6.26/2.23  ----------------------
% 6.26/2.23  Preprocessing        : 0.31
% 6.26/2.23  Parsing              : 0.15
% 6.26/2.23  CNF conversion       : 0.03
% 6.26/2.23  Main loop            : 1.13
% 6.26/2.23  Inferencing          : 0.45
% 6.26/2.23  Reduction            : 0.28
% 6.26/2.23  Demodulation         : 0.18
% 6.26/2.23  BG Simplification    : 0.05
% 6.26/2.23  Subsumption          : 0.23
% 6.26/2.24  Abstraction          : 0.06
% 6.26/2.24  MUC search           : 0.00
% 6.26/2.24  Cooper               : 0.00
% 6.26/2.24  Total                : 1.50
% 6.26/2.24  Index Insertion      : 0.00
% 6.26/2.24  Index Deletion       : 0.00
% 6.26/2.24  Index Matching       : 0.00
% 6.26/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
