%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:39 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 767 expanded)
%              Number of leaves         :   33 ( 244 expanded)
%              Depth                    :   11
%              Number of atoms          :  242 (1383 expanded)
%              Number of equality atoms :  130 (1076 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_8693,plain,(
    ! [A_870,B_871,C_872] :
      ( r2_hidden('#skF_4'(A_870,B_871,C_872),A_870)
      | r2_hidden('#skF_6'(A_870,B_871,C_872),C_872)
      | k2_zfmisc_1(A_870,B_871) = C_872 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_164,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_26,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,A_54) = k3_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_100,plain,(
    ! [A_54] : k3_xboole_0(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_24])).

tff(c_177,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_186,plain,(
    ! [A_54] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_177])).

tff(c_198,plain,(
    ! [A_54] : k4_xboole_0(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_186])).

tff(c_5144,plain,(
    ! [A_567,B_568,C_569] :
      ( r2_hidden('#skF_1'(A_567,B_568,C_569),A_567)
      | r2_hidden('#skF_2'(A_567,B_568,C_569),C_569)
      | k4_xboole_0(A_567,B_568) = C_569 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(A_56,B_57)
      | ~ r1_xboole_0(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_174,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_169])).

tff(c_5260,plain,(
    ! [B_568,C_569] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_568,C_569),C_569)
      | k4_xboole_0(k1_xboole_0,B_568) = C_569 ) ),
    inference(resolution,[status(thm)],[c_5144,c_174])).

tff(c_5432,plain,(
    ! [B_570,C_571] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_570,C_571),C_571)
      | k1_xboole_0 = C_571 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_5260])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_167,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_4207,plain,(
    ! [A_480,B_481,C_482] :
      ( r2_hidden('#skF_1'(A_480,B_481,C_482),A_480)
      | r2_hidden('#skF_2'(A_480,B_481,C_482),C_482)
      | k4_xboole_0(A_480,B_481) = C_482 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4331,plain,(
    ! [B_481,C_482] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_481,C_482),C_482)
      | k4_xboole_0(k1_xboole_0,B_481) = C_482 ) ),
    inference(resolution,[status(thm)],[c_4207,c_174])).

tff(c_4515,plain,(
    ! [B_483,C_484] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_483,C_484),C_484)
      | k1_xboole_0 = C_484 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_4331])).

tff(c_1244,plain,(
    ! [A_212,B_213,C_214] :
      ( r2_hidden('#skF_1'(A_212,B_213,C_214),A_212)
      | r2_hidden('#skF_2'(A_212,B_213,C_214),C_214)
      | k4_xboole_0(A_212,B_213) = C_214 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1355,plain,(
    ! [B_213,C_214] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_213,C_214),C_214)
      | k4_xboole_0(k1_xboole_0,B_213) = C_214 ) ),
    inference(resolution,[status(thm)],[c_1244,c_174])).

tff(c_1524,plain,(
    ! [B_215,C_216] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_215,C_216),C_216)
      | k1_xboole_0 = C_216 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1355])).

tff(c_555,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden('#skF_1'(A_117,B_118,C_119),A_117)
      | r2_hidden('#skF_2'(A_117,B_118,C_119),C_119)
      | k4_xboole_0(A_117,B_118) = C_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_615,plain,(
    ! [B_118,C_119] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_118,C_119),C_119)
      | k4_xboole_0(k1_xboole_0,B_118) = C_119 ) ),
    inference(resolution,[status(thm)],[c_555,c_174])).

tff(c_711,plain,(
    ! [B_120,C_121] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_120,C_121),C_121)
      | k1_xboole_0 = C_121 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_615])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_241,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_299,plain,(
    ! [E_74,F_75,A_76,B_77] :
      ( r2_hidden(k4_tarski(E_74,F_75),k2_zfmisc_1(A_76,B_77))
      | ~ r2_hidden(F_75,B_77)
      | ~ r2_hidden(E_74,A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_302,plain,(
    ! [E_74,F_75] :
      ( r2_hidden(k4_tarski(E_74,F_75),k1_xboole_0)
      | ~ r2_hidden(F_75,'#skF_12')
      | ~ r2_hidden(E_74,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_299])).

tff(c_303,plain,(
    ! [F_75,E_74] :
      ( ~ r2_hidden(F_75,'#skF_12')
      | ~ r2_hidden(E_74,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_302])).

tff(c_304,plain,(
    ! [E_74] : ~ r2_hidden(E_74,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_763,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_711,c_304])).

tff(c_791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_763])).

tff(c_792,plain,(
    ! [F_75] : ~ r2_hidden(F_75,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_1624,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1524,c_792])).

tff(c_1664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_1624])).

tff(c_1665,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1667,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1665])).

tff(c_1676,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_10') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1690,plain,(
    ! [A_219] : k3_xboole_0(A_219,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_1667,c_24])).

tff(c_1723,plain,(
    ! [B_221] : k3_xboole_0('#skF_10',B_221) = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1690])).

tff(c_22,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1731,plain,(
    ! [B_221] : k5_xboole_0('#skF_10','#skF_10') = k4_xboole_0('#skF_10',B_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_1723,c_22])).

tff(c_1753,plain,(
    ! [B_221] : k4_xboole_0('#skF_10',B_221) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1731])).

tff(c_2511,plain,(
    ! [A_301,B_302,C_303] :
      ( r2_hidden('#skF_1'(A_301,B_302,C_303),A_301)
      | r2_hidden('#skF_2'(A_301,B_302,C_303),C_303)
      | k4_xboole_0(A_301,B_302) = C_303 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1671,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_174])).

tff(c_2538,plain,(
    ! [B_302,C_303] :
      ( r2_hidden('#skF_2'('#skF_10',B_302,C_303),C_303)
      | k4_xboole_0('#skF_10',B_302) = C_303 ) ),
    inference(resolution,[status(thm)],[c_2511,c_1671])).

tff(c_2589,plain,(
    ! [B_304,C_305] :
      ( r2_hidden('#skF_2'('#skF_10',B_304,C_305),C_305)
      | C_305 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_2538])).

tff(c_1823,plain,(
    ! [A_231,B_232,D_233] :
      ( r2_hidden('#skF_8'(A_231,B_232,k2_zfmisc_1(A_231,B_232),D_233),B_232)
      | ~ r2_hidden(D_233,k2_zfmisc_1(A_231,B_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1836,plain,(
    ! [D_233,A_231] : ~ r2_hidden(D_233,k2_zfmisc_1(A_231,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_1823,c_1671])).

tff(c_2621,plain,(
    ! [A_231] : k2_zfmisc_1(A_231,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2589,c_1836])).

tff(c_64,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_212,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1669,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_212])).

tff(c_2635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2621,c_1669])).

tff(c_2636,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1665])).

tff(c_2648,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_9') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_26])).

tff(c_2710,plain,(
    ! [A_311] : k3_xboole_0('#skF_9',A_311) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_2636,c_100])).

tff(c_2718,plain,(
    ! [A_311] : k5_xboole_0('#skF_9','#skF_9') = k4_xboole_0('#skF_9',A_311) ),
    inference(superposition,[status(thm),theory(equality)],[c_2710,c_22])).

tff(c_2740,plain,(
    ! [A_311] : k4_xboole_0('#skF_9',A_311) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2648,c_2718])).

tff(c_3315,plain,(
    ! [A_370,B_371,C_372] :
      ( r2_hidden('#skF_1'(A_370,B_371,C_372),A_370)
      | r2_hidden('#skF_2'(A_370,B_371,C_372),C_372)
      | k4_xboole_0(A_370,B_371) = C_372 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2643,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_174])).

tff(c_3363,plain,(
    ! [B_371,C_372] :
      ( r2_hidden('#skF_2'('#skF_9',B_371,C_372),C_372)
      | k4_xboole_0('#skF_9',B_371) = C_372 ) ),
    inference(resolution,[status(thm)],[c_3315,c_2643])).

tff(c_3454,plain,(
    ! [B_373,C_374] :
      ( r2_hidden('#skF_2'('#skF_9',B_373,C_374),C_374)
      | C_374 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2740,c_3363])).

tff(c_2831,plain,(
    ! [A_322,B_323,D_324] :
      ( r2_hidden('#skF_7'(A_322,B_323,k2_zfmisc_1(A_322,B_323),D_324),A_322)
      | ~ r2_hidden(D_324,k2_zfmisc_1(A_322,B_323)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2844,plain,(
    ! [D_324,B_323] : ~ r2_hidden(D_324,k2_zfmisc_1('#skF_9',B_323)) ),
    inference(resolution,[status(thm)],[c_2831,c_2643])).

tff(c_3521,plain,(
    ! [B_323] : k2_zfmisc_1('#skF_9',B_323) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3454,c_2844])).

tff(c_2641,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_212])).

tff(c_3595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3521,c_2641])).

tff(c_3596,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3688,plain,(
    ! [E_385,F_386,A_387,B_388] :
      ( r2_hidden(k4_tarski(E_385,F_386),k2_zfmisc_1(A_387,B_388))
      | ~ r2_hidden(F_386,B_388)
      | ~ r2_hidden(E_385,A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3694,plain,(
    ! [E_385,F_386] :
      ( r2_hidden(k4_tarski(E_385,F_386),k1_xboole_0)
      | ~ r2_hidden(F_386,'#skF_12')
      | ~ r2_hidden(E_385,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3596,c_3688])).

tff(c_3696,plain,(
    ! [F_386,E_385] :
      ( ~ r2_hidden(F_386,'#skF_12')
      | ~ r2_hidden(E_385,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_3694])).

tff(c_3699,plain,(
    ! [E_385] : ~ r2_hidden(E_385,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_3696])).

tff(c_4623,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_4515,c_3699])).

tff(c_4669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_4623])).

tff(c_4670,plain,(
    ! [F_386] : ~ r2_hidden(F_386,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_3696])).

tff(c_5532,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5432,c_4670])).

tff(c_5576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_5532])).

tff(c_5578,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5656,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5578,c_5578,c_5578,c_62])).

tff(c_5657,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_5656])).

tff(c_5577,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_5611,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5578,c_5577])).

tff(c_5660,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5657,c_5611])).

tff(c_5582,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_11') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5578,c_26])).

tff(c_5659,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_9') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5657,c_5582])).

tff(c_5590,plain,(
    ! [A_573] : k3_xboole_0(A_573,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5578,c_5578,c_24])).

tff(c_5604,plain,(
    ! [A_1] : k3_xboole_0('#skF_11',A_1) = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5590])).

tff(c_5713,plain,(
    ! [A_1] : k3_xboole_0('#skF_9',A_1) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5657,c_5657,c_5604])).

tff(c_5759,plain,(
    ! [A_589,B_590] : k5_xboole_0(A_589,k3_xboole_0(A_589,B_590)) = k4_xboole_0(A_589,B_590) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5768,plain,(
    ! [A_1] : k5_xboole_0('#skF_9','#skF_9') = k4_xboole_0('#skF_9',A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_5713,c_5759])).

tff(c_5780,plain,(
    ! [A_1] : k4_xboole_0('#skF_9',A_1) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5659,c_5768])).

tff(c_6385,plain,(
    ! [A_662,B_663,C_664] :
      ( r2_hidden('#skF_1'(A_662,B_663,C_664),A_662)
      | r2_hidden('#skF_2'(A_662,B_663,C_664),C_664)
      | k4_xboole_0(A_662,B_663) = C_664 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5583,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5578,c_28])).

tff(c_5662,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5657,c_5583])).

tff(c_5706,plain,(
    ! [A_579,B_580] :
      ( ~ r2_hidden(A_579,B_580)
      | ~ r1_xboole_0(k1_tarski(A_579),B_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5711,plain,(
    ! [A_579] : ~ r2_hidden(A_579,'#skF_9') ),
    inference(resolution,[status(thm)],[c_5662,c_5706])).

tff(c_6453,plain,(
    ! [B_663,C_664] :
      ( r2_hidden('#skF_2'('#skF_9',B_663,C_664),C_664)
      | k4_xboole_0('#skF_9',B_663) = C_664 ) ),
    inference(resolution,[status(thm)],[c_6385,c_5711])).

tff(c_6554,plain,(
    ! [B_665,C_666] :
      ( r2_hidden('#skF_2'('#skF_9',B_665,C_666),C_666)
      | C_666 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5780,c_6453])).

tff(c_5902,plain,(
    ! [A_607,B_608,D_609] :
      ( r2_hidden('#skF_7'(A_607,B_608,k2_zfmisc_1(A_607,B_608),D_609),A_607)
      | ~ r2_hidden(D_609,k2_zfmisc_1(A_607,B_608)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5922,plain,(
    ! [D_609,B_608] : ~ r2_hidden(D_609,k2_zfmisc_1('#skF_9',B_608)) ),
    inference(resolution,[status(thm)],[c_5902,c_5711])).

tff(c_6635,plain,(
    ! [B_608] : k2_zfmisc_1('#skF_9',B_608) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6554,c_5922])).

tff(c_5664,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5657,c_5578])).

tff(c_5673,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9'
    | k2_zfmisc_1('#skF_9','#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_5657,c_5664,c_64])).

tff(c_5674,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_5673])).

tff(c_6650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6635,c_5674])).

tff(c_6652,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5673])).

tff(c_6689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5660,c_6652])).

tff(c_6690,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_5656])).

tff(c_6693,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_10') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6690,c_5582])).

tff(c_5581,plain,(
    ! [A_11] : k3_xboole_0(A_11,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5578,c_5578,c_24])).

tff(c_6720,plain,(
    ! [A_672] : k3_xboole_0(A_672,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6690,c_6690,c_5581])).

tff(c_6725,plain,(
    ! [A_672] : k3_xboole_0('#skF_10',A_672) = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_6720,c_2])).

tff(c_6789,plain,(
    ! [A_677,B_678] : k5_xboole_0(A_677,k3_xboole_0(A_677,B_678)) = k4_xboole_0(A_677,B_678) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6798,plain,(
    ! [A_672] : k5_xboole_0('#skF_10','#skF_10') = k4_xboole_0('#skF_10',A_672) ),
    inference(superposition,[status(thm),theory(equality)],[c_6725,c_6789])).

tff(c_6810,plain,(
    ! [A_672] : k4_xboole_0('#skF_10',A_672) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6693,c_6798])).

tff(c_7204,plain,(
    ! [A_733,B_734,C_735] :
      ( r2_hidden('#skF_1'(A_733,B_734,C_735),A_733)
      | r2_hidden('#skF_2'(A_733,B_734,C_735),C_735)
      | k4_xboole_0(A_733,B_734) = C_735 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6696,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6690,c_5583])).

tff(c_6741,plain,(
    ! [A_673,B_674] :
      ( ~ r2_hidden(A_673,B_674)
      | ~ r1_xboole_0(k1_tarski(A_673),B_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6746,plain,(
    ! [A_673] : ~ r2_hidden(A_673,'#skF_10') ),
    inference(resolution,[status(thm)],[c_6696,c_6741])).

tff(c_7252,plain,(
    ! [B_734,C_735] :
      ( r2_hidden('#skF_2'('#skF_10',B_734,C_735),C_735)
      | k4_xboole_0('#skF_10',B_734) = C_735 ) ),
    inference(resolution,[status(thm)],[c_7204,c_6746])).

tff(c_7323,plain,(
    ! [B_736,C_737] :
      ( r2_hidden('#skF_2'('#skF_10',B_736,C_737),C_737)
      | C_737 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6810,c_7252])).

tff(c_6937,plain,(
    ! [A_701,B_702,D_703] :
      ( r2_hidden('#skF_8'(A_701,B_702,k2_zfmisc_1(A_701,B_702),D_703),B_702)
      | ~ r2_hidden(D_703,k2_zfmisc_1(A_701,B_702)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6957,plain,(
    ! [D_703,A_701] : ~ r2_hidden(D_703,k2_zfmisc_1(A_701,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_6937,c_6746])).

tff(c_7379,plain,(
    ! [A_701] : k2_zfmisc_1(A_701,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_7323,c_6957])).

tff(c_6694,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6690,c_5611])).

tff(c_7391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7379,c_6694])).

tff(c_7393,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7397,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7393,c_28])).

tff(c_8469,plain,(
    ! [A_832,B_833] :
      ( ~ r2_hidden(A_832,B_833)
      | ~ r1_xboole_0(k1_tarski(A_832),B_833) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8474,plain,(
    ! [A_832] : ~ r2_hidden(A_832,'#skF_12') ),
    inference(resolution,[status(thm)],[c_7397,c_8469])).

tff(c_9580,plain,(
    ! [A_931,B_932] :
      ( r2_hidden('#skF_4'(A_931,B_932,'#skF_12'),A_931)
      | k2_zfmisc_1(A_931,B_932) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_8693,c_8474])).

tff(c_9610,plain,(
    ! [B_932] : k2_zfmisc_1('#skF_12',B_932) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_9580,c_8474])).

tff(c_8060,plain,(
    ! [A_816,B_817,C_818] :
      ( r2_hidden('#skF_5'(A_816,B_817,C_818),B_817)
      | r2_hidden('#skF_6'(A_816,B_817,C_818),C_818)
      | k2_zfmisc_1(A_816,B_817) = C_818 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7485,plain,(
    ! [A_742,B_743] :
      ( ~ r2_hidden(A_742,B_743)
      | ~ r1_xboole_0(k1_tarski(A_742),B_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7490,plain,(
    ! [A_742] : ~ r2_hidden(A_742,'#skF_12') ),
    inference(resolution,[status(thm)],[c_7397,c_7485])).

tff(c_8290,plain,(
    ! [A_827,B_828] :
      ( r2_hidden('#skF_5'(A_827,B_828,'#skF_12'),B_828)
      | k2_zfmisc_1(A_827,B_828) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_8060,c_7490])).

tff(c_8375,plain,(
    ! [A_827] : k2_zfmisc_1(A_827,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8290,c_7490])).

tff(c_7392,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7403,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7393,c_7393,c_7392])).

tff(c_7404,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_7403])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7484,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7393,c_7404,c_7393,c_56])).

tff(c_8385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8375,c_7484])).

tff(c_8386,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_7403])).

tff(c_8468,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7393,c_8386,c_7393,c_56])).

tff(c_9620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9610,c_8468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.14  
% 5.74/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.14  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 5.74/2.14  
% 5.74/2.14  %Foreground sorts:
% 5.74/2.14  
% 5.74/2.14  
% 5.74/2.14  %Background operators:
% 5.74/2.14  
% 5.74/2.14  
% 5.74/2.14  %Foreground operators:
% 5.74/2.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.74/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.74/2.14  tff('#skF_11', type, '#skF_11': $i).
% 5.74/2.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.74/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.74/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.74/2.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.74/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.74/2.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.74/2.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.74/2.14  tff('#skF_10', type, '#skF_10': $i).
% 5.74/2.14  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.74/2.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.74/2.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.74/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.74/2.14  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 5.74/2.14  tff('#skF_9', type, '#skF_9': $i).
% 5.74/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.74/2.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.74/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.74/2.14  tff('#skF_12', type, '#skF_12': $i).
% 5.74/2.14  
% 5.74/2.17  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.74/2.17  tff(f_69, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.74/2.17  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.74/2.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.74/2.17  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.74/2.17  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.74/2.17  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.74/2.17  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.74/2.17  tff(f_62, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 5.74/2.17  tff(c_8693, plain, (![A_870, B_871, C_872]: (r2_hidden('#skF_4'(A_870, B_871, C_872), A_870) | r2_hidden('#skF_6'(A_870, B_871, C_872), C_872) | k2_zfmisc_1(A_870, B_871)=C_872)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.17  tff(c_58, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.17  tff(c_164, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_58])).
% 5.74/2.17  tff(c_26, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.74/2.17  tff(c_84, plain, (![B_53, A_54]: (k3_xboole_0(B_53, A_54)=k3_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.74/2.17  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.17  tff(c_100, plain, (![A_54]: (k3_xboole_0(k1_xboole_0, A_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_84, c_24])).
% 5.74/2.17  tff(c_177, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.74/2.17  tff(c_186, plain, (![A_54]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_54))), inference(superposition, [status(thm), theory('equality')], [c_100, c_177])).
% 5.74/2.17  tff(c_198, plain, (![A_54]: (k4_xboole_0(k1_xboole_0, A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_186])).
% 5.74/2.17  tff(c_5144, plain, (![A_567, B_568, C_569]: (r2_hidden('#skF_1'(A_567, B_568, C_569), A_567) | r2_hidden('#skF_2'(A_567, B_568, C_569), C_569) | k4_xboole_0(A_567, B_568)=C_569)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.17  tff(c_28, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.74/2.17  tff(c_169, plain, (![A_56, B_57]: (~r2_hidden(A_56, B_57) | ~r1_xboole_0(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.74/2.17  tff(c_174, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_169])).
% 5.74/2.17  tff(c_5260, plain, (![B_568, C_569]: (r2_hidden('#skF_2'(k1_xboole_0, B_568, C_569), C_569) | k4_xboole_0(k1_xboole_0, B_568)=C_569)), inference(resolution, [status(thm)], [c_5144, c_174])).
% 5.74/2.17  tff(c_5432, plain, (![B_570, C_571]: (r2_hidden('#skF_2'(k1_xboole_0, B_570, C_571), C_571) | k1_xboole_0=C_571)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_5260])).
% 5.74/2.17  tff(c_60, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.17  tff(c_167, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_60])).
% 5.74/2.17  tff(c_4207, plain, (![A_480, B_481, C_482]: (r2_hidden('#skF_1'(A_480, B_481, C_482), A_480) | r2_hidden('#skF_2'(A_480, B_481, C_482), C_482) | k4_xboole_0(A_480, B_481)=C_482)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.17  tff(c_4331, plain, (![B_481, C_482]: (r2_hidden('#skF_2'(k1_xboole_0, B_481, C_482), C_482) | k4_xboole_0(k1_xboole_0, B_481)=C_482)), inference(resolution, [status(thm)], [c_4207, c_174])).
% 5.74/2.17  tff(c_4515, plain, (![B_483, C_484]: (r2_hidden('#skF_2'(k1_xboole_0, B_483, C_484), C_484) | k1_xboole_0=C_484)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_4331])).
% 5.74/2.17  tff(c_1244, plain, (![A_212, B_213, C_214]: (r2_hidden('#skF_1'(A_212, B_213, C_214), A_212) | r2_hidden('#skF_2'(A_212, B_213, C_214), C_214) | k4_xboole_0(A_212, B_213)=C_214)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.17  tff(c_1355, plain, (![B_213, C_214]: (r2_hidden('#skF_2'(k1_xboole_0, B_213, C_214), C_214) | k4_xboole_0(k1_xboole_0, B_213)=C_214)), inference(resolution, [status(thm)], [c_1244, c_174])).
% 5.74/2.17  tff(c_1524, plain, (![B_215, C_216]: (r2_hidden('#skF_2'(k1_xboole_0, B_215, C_216), C_216) | k1_xboole_0=C_216)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1355])).
% 5.74/2.17  tff(c_555, plain, (![A_117, B_118, C_119]: (r2_hidden('#skF_1'(A_117, B_118, C_119), A_117) | r2_hidden('#skF_2'(A_117, B_118, C_119), C_119) | k4_xboole_0(A_117, B_118)=C_119)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.17  tff(c_615, plain, (![B_118, C_119]: (r2_hidden('#skF_2'(k1_xboole_0, B_118, C_119), C_119) | k4_xboole_0(k1_xboole_0, B_118)=C_119)), inference(resolution, [status(thm)], [c_555, c_174])).
% 5.74/2.17  tff(c_711, plain, (![B_120, C_121]: (r2_hidden('#skF_2'(k1_xboole_0, B_120, C_121), C_121) | k1_xboole_0=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_615])).
% 5.74/2.17  tff(c_66, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.17  tff(c_241, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 5.74/2.17  tff(c_299, plain, (![E_74, F_75, A_76, B_77]: (r2_hidden(k4_tarski(E_74, F_75), k2_zfmisc_1(A_76, B_77)) | ~r2_hidden(F_75, B_77) | ~r2_hidden(E_74, A_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.17  tff(c_302, plain, (![E_74, F_75]: (r2_hidden(k4_tarski(E_74, F_75), k1_xboole_0) | ~r2_hidden(F_75, '#skF_12') | ~r2_hidden(E_74, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_299])).
% 5.74/2.17  tff(c_303, plain, (![F_75, E_74]: (~r2_hidden(F_75, '#skF_12') | ~r2_hidden(E_74, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_174, c_302])).
% 5.74/2.17  tff(c_304, plain, (![E_74]: (~r2_hidden(E_74, '#skF_11'))), inference(splitLeft, [status(thm)], [c_303])).
% 5.74/2.17  tff(c_763, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_711, c_304])).
% 5.74/2.17  tff(c_791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_763])).
% 5.74/2.17  tff(c_792, plain, (![F_75]: (~r2_hidden(F_75, '#skF_12'))), inference(splitRight, [status(thm)], [c_303])).
% 5.74/2.17  tff(c_1624, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_1524, c_792])).
% 5.74/2.17  tff(c_1664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_1624])).
% 5.74/2.17  tff(c_1665, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_66])).
% 5.74/2.17  tff(c_1667, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_1665])).
% 5.74/2.17  tff(c_1676, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_10')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_26])).
% 5.74/2.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.74/2.17  tff(c_1690, plain, (![A_219]: (k3_xboole_0(A_219, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_1667, c_24])).
% 5.74/2.17  tff(c_1723, plain, (![B_221]: (k3_xboole_0('#skF_10', B_221)='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2, c_1690])).
% 5.74/2.17  tff(c_22, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.74/2.17  tff(c_1731, plain, (![B_221]: (k5_xboole_0('#skF_10', '#skF_10')=k4_xboole_0('#skF_10', B_221))), inference(superposition, [status(thm), theory('equality')], [c_1723, c_22])).
% 5.74/2.17  tff(c_1753, plain, (![B_221]: (k4_xboole_0('#skF_10', B_221)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1731])).
% 5.74/2.17  tff(c_2511, plain, (![A_301, B_302, C_303]: (r2_hidden('#skF_1'(A_301, B_302, C_303), A_301) | r2_hidden('#skF_2'(A_301, B_302, C_303), C_303) | k4_xboole_0(A_301, B_302)=C_303)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.17  tff(c_1671, plain, (![A_56]: (~r2_hidden(A_56, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_174])).
% 5.74/2.17  tff(c_2538, plain, (![B_302, C_303]: (r2_hidden('#skF_2'('#skF_10', B_302, C_303), C_303) | k4_xboole_0('#skF_10', B_302)=C_303)), inference(resolution, [status(thm)], [c_2511, c_1671])).
% 5.74/2.17  tff(c_2589, plain, (![B_304, C_305]: (r2_hidden('#skF_2'('#skF_10', B_304, C_305), C_305) | C_305='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1753, c_2538])).
% 5.74/2.17  tff(c_1823, plain, (![A_231, B_232, D_233]: (r2_hidden('#skF_8'(A_231, B_232, k2_zfmisc_1(A_231, B_232), D_233), B_232) | ~r2_hidden(D_233, k2_zfmisc_1(A_231, B_232)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.17  tff(c_1836, plain, (![D_233, A_231]: (~r2_hidden(D_233, k2_zfmisc_1(A_231, '#skF_10')))), inference(resolution, [status(thm)], [c_1823, c_1671])).
% 5.74/2.17  tff(c_2621, plain, (![A_231]: (k2_zfmisc_1(A_231, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_2589, c_1836])).
% 5.74/2.17  tff(c_64, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.17  tff(c_212, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 5.74/2.17  tff(c_1669, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_212])).
% 5.74/2.17  tff(c_2635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2621, c_1669])).
% 5.74/2.17  tff(c_2636, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1665])).
% 5.74/2.17  tff(c_2648, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_9')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_26])).
% 5.74/2.17  tff(c_2710, plain, (![A_311]: (k3_xboole_0('#skF_9', A_311)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_2636, c_100])).
% 5.74/2.17  tff(c_2718, plain, (![A_311]: (k5_xboole_0('#skF_9', '#skF_9')=k4_xboole_0('#skF_9', A_311))), inference(superposition, [status(thm), theory('equality')], [c_2710, c_22])).
% 5.74/2.17  tff(c_2740, plain, (![A_311]: (k4_xboole_0('#skF_9', A_311)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2648, c_2718])).
% 5.74/2.17  tff(c_3315, plain, (![A_370, B_371, C_372]: (r2_hidden('#skF_1'(A_370, B_371, C_372), A_370) | r2_hidden('#skF_2'(A_370, B_371, C_372), C_372) | k4_xboole_0(A_370, B_371)=C_372)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.17  tff(c_2643, plain, (![A_56]: (~r2_hidden(A_56, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_174])).
% 5.74/2.17  tff(c_3363, plain, (![B_371, C_372]: (r2_hidden('#skF_2'('#skF_9', B_371, C_372), C_372) | k4_xboole_0('#skF_9', B_371)=C_372)), inference(resolution, [status(thm)], [c_3315, c_2643])).
% 5.74/2.17  tff(c_3454, plain, (![B_373, C_374]: (r2_hidden('#skF_2'('#skF_9', B_373, C_374), C_374) | C_374='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2740, c_3363])).
% 5.74/2.17  tff(c_2831, plain, (![A_322, B_323, D_324]: (r2_hidden('#skF_7'(A_322, B_323, k2_zfmisc_1(A_322, B_323), D_324), A_322) | ~r2_hidden(D_324, k2_zfmisc_1(A_322, B_323)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.17  tff(c_2844, plain, (![D_324, B_323]: (~r2_hidden(D_324, k2_zfmisc_1('#skF_9', B_323)))), inference(resolution, [status(thm)], [c_2831, c_2643])).
% 5.74/2.17  tff(c_3521, plain, (![B_323]: (k2_zfmisc_1('#skF_9', B_323)='#skF_9')), inference(resolution, [status(thm)], [c_3454, c_2844])).
% 5.74/2.17  tff(c_2641, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_212])).
% 5.74/2.17  tff(c_3595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3521, c_2641])).
% 5.74/2.17  tff(c_3596, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 5.74/2.17  tff(c_3688, plain, (![E_385, F_386, A_387, B_388]: (r2_hidden(k4_tarski(E_385, F_386), k2_zfmisc_1(A_387, B_388)) | ~r2_hidden(F_386, B_388) | ~r2_hidden(E_385, A_387))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.17  tff(c_3694, plain, (![E_385, F_386]: (r2_hidden(k4_tarski(E_385, F_386), k1_xboole_0) | ~r2_hidden(F_386, '#skF_12') | ~r2_hidden(E_385, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_3596, c_3688])).
% 5.74/2.17  tff(c_3696, plain, (![F_386, E_385]: (~r2_hidden(F_386, '#skF_12') | ~r2_hidden(E_385, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_174, c_3694])).
% 5.74/2.17  tff(c_3699, plain, (![E_385]: (~r2_hidden(E_385, '#skF_11'))), inference(splitLeft, [status(thm)], [c_3696])).
% 5.74/2.17  tff(c_4623, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_4515, c_3699])).
% 5.74/2.17  tff(c_4669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_4623])).
% 5.74/2.17  tff(c_4670, plain, (![F_386]: (~r2_hidden(F_386, '#skF_12'))), inference(splitRight, [status(thm)], [c_3696])).
% 5.74/2.17  tff(c_5532, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_5432, c_4670])).
% 5.74/2.17  tff(c_5576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_5532])).
% 5.74/2.17  tff(c_5578, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_60])).
% 5.74/2.17  tff(c_62, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.17  tff(c_5656, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5578, c_5578, c_5578, c_62])).
% 5.74/2.17  tff(c_5657, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_5656])).
% 5.74/2.17  tff(c_5577, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 5.74/2.17  tff(c_5611, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_5578, c_5577])).
% 5.74/2.17  tff(c_5660, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5657, c_5611])).
% 5.74/2.17  tff(c_5582, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_11')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_5578, c_26])).
% 5.74/2.17  tff(c_5659, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_9')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_5657, c_5582])).
% 5.74/2.17  tff(c_5590, plain, (![A_573]: (k3_xboole_0(A_573, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_5578, c_5578, c_24])).
% 5.74/2.17  tff(c_5604, plain, (![A_1]: (k3_xboole_0('#skF_11', A_1)='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_2, c_5590])).
% 5.74/2.17  tff(c_5713, plain, (![A_1]: (k3_xboole_0('#skF_9', A_1)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5657, c_5657, c_5604])).
% 5.74/2.17  tff(c_5759, plain, (![A_589, B_590]: (k5_xboole_0(A_589, k3_xboole_0(A_589, B_590))=k4_xboole_0(A_589, B_590))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.74/2.17  tff(c_5768, plain, (![A_1]: (k5_xboole_0('#skF_9', '#skF_9')=k4_xboole_0('#skF_9', A_1))), inference(superposition, [status(thm), theory('equality')], [c_5713, c_5759])).
% 5.74/2.17  tff(c_5780, plain, (![A_1]: (k4_xboole_0('#skF_9', A_1)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5659, c_5768])).
% 5.74/2.17  tff(c_6385, plain, (![A_662, B_663, C_664]: (r2_hidden('#skF_1'(A_662, B_663, C_664), A_662) | r2_hidden('#skF_2'(A_662, B_663, C_664), C_664) | k4_xboole_0(A_662, B_663)=C_664)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.17  tff(c_5583, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_5578, c_28])).
% 5.74/2.17  tff(c_5662, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_5657, c_5583])).
% 5.74/2.17  tff(c_5706, plain, (![A_579, B_580]: (~r2_hidden(A_579, B_580) | ~r1_xboole_0(k1_tarski(A_579), B_580))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.74/2.17  tff(c_5711, plain, (![A_579]: (~r2_hidden(A_579, '#skF_9'))), inference(resolution, [status(thm)], [c_5662, c_5706])).
% 5.74/2.17  tff(c_6453, plain, (![B_663, C_664]: (r2_hidden('#skF_2'('#skF_9', B_663, C_664), C_664) | k4_xboole_0('#skF_9', B_663)=C_664)), inference(resolution, [status(thm)], [c_6385, c_5711])).
% 5.74/2.17  tff(c_6554, plain, (![B_665, C_666]: (r2_hidden('#skF_2'('#skF_9', B_665, C_666), C_666) | C_666='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5780, c_6453])).
% 5.74/2.17  tff(c_5902, plain, (![A_607, B_608, D_609]: (r2_hidden('#skF_7'(A_607, B_608, k2_zfmisc_1(A_607, B_608), D_609), A_607) | ~r2_hidden(D_609, k2_zfmisc_1(A_607, B_608)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.17  tff(c_5922, plain, (![D_609, B_608]: (~r2_hidden(D_609, k2_zfmisc_1('#skF_9', B_608)))), inference(resolution, [status(thm)], [c_5902, c_5711])).
% 5.74/2.17  tff(c_6635, plain, (![B_608]: (k2_zfmisc_1('#skF_9', B_608)='#skF_9')), inference(resolution, [status(thm)], [c_6554, c_5922])).
% 5.74/2.17  tff(c_5664, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5657, c_5578])).
% 5.74/2.17  tff(c_5673, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9' | k2_zfmisc_1('#skF_9', '#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_5657, c_5664, c_64])).
% 5.74/2.17  tff(c_5674, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(splitLeft, [status(thm)], [c_5673])).
% 5.74/2.17  tff(c_6650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6635, c_5674])).
% 5.74/2.17  tff(c_6652, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_5673])).
% 5.74/2.17  tff(c_6689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5660, c_6652])).
% 5.74/2.17  tff(c_6690, plain, ('#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_5656])).
% 5.74/2.17  tff(c_6693, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_10')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_6690, c_5582])).
% 5.74/2.17  tff(c_5581, plain, (![A_11]: (k3_xboole_0(A_11, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_5578, c_5578, c_24])).
% 5.74/2.17  tff(c_6720, plain, (![A_672]: (k3_xboole_0(A_672, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_6690, c_6690, c_5581])).
% 5.74/2.17  tff(c_6725, plain, (![A_672]: (k3_xboole_0('#skF_10', A_672)='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6720, c_2])).
% 5.74/2.17  tff(c_6789, plain, (![A_677, B_678]: (k5_xboole_0(A_677, k3_xboole_0(A_677, B_678))=k4_xboole_0(A_677, B_678))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.74/2.17  tff(c_6798, plain, (![A_672]: (k5_xboole_0('#skF_10', '#skF_10')=k4_xboole_0('#skF_10', A_672))), inference(superposition, [status(thm), theory('equality')], [c_6725, c_6789])).
% 5.74/2.17  tff(c_6810, plain, (![A_672]: (k4_xboole_0('#skF_10', A_672)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_6693, c_6798])).
% 5.74/2.17  tff(c_7204, plain, (![A_733, B_734, C_735]: (r2_hidden('#skF_1'(A_733, B_734, C_735), A_733) | r2_hidden('#skF_2'(A_733, B_734, C_735), C_735) | k4_xboole_0(A_733, B_734)=C_735)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.17  tff(c_6696, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_6690, c_5583])).
% 5.74/2.17  tff(c_6741, plain, (![A_673, B_674]: (~r2_hidden(A_673, B_674) | ~r1_xboole_0(k1_tarski(A_673), B_674))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.74/2.17  tff(c_6746, plain, (![A_673]: (~r2_hidden(A_673, '#skF_10'))), inference(resolution, [status(thm)], [c_6696, c_6741])).
% 5.74/2.17  tff(c_7252, plain, (![B_734, C_735]: (r2_hidden('#skF_2'('#skF_10', B_734, C_735), C_735) | k4_xboole_0('#skF_10', B_734)=C_735)), inference(resolution, [status(thm)], [c_7204, c_6746])).
% 5.74/2.17  tff(c_7323, plain, (![B_736, C_737]: (r2_hidden('#skF_2'('#skF_10', B_736, C_737), C_737) | C_737='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_6810, c_7252])).
% 5.74/2.17  tff(c_6937, plain, (![A_701, B_702, D_703]: (r2_hidden('#skF_8'(A_701, B_702, k2_zfmisc_1(A_701, B_702), D_703), B_702) | ~r2_hidden(D_703, k2_zfmisc_1(A_701, B_702)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.17  tff(c_6957, plain, (![D_703, A_701]: (~r2_hidden(D_703, k2_zfmisc_1(A_701, '#skF_10')))), inference(resolution, [status(thm)], [c_6937, c_6746])).
% 5.74/2.17  tff(c_7379, plain, (![A_701]: (k2_zfmisc_1(A_701, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_7323, c_6957])).
% 5.74/2.17  tff(c_6694, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6690, c_5611])).
% 5.74/2.17  tff(c_7391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7379, c_6694])).
% 5.74/2.17  tff(c_7393, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_58])).
% 5.74/2.17  tff(c_7397, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_7393, c_28])).
% 5.74/2.17  tff(c_8469, plain, (![A_832, B_833]: (~r2_hidden(A_832, B_833) | ~r1_xboole_0(k1_tarski(A_832), B_833))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.74/2.17  tff(c_8474, plain, (![A_832]: (~r2_hidden(A_832, '#skF_12'))), inference(resolution, [status(thm)], [c_7397, c_8469])).
% 5.74/2.17  tff(c_9580, plain, (![A_931, B_932]: (r2_hidden('#skF_4'(A_931, B_932, '#skF_12'), A_931) | k2_zfmisc_1(A_931, B_932)='#skF_12')), inference(resolution, [status(thm)], [c_8693, c_8474])).
% 5.74/2.17  tff(c_9610, plain, (![B_932]: (k2_zfmisc_1('#skF_12', B_932)='#skF_12')), inference(resolution, [status(thm)], [c_9580, c_8474])).
% 5.74/2.17  tff(c_8060, plain, (![A_816, B_817, C_818]: (r2_hidden('#skF_5'(A_816, B_817, C_818), B_817) | r2_hidden('#skF_6'(A_816, B_817, C_818), C_818) | k2_zfmisc_1(A_816, B_817)=C_818)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.17  tff(c_7485, plain, (![A_742, B_743]: (~r2_hidden(A_742, B_743) | ~r1_xboole_0(k1_tarski(A_742), B_743))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.74/2.17  tff(c_7490, plain, (![A_742]: (~r2_hidden(A_742, '#skF_12'))), inference(resolution, [status(thm)], [c_7397, c_7485])).
% 5.74/2.17  tff(c_8290, plain, (![A_827, B_828]: (r2_hidden('#skF_5'(A_827, B_828, '#skF_12'), B_828) | k2_zfmisc_1(A_827, B_828)='#skF_12')), inference(resolution, [status(thm)], [c_8060, c_7490])).
% 5.74/2.17  tff(c_8375, plain, (![A_827]: (k2_zfmisc_1(A_827, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_8290, c_7490])).
% 5.74/2.17  tff(c_7392, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_58])).
% 5.74/2.17  tff(c_7403, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_7393, c_7393, c_7392])).
% 5.74/2.17  tff(c_7404, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_7403])).
% 5.74/2.17  tff(c_56, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.17  tff(c_7484, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_7393, c_7404, c_7393, c_56])).
% 5.74/2.17  tff(c_8385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8375, c_7484])).
% 5.74/2.17  tff(c_8386, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_7403])).
% 5.74/2.17  tff(c_8468, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_7393, c_8386, c_7393, c_56])).
% 5.74/2.17  tff(c_9620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9610, c_8468])).
% 5.74/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.17  
% 5.74/2.17  Inference rules
% 5.74/2.17  ----------------------
% 5.74/2.17  #Ref     : 0
% 5.74/2.17  #Sup     : 1924
% 5.74/2.17  #Fact    : 0
% 5.74/2.17  #Define  : 0
% 5.74/2.17  #Split   : 14
% 5.74/2.17  #Chain   : 0
% 5.74/2.17  #Close   : 0
% 5.74/2.17  
% 5.74/2.17  Ordering : KBO
% 5.74/2.17  
% 5.74/2.17  Simplification rules
% 5.74/2.17  ----------------------
% 5.74/2.17  #Subsume      : 412
% 5.74/2.17  #Demod        : 494
% 5.74/2.17  #Tautology    : 390
% 5.74/2.17  #SimpNegUnit  : 53
% 5.74/2.17  #BackRed      : 111
% 5.74/2.17  
% 5.74/2.17  #Partial instantiations: 0
% 5.74/2.17  #Strategies tried      : 1
% 5.74/2.17  
% 5.74/2.17  Timing (in seconds)
% 5.74/2.17  ----------------------
% 5.74/2.17  Preprocessing        : 0.31
% 5.74/2.17  Parsing              : 0.15
% 5.74/2.17  CNF conversion       : 0.03
% 5.74/2.17  Main loop            : 1.06
% 5.74/2.17  Inferencing          : 0.42
% 5.74/2.17  Reduction            : 0.29
% 5.74/2.17  Demodulation         : 0.17
% 5.74/2.17  BG Simplification    : 0.05
% 5.74/2.17  Subsumption          : 0.20
% 5.74/2.17  Abstraction          : 0.06
% 5.74/2.17  MUC search           : 0.00
% 5.74/2.17  Cooper               : 0.00
% 5.74/2.17  Total                : 1.42
% 5.74/2.17  Index Insertion      : 0.00
% 5.74/2.17  Index Deletion       : 0.00
% 5.74/2.17  Index Matching       : 0.00
% 5.74/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
