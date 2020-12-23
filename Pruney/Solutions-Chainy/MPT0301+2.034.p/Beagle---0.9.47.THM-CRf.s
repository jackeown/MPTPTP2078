%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:44 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 435 expanded)
%              Number of leaves         :   33 ( 145 expanded)
%              Depth                    :    9
%              Number of atoms          :  177 ( 795 expanded)
%              Number of equality atoms :   79 ( 557 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_1331,plain,(
    ! [A_387,B_388] :
      ( r2_hidden('#skF_1'(A_387,B_388),B_388)
      | r2_hidden('#skF_2'(A_387,B_388),A_387)
      | B_388 = A_387 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1177,plain,(
    ! [A_342,B_343] :
      ( r2_hidden('#skF_1'(A_342,B_343),B_343)
      | r2_hidden('#skF_2'(A_342,B_343),A_342)
      | B_343 = A_342 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1013,plain,(
    ! [A_295,B_296] :
      ( r2_hidden('#skF_1'(A_295,B_296),B_296)
      | r2_hidden('#skF_2'(A_295,B_296),A_295)
      | B_296 = A_295 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_69,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_120,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99,B_100),B_100)
      | r2_hidden('#skF_2'(A_99,B_100),A_99)
      | B_100 = A_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_85,plain,(
    ! [A_76,C_77,B_78] :
      ( ~ r2_hidden(A_76,C_77)
      | ~ r1_xboole_0(k2_tarski(A_76,B_78),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,(
    ! [A_76] : ~ r2_hidden(A_76,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_134,plain,(
    ! [B_100] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_100),B_100)
      | k1_xboole_0 = B_100 ) ),
    inference(resolution,[status(thm)],[c_120,c_90])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_79,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_158,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( r2_hidden(k4_tarski(A_104,B_105),k2_zfmisc_1(C_106,D_107))
      | ~ r2_hidden(B_105,D_107)
      | ~ r2_hidden(A_104,C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,(
    ! [A_104,B_105] :
      ( r2_hidden(k4_tarski(A_104,B_105),k1_xboole_0)
      | ~ r2_hidden(B_105,'#skF_12')
      | ~ r2_hidden(A_104,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_158])).

tff(c_170,plain,(
    ! [B_105,A_104] :
      ( ~ r2_hidden(B_105,'#skF_12')
      | ~ r2_hidden(A_104,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_167])).

tff(c_181,plain,(
    ! [A_113] : ~ r2_hidden(A_113,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_189,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_134,c_181])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_189])).

tff(c_202,plain,(
    ! [B_114] : ~ r2_hidden(B_114,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_210,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_134,c_202])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_210])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_224,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_277,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_1'(A_141,B_142),B_142)
      | r2_hidden('#skF_2'(A_141,B_142),A_141)
      | B_142 = A_141 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_228,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_10])).

tff(c_236,plain,(
    ! [A_116,C_117,B_118] :
      ( ~ r2_hidden(A_116,C_117)
      | ~ r1_xboole_0(k2_tarski(A_116,B_118),C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_241,plain,(
    ! [A_116] : ~ r2_hidden(A_116,'#skF_10') ),
    inference(resolution,[status(thm)],[c_228,c_236])).

tff(c_291,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_1'('#skF_10',B_142),B_142)
      | B_142 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_277,c_241])).

tff(c_400,plain,(
    ! [A_160,B_161,D_162] :
      ( r2_hidden('#skF_8'(A_160,B_161,k2_zfmisc_1(A_160,B_161),D_162),B_161)
      | ~ r2_hidden(D_162,k2_zfmisc_1(A_160,B_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_410,plain,(
    ! [D_163,A_164] : ~ r2_hidden(D_163,k2_zfmisc_1(A_164,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_400,c_241])).

tff(c_450,plain,(
    ! [A_164] : k2_zfmisc_1(A_164,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_291,c_410])).

tff(c_64,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_225,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_234,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_225])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_234])).

tff(c_458,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_473,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_458])).

tff(c_223,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_224,c_223])).

tff(c_480,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_696,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_223])).

tff(c_534,plain,(
    ! [A_190,B_191] :
      ( r2_hidden('#skF_1'(A_190,B_191),B_191)
      | r2_hidden('#skF_2'(A_190,B_191),A_190)
      | B_191 = A_190 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_484,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_10])).

tff(c_494,plain,(
    ! [A_167,C_168,B_169] :
      ( ~ r2_hidden(A_167,C_168)
      | ~ r1_xboole_0(k2_tarski(A_167,B_169),C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_499,plain,(
    ! [A_167] : ~ r2_hidden(A_167,'#skF_9') ),
    inference(resolution,[status(thm)],[c_484,c_494])).

tff(c_547,plain,(
    ! [B_191] :
      ( r2_hidden('#skF_1'('#skF_9',B_191),B_191)
      | B_191 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_534,c_499])).

tff(c_640,plain,(
    ! [A_210,B_211,D_212] :
      ( r2_hidden('#skF_7'(A_210,B_211,k2_zfmisc_1(A_210,B_211),D_212),A_210)
      | ~ r2_hidden(D_212,k2_zfmisc_1(A_210,B_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_650,plain,(
    ! [D_213,B_214] : ~ r2_hidden(D_213,k2_zfmisc_1('#skF_9',B_214)) ),
    inference(resolution,[status(thm)],[c_640,c_499])).

tff(c_685,plain,(
    ! [B_214] : k2_zfmisc_1('#skF_9',B_214) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_547,c_650])).

tff(c_490,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_480,c_64])).

tff(c_491,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_491])).

tff(c_693,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_693])).

tff(c_699,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_701,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_10])).

tff(c_972,plain,(
    ! [A_270,C_271,B_272] :
      ( ~ r2_hidden(A_270,C_271)
      | ~ r1_xboole_0(k2_tarski(A_270,B_272),C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_977,plain,(
    ! [A_270] : ~ r2_hidden(A_270,'#skF_12') ),
    inference(resolution,[status(thm)],[c_701,c_972])).

tff(c_1027,plain,(
    ! [B_296] :
      ( r2_hidden('#skF_1'('#skF_12',B_296),B_296)
      | B_296 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_1013,c_977])).

tff(c_1057,plain,(
    ! [A_307,B_308,D_309] :
      ( r2_hidden('#skF_7'(A_307,B_308,k2_zfmisc_1(A_307,B_308),D_309),A_307)
      | ~ r2_hidden(D_309,k2_zfmisc_1(A_307,B_308)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1069,plain,(
    ! [D_313,B_314] : ~ r2_hidden(D_313,k2_zfmisc_1('#skF_12',B_314)) ),
    inference(resolution,[status(thm)],[c_1057,c_977])).

tff(c_1100,plain,(
    ! [B_314] : k2_zfmisc_1('#skF_12',B_314) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1027,c_1069])).

tff(c_769,plain,(
    ! [A_244,B_245] :
      ( r2_hidden('#skF_1'(A_244,B_245),B_245)
      | r2_hidden('#skF_2'(A_244,B_245),A_244)
      | B_245 = A_244 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_728,plain,(
    ! [A_219,C_220,B_221] :
      ( ~ r2_hidden(A_219,C_220)
      | ~ r1_xboole_0(k2_tarski(A_219,B_221),C_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_733,plain,(
    ! [A_219] : ~ r2_hidden(A_219,'#skF_12') ),
    inference(resolution,[status(thm)],[c_701,c_728])).

tff(c_783,plain,(
    ! [B_245] :
      ( r2_hidden('#skF_1'('#skF_12',B_245),B_245)
      | B_245 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_769,c_733])).

tff(c_892,plain,(
    ! [A_263,B_264,D_265] :
      ( r2_hidden('#skF_8'(A_263,B_264,k2_zfmisc_1(A_263,B_264),D_265),B_264)
      | ~ r2_hidden(D_265,k2_zfmisc_1(A_263,B_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_902,plain,(
    ! [D_266,A_267] : ~ r2_hidden(D_266,k2_zfmisc_1(A_267,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_892,c_733])).

tff(c_942,plain,(
    ! [A_267] : k2_zfmisc_1(A_267,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_783,c_902])).

tff(c_698,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_707,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_699,c_698])).

tff(c_708,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_710,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_699,c_56])).

tff(c_711,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_710])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_711])).

tff(c_950,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_957,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_950,c_699,c_56])).

tff(c_1108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_957])).

tff(c_1110,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1122,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1110,c_1110,c_62])).

tff(c_1123,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1122])).

tff(c_1111,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_10])).

tff(c_1127,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1111])).

tff(c_1148,plain,(
    ! [A_319,C_320,B_321] :
      ( ~ r2_hidden(A_319,C_320)
      | ~ r1_xboole_0(k2_tarski(A_319,B_321),C_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1153,plain,(
    ! [A_319] : ~ r2_hidden(A_319,'#skF_9') ),
    inference(resolution,[status(thm)],[c_1127,c_1148])).

tff(c_1191,plain,(
    ! [B_343] :
      ( r2_hidden('#skF_1'('#skF_9',B_343),B_343)
      | B_343 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1177,c_1153])).

tff(c_1233,plain,(
    ! [A_356,B_357,D_358] :
      ( r2_hidden('#skF_7'(A_356,B_357,k2_zfmisc_1(A_356,B_357),D_358),A_356)
      | ~ r2_hidden(D_358,k2_zfmisc_1(A_356,B_357)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1239,plain,(
    ! [D_359,B_360] : ~ r2_hidden(D_359,k2_zfmisc_1('#skF_9',B_360)) ),
    inference(resolution,[status(thm)],[c_1233,c_1153])).

tff(c_1267,plain,(
    ! [B_360] : k2_zfmisc_1('#skF_9',B_360) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1191,c_1239])).

tff(c_1109,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1117,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1109])).

tff(c_1126,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1117])).

tff(c_1273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1267,c_1126])).

tff(c_1274,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_1122])).

tff(c_1278,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1111])).

tff(c_1301,plain,(
    ! [A_364,C_365,B_366] :
      ( ~ r2_hidden(A_364,C_365)
      | ~ r1_xboole_0(k2_tarski(A_364,B_366),C_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1306,plain,(
    ! [A_364] : ~ r2_hidden(A_364,'#skF_10') ),
    inference(resolution,[status(thm)],[c_1278,c_1301])).

tff(c_1345,plain,(
    ! [B_388] :
      ( r2_hidden('#skF_1'('#skF_10',B_388),B_388)
      | B_388 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1331,c_1306])).

tff(c_1387,plain,(
    ! [A_401,B_402,D_403] :
      ( r2_hidden('#skF_8'(A_401,B_402,k2_zfmisc_1(A_401,B_402),D_403),B_402)
      | ~ r2_hidden(D_403,k2_zfmisc_1(A_401,B_402)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1393,plain,(
    ! [D_404,A_405] : ~ r2_hidden(D_404,k2_zfmisc_1(A_405,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_1387,c_1306])).

tff(c_1421,plain,(
    ! [A_405] : k2_zfmisc_1(A_405,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1345,c_1393])).

tff(c_1277,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1117])).

tff(c_1427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_1277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:08:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.45  
% 2.98/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.45  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 2.98/1.45  
% 2.98/1.45  %Foreground sorts:
% 2.98/1.45  
% 2.98/1.45  
% 2.98/1.45  %Background operators:
% 2.98/1.45  
% 2.98/1.45  
% 2.98/1.45  %Foreground operators:
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.45  tff('#skF_11', type, '#skF_11': $i).
% 2.98/1.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.98/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.98/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.98/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.45  tff('#skF_10', type, '#skF_10': $i).
% 2.98/1.45  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.98/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.98/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.98/1.45  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.98/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.45  tff('#skF_9', type, '#skF_9': $i).
% 2.98/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.98/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.45  tff('#skF_12', type, '#skF_12': $i).
% 2.98/1.45  
% 3.12/1.47  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.12/1.47  tff(f_76, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.12/1.47  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.12/1.47  tff(f_69, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.12/1.47  tff(f_64, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.12/1.47  tff(f_58, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.12/1.47  tff(c_1331, plain, (![A_387, B_388]: (r2_hidden('#skF_1'(A_387, B_388), B_388) | r2_hidden('#skF_2'(A_387, B_388), A_387) | B_388=A_387)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.47  tff(c_1177, plain, (![A_342, B_343]: (r2_hidden('#skF_1'(A_342, B_343), B_343) | r2_hidden('#skF_2'(A_342, B_343), A_342) | B_343=A_342)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.47  tff(c_1013, plain, (![A_295, B_296]: (r2_hidden('#skF_1'(A_295, B_296), B_296) | r2_hidden('#skF_2'(A_295, B_296), A_295) | B_296=A_295)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.47  tff(c_58, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.47  tff(c_69, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_58])).
% 3.12/1.47  tff(c_120, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99, B_100), B_100) | r2_hidden('#skF_2'(A_99, B_100), A_99) | B_100=A_99)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.47  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.12/1.47  tff(c_85, plain, (![A_76, C_77, B_78]: (~r2_hidden(A_76, C_77) | ~r1_xboole_0(k2_tarski(A_76, B_78), C_77))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.47  tff(c_90, plain, (![A_76]: (~r2_hidden(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_85])).
% 3.12/1.47  tff(c_134, plain, (![B_100]: (r2_hidden('#skF_1'(k1_xboole_0, B_100), B_100) | k1_xboole_0=B_100)), inference(resolution, [status(thm)], [c_120, c_90])).
% 3.12/1.47  tff(c_60, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.47  tff(c_68, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_60])).
% 3.12/1.47  tff(c_66, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.47  tff(c_79, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 3.12/1.47  tff(c_158, plain, (![A_104, B_105, C_106, D_107]: (r2_hidden(k4_tarski(A_104, B_105), k2_zfmisc_1(C_106, D_107)) | ~r2_hidden(B_105, D_107) | ~r2_hidden(A_104, C_106))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.12/1.47  tff(c_167, plain, (![A_104, B_105]: (r2_hidden(k4_tarski(A_104, B_105), k1_xboole_0) | ~r2_hidden(B_105, '#skF_12') | ~r2_hidden(A_104, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_158])).
% 3.12/1.47  tff(c_170, plain, (![B_105, A_104]: (~r2_hidden(B_105, '#skF_12') | ~r2_hidden(A_104, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_90, c_167])).
% 3.12/1.47  tff(c_181, plain, (![A_113]: (~r2_hidden(A_113, '#skF_11'))), inference(splitLeft, [status(thm)], [c_170])).
% 3.12/1.47  tff(c_189, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_134, c_181])).
% 3.12/1.47  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_189])).
% 3.12/1.47  tff(c_202, plain, (![B_114]: (~r2_hidden(B_114, '#skF_12'))), inference(splitRight, [status(thm)], [c_170])).
% 3.12/1.47  tff(c_210, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_134, c_202])).
% 3.12/1.47  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_210])).
% 3.12/1.47  tff(c_222, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_66])).
% 3.12/1.47  tff(c_224, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_222])).
% 3.12/1.47  tff(c_277, plain, (![A_141, B_142]: (r2_hidden('#skF_1'(A_141, B_142), B_142) | r2_hidden('#skF_2'(A_141, B_142), A_141) | B_142=A_141)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.47  tff(c_228, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_10])).
% 3.12/1.47  tff(c_236, plain, (![A_116, C_117, B_118]: (~r2_hidden(A_116, C_117) | ~r1_xboole_0(k2_tarski(A_116, B_118), C_117))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.47  tff(c_241, plain, (![A_116]: (~r2_hidden(A_116, '#skF_10'))), inference(resolution, [status(thm)], [c_228, c_236])).
% 3.12/1.47  tff(c_291, plain, (![B_142]: (r2_hidden('#skF_1'('#skF_10', B_142), B_142) | B_142='#skF_10')), inference(resolution, [status(thm)], [c_277, c_241])).
% 3.12/1.47  tff(c_400, plain, (![A_160, B_161, D_162]: (r2_hidden('#skF_8'(A_160, B_161, k2_zfmisc_1(A_160, B_161), D_162), B_161) | ~r2_hidden(D_162, k2_zfmisc_1(A_160, B_161)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.47  tff(c_410, plain, (![D_163, A_164]: (~r2_hidden(D_163, k2_zfmisc_1(A_164, '#skF_10')))), inference(resolution, [status(thm)], [c_400, c_241])).
% 3.12/1.47  tff(c_450, plain, (![A_164]: (k2_zfmisc_1(A_164, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_291, c_410])).
% 3.12/1.47  tff(c_64, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.47  tff(c_225, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 3.12/1.47  tff(c_234, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_225])).
% 3.12/1.47  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_450, c_234])).
% 3.12/1.47  tff(c_458, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 3.12/1.47  tff(c_473, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_458])).
% 3.12/1.47  tff(c_223, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 3.12/1.47  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_473, c_224, c_223])).
% 3.12/1.47  tff(c_480, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_222])).
% 3.12/1.47  tff(c_696, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_223])).
% 3.12/1.47  tff(c_534, plain, (![A_190, B_191]: (r2_hidden('#skF_1'(A_190, B_191), B_191) | r2_hidden('#skF_2'(A_190, B_191), A_190) | B_191=A_190)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.47  tff(c_484, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_10])).
% 3.12/1.47  tff(c_494, plain, (![A_167, C_168, B_169]: (~r2_hidden(A_167, C_168) | ~r1_xboole_0(k2_tarski(A_167, B_169), C_168))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.47  tff(c_499, plain, (![A_167]: (~r2_hidden(A_167, '#skF_9'))), inference(resolution, [status(thm)], [c_484, c_494])).
% 3.12/1.47  tff(c_547, plain, (![B_191]: (r2_hidden('#skF_1'('#skF_9', B_191), B_191) | B_191='#skF_9')), inference(resolution, [status(thm)], [c_534, c_499])).
% 3.12/1.47  tff(c_640, plain, (![A_210, B_211, D_212]: (r2_hidden('#skF_7'(A_210, B_211, k2_zfmisc_1(A_210, B_211), D_212), A_210) | ~r2_hidden(D_212, k2_zfmisc_1(A_210, B_211)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.47  tff(c_650, plain, (![D_213, B_214]: (~r2_hidden(D_213, k2_zfmisc_1('#skF_9', B_214)))), inference(resolution, [status(thm)], [c_640, c_499])).
% 3.12/1.47  tff(c_685, plain, (![B_214]: (k2_zfmisc_1('#skF_9', B_214)='#skF_9')), inference(resolution, [status(thm)], [c_547, c_650])).
% 3.12/1.47  tff(c_490, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_480, c_64])).
% 3.12/1.47  tff(c_491, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(splitLeft, [status(thm)], [c_490])).
% 3.12/1.47  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_685, c_491])).
% 3.12/1.47  tff(c_693, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(splitRight, [status(thm)], [c_490])).
% 3.12/1.47  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_696, c_693])).
% 3.12/1.47  tff(c_699, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_58])).
% 3.12/1.47  tff(c_701, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_10])).
% 3.12/1.47  tff(c_972, plain, (![A_270, C_271, B_272]: (~r2_hidden(A_270, C_271) | ~r1_xboole_0(k2_tarski(A_270, B_272), C_271))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.47  tff(c_977, plain, (![A_270]: (~r2_hidden(A_270, '#skF_12'))), inference(resolution, [status(thm)], [c_701, c_972])).
% 3.12/1.47  tff(c_1027, plain, (![B_296]: (r2_hidden('#skF_1'('#skF_12', B_296), B_296) | B_296='#skF_12')), inference(resolution, [status(thm)], [c_1013, c_977])).
% 3.12/1.47  tff(c_1057, plain, (![A_307, B_308, D_309]: (r2_hidden('#skF_7'(A_307, B_308, k2_zfmisc_1(A_307, B_308), D_309), A_307) | ~r2_hidden(D_309, k2_zfmisc_1(A_307, B_308)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.47  tff(c_1069, plain, (![D_313, B_314]: (~r2_hidden(D_313, k2_zfmisc_1('#skF_12', B_314)))), inference(resolution, [status(thm)], [c_1057, c_977])).
% 3.12/1.47  tff(c_1100, plain, (![B_314]: (k2_zfmisc_1('#skF_12', B_314)='#skF_12')), inference(resolution, [status(thm)], [c_1027, c_1069])).
% 3.12/1.47  tff(c_769, plain, (![A_244, B_245]: (r2_hidden('#skF_1'(A_244, B_245), B_245) | r2_hidden('#skF_2'(A_244, B_245), A_244) | B_245=A_244)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.47  tff(c_728, plain, (![A_219, C_220, B_221]: (~r2_hidden(A_219, C_220) | ~r1_xboole_0(k2_tarski(A_219, B_221), C_220))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.47  tff(c_733, plain, (![A_219]: (~r2_hidden(A_219, '#skF_12'))), inference(resolution, [status(thm)], [c_701, c_728])).
% 3.12/1.47  tff(c_783, plain, (![B_245]: (r2_hidden('#skF_1'('#skF_12', B_245), B_245) | B_245='#skF_12')), inference(resolution, [status(thm)], [c_769, c_733])).
% 3.12/1.47  tff(c_892, plain, (![A_263, B_264, D_265]: (r2_hidden('#skF_8'(A_263, B_264, k2_zfmisc_1(A_263, B_264), D_265), B_264) | ~r2_hidden(D_265, k2_zfmisc_1(A_263, B_264)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.47  tff(c_902, plain, (![D_266, A_267]: (~r2_hidden(D_266, k2_zfmisc_1(A_267, '#skF_12')))), inference(resolution, [status(thm)], [c_892, c_733])).
% 3.12/1.47  tff(c_942, plain, (![A_267]: (k2_zfmisc_1(A_267, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_783, c_902])).
% 3.12/1.47  tff(c_698, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_58])).
% 3.12/1.47  tff(c_707, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_699, c_699, c_698])).
% 3.12/1.47  tff(c_708, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_707])).
% 3.12/1.47  tff(c_56, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.47  tff(c_710, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_699, c_699, c_56])).
% 3.12/1.47  tff(c_711, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_708, c_710])).
% 3.12/1.47  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_942, c_711])).
% 3.12/1.47  tff(c_950, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_707])).
% 3.12/1.47  tff(c_957, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_699, c_950, c_699, c_56])).
% 3.12/1.47  tff(c_1108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1100, c_957])).
% 3.12/1.47  tff(c_1110, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_60])).
% 3.12/1.47  tff(c_62, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.47  tff(c_1122, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1110, c_1110, c_62])).
% 3.12/1.47  tff(c_1123, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_1122])).
% 3.12/1.47  tff(c_1111, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_10])).
% 3.12/1.47  tff(c_1127, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1111])).
% 3.12/1.47  tff(c_1148, plain, (![A_319, C_320, B_321]: (~r2_hidden(A_319, C_320) | ~r1_xboole_0(k2_tarski(A_319, B_321), C_320))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.47  tff(c_1153, plain, (![A_319]: (~r2_hidden(A_319, '#skF_9'))), inference(resolution, [status(thm)], [c_1127, c_1148])).
% 3.12/1.47  tff(c_1191, plain, (![B_343]: (r2_hidden('#skF_1'('#skF_9', B_343), B_343) | B_343='#skF_9')), inference(resolution, [status(thm)], [c_1177, c_1153])).
% 3.12/1.47  tff(c_1233, plain, (![A_356, B_357, D_358]: (r2_hidden('#skF_7'(A_356, B_357, k2_zfmisc_1(A_356, B_357), D_358), A_356) | ~r2_hidden(D_358, k2_zfmisc_1(A_356, B_357)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.47  tff(c_1239, plain, (![D_359, B_360]: (~r2_hidden(D_359, k2_zfmisc_1('#skF_9', B_360)))), inference(resolution, [status(thm)], [c_1233, c_1153])).
% 3.12/1.47  tff(c_1267, plain, (![B_360]: (k2_zfmisc_1('#skF_9', B_360)='#skF_9')), inference(resolution, [status(thm)], [c_1191, c_1239])).
% 3.12/1.47  tff(c_1109, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.12/1.47  tff(c_1117, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1109])).
% 3.12/1.47  tff(c_1126, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1117])).
% 3.12/1.47  tff(c_1273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1267, c_1126])).
% 3.12/1.47  tff(c_1274, plain, ('#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_1122])).
% 3.12/1.47  tff(c_1278, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_1111])).
% 3.12/1.47  tff(c_1301, plain, (![A_364, C_365, B_366]: (~r2_hidden(A_364, C_365) | ~r1_xboole_0(k2_tarski(A_364, B_366), C_365))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.47  tff(c_1306, plain, (![A_364]: (~r2_hidden(A_364, '#skF_10'))), inference(resolution, [status(thm)], [c_1278, c_1301])).
% 3.12/1.47  tff(c_1345, plain, (![B_388]: (r2_hidden('#skF_1'('#skF_10', B_388), B_388) | B_388='#skF_10')), inference(resolution, [status(thm)], [c_1331, c_1306])).
% 3.12/1.47  tff(c_1387, plain, (![A_401, B_402, D_403]: (r2_hidden('#skF_8'(A_401, B_402, k2_zfmisc_1(A_401, B_402), D_403), B_402) | ~r2_hidden(D_403, k2_zfmisc_1(A_401, B_402)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.47  tff(c_1393, plain, (![D_404, A_405]: (~r2_hidden(D_404, k2_zfmisc_1(A_405, '#skF_10')))), inference(resolution, [status(thm)], [c_1387, c_1306])).
% 3.12/1.47  tff(c_1421, plain, (![A_405]: (k2_zfmisc_1(A_405, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1345, c_1393])).
% 3.12/1.47  tff(c_1277, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_1117])).
% 3.12/1.47  tff(c_1427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1421, c_1277])).
% 3.12/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.47  
% 3.12/1.47  Inference rules
% 3.12/1.47  ----------------------
% 3.12/1.47  #Ref     : 0
% 3.12/1.47  #Sup     : 250
% 3.12/1.47  #Fact    : 0
% 3.12/1.47  #Define  : 0
% 3.12/1.47  #Split   : 11
% 3.12/1.47  #Chain   : 0
% 3.12/1.47  #Close   : 0
% 3.12/1.47  
% 3.12/1.47  Ordering : KBO
% 3.12/1.47  
% 3.12/1.47  Simplification rules
% 3.12/1.47  ----------------------
% 3.12/1.47  #Subsume      : 77
% 3.12/1.47  #Demod        : 117
% 3.12/1.47  #Tautology    : 129
% 3.12/1.47  #SimpNegUnit  : 18
% 3.12/1.47  #BackRed      : 36
% 3.12/1.47  
% 3.12/1.47  #Partial instantiations: 0
% 3.12/1.47  #Strategies tried      : 1
% 3.12/1.47  
% 3.12/1.47  Timing (in seconds)
% 3.12/1.47  ----------------------
% 3.12/1.48  Preprocessing        : 0.33
% 3.12/1.48  Parsing              : 0.17
% 3.12/1.48  CNF conversion       : 0.03
% 3.12/1.48  Main loop            : 0.39
% 3.12/1.48  Inferencing          : 0.17
% 3.12/1.48  Reduction            : 0.10
% 3.12/1.48  Demodulation         : 0.06
% 3.12/1.48  BG Simplification    : 0.03
% 3.12/1.48  Subsumption          : 0.06
% 3.12/1.48  Abstraction          : 0.02
% 3.12/1.48  MUC search           : 0.00
% 3.12/1.48  Cooper               : 0.00
% 3.12/1.48  Total                : 0.76
% 3.12/1.48  Index Insertion      : 0.00
% 3.12/1.48  Index Deletion       : 0.00
% 3.12/1.48  Index Matching       : 0.00
% 3.12/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
