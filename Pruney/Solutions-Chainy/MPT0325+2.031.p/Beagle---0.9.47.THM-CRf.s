%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:25 EST 2020

% Result     : Theorem 12.33s
% Output     : CNFRefutation 12.45s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 879 expanded)
%              Number of leaves         :   31 ( 298 expanded)
%              Depth                    :   15
%              Number of atoms          :  357 (2040 expanded)
%              Number of equality atoms :   94 ( 531 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_11 > #skF_6 > #skF_10 > #skF_9 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_68,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,
    ( ~ r1_tarski('#skF_12','#skF_14')
    | ~ r1_tarski('#skF_11','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_98,plain,(
    ~ r1_tarski('#skF_11','#skF_13') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_18,B_19,D_45] :
      ( r2_hidden('#skF_10'(A_18,B_19,k2_zfmisc_1(A_18,B_19),D_45),B_19)
      | ~ r2_hidden(D_45,k2_zfmisc_1(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    r1_tarski(k2_zfmisc_1('#skF_11','#skF_12'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_615,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( r2_hidden(k4_tarski(A_124,B_125),k2_zfmisc_1(C_126,D_127))
      | ~ r2_hidden(B_125,D_127)
      | ~ r2_hidden(A_124,C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8993,plain,(
    ! [A_483,D_484,B_485,C_486,B_487] :
      ( r2_hidden(k4_tarski(A_483,B_485),B_487)
      | ~ r1_tarski(k2_zfmisc_1(C_486,D_484),B_487)
      | ~ r2_hidden(B_485,D_484)
      | ~ r2_hidden(A_483,C_486) ) ),
    inference(resolution,[status(thm)],[c_615,c_2])).

tff(c_11849,plain,(
    ! [A_520,B_521] :
      ( r2_hidden(k4_tarski(A_520,B_521),k2_zfmisc_1('#skF_13','#skF_14'))
      | ~ r2_hidden(B_521,'#skF_12')
      | ~ r2_hidden(A_520,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_70,c_8993])).

tff(c_64,plain,(
    ! [A_52,C_54,B_53,D_55] :
      ( r2_hidden(A_52,C_54)
      | ~ r2_hidden(k4_tarski(A_52,B_53),k2_zfmisc_1(C_54,D_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_11877,plain,(
    ! [A_520,B_521] :
      ( r2_hidden(A_520,'#skF_13')
      | ~ r2_hidden(B_521,'#skF_12')
      | ~ r2_hidden(A_520,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_11849,c_64])).

tff(c_12509,plain,(
    ! [B_529] : ~ r2_hidden(B_529,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_11877])).

tff(c_12652,plain,(
    ! [D_45,A_18] : ~ r2_hidden(D_45,k2_zfmisc_1(A_18,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_40,c_12509])).

tff(c_3541,plain,(
    ! [A_280,B_281,C_282] :
      ( r2_hidden('#skF_2'(A_280,B_281,C_282),A_280)
      | r2_hidden('#skF_3'(A_280,B_281,C_282),C_282)
      | k4_xboole_0(A_280,B_281) = C_282 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3591,plain,(
    ! [A_280,B_281] :
      ( r2_hidden('#skF_3'(A_280,B_281,A_280),A_280)
      | k4_xboole_0(A_280,B_281) = A_280 ) ),
    inference(resolution,[status(thm)],[c_3541,c_20])).

tff(c_4828,plain,(
    ! [A_349,B_350,C_351] :
      ( r2_hidden('#skF_2'(A_349,B_350,C_351),A_349)
      | r2_hidden('#skF_3'(A_349,B_350,C_351),B_350)
      | ~ r2_hidden('#skF_3'(A_349,B_350,C_351),A_349)
      | k4_xboole_0(A_349,B_350) = C_351 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_7596,plain,(
    ! [A_468,B_469] :
      ( r2_hidden('#skF_3'(A_468,B_469,A_468),B_469)
      | ~ r2_hidden('#skF_3'(A_468,B_469,A_468),A_468)
      | k4_xboole_0(A_468,B_469) = A_468 ) ),
    inference(resolution,[status(thm)],[c_4828,c_14])).

tff(c_7623,plain,(
    ! [A_470,B_471] :
      ( r2_hidden('#skF_3'(A_470,B_471,A_470),B_471)
      | k4_xboole_0(A_470,B_471) = A_470 ) ),
    inference(resolution,[status(thm)],[c_3591,c_7596])).

tff(c_32,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_234,plain,(
    ! [C_82,B_83,A_84] :
      ( r2_hidden(C_82,B_83)
      | ~ r2_hidden(C_82,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_486,plain,(
    ! [A_111,B_112,B_113] :
      ( r2_hidden('#skF_1'(A_111,B_112),B_113)
      | ~ r1_tarski(A_111,B_113)
      | r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_6,c_234])).

tff(c_132,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    ! [D_66,A_16] :
      ( ~ r2_hidden(D_66,k1_xboole_0)
      | ~ r2_hidden(D_66,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_132])).

tff(c_632,plain,(
    ! [A_128,B_129,A_130] :
      ( ~ r2_hidden('#skF_1'(A_128,B_129),A_130)
      | ~ r1_tarski(A_128,k1_xboole_0)
      | r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_486,c_142])).

tff(c_646,plain,(
    ! [A_131,B_132] :
      ( ~ r1_tarski(A_131,k1_xboole_0)
      | r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_6,c_632])).

tff(c_655,plain,(
    ! [A_14,B_132] :
      ( r1_tarski(A_14,B_132)
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_646])).

tff(c_661,plain,(
    ! [A_14,B_132] :
      ( r1_tarski(A_14,B_132)
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_655])).

tff(c_3640,plain,(
    ! [A_285,B_286] :
      ( r2_hidden('#skF_3'(A_285,B_286,A_285),A_285)
      | k4_xboole_0(A_285,B_286) = A_285 ) ),
    inference(resolution,[status(thm)],[c_3541,c_20])).

tff(c_3841,plain,(
    ! [A_299,B_300,B_301] :
      ( r2_hidden('#skF_3'(A_299,B_300,A_299),B_301)
      | ~ r1_tarski(A_299,B_301)
      | k4_xboole_0(A_299,B_300) = A_299 ) ),
    inference(resolution,[status(thm)],[c_3640,c_2])).

tff(c_3966,plain,(
    ! [A_309,B_310,A_311] :
      ( ~ r2_hidden('#skF_3'(A_309,B_310,A_309),A_311)
      | ~ r1_tarski(A_309,k1_xboole_0)
      | k4_xboole_0(A_309,B_310) = A_309 ) ),
    inference(resolution,[status(thm)],[c_3841,c_142])).

tff(c_4043,plain,(
    ! [A_314,B_315] :
      ( ~ r1_tarski(A_314,k1_xboole_0)
      | k4_xboole_0(A_314,B_315) = A_314 ) ),
    inference(resolution,[status(thm)],[c_3591,c_3966])).

tff(c_4076,plain,(
    ! [A_316,B_317] :
      ( k4_xboole_0(A_316,B_317) = A_316
      | k1_xboole_0 != A_316 ) ),
    inference(resolution,[status(thm)],[c_661,c_4043])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4442,plain,(
    ! [D_327,B_328,A_329] :
      ( ~ r2_hidden(D_327,B_328)
      | ~ r2_hidden(D_327,A_329)
      | k1_xboole_0 != A_329 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4076,c_10])).

tff(c_4504,plain,(
    ! [A_280,B_281,A_329] :
      ( ~ r2_hidden('#skF_3'(A_280,B_281,A_280),A_329)
      | k1_xboole_0 != A_329
      | k4_xboole_0(A_280,B_281) = A_280 ) ),
    inference(resolution,[status(thm)],[c_3591,c_4442])).

tff(c_7689,plain,(
    ! [B_472,A_473] :
      ( k1_xboole_0 != B_472
      | k4_xboole_0(A_473,B_472) = A_473 ) ),
    inference(resolution,[status(thm)],[c_7623,c_4504])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,(
    ! [D_63,A_64,B_65] :
      ( r2_hidden(D_63,A_64)
      | ~ r2_hidden(D_63,k4_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_131,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_64,B_65)),A_64)
      | k4_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_117])).

tff(c_8222,plain,(
    ! [A_479,B_480] :
      ( r2_hidden('#skF_4'(A_479),A_479)
      | k4_xboole_0(A_479,B_480) = k1_xboole_0
      | k1_xboole_0 != B_480 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7689,c_131])).

tff(c_3018,plain,(
    ! [A_244,B_245,B_246,A_247] :
      ( ~ r2_hidden('#skF_1'(A_244,B_245),B_246)
      | ~ r1_tarski(A_244,k4_xboole_0(A_247,B_246))
      | r1_tarski(A_244,B_245) ) ),
    inference(resolution,[status(thm)],[c_486,c_10])).

tff(c_3085,plain,(
    ! [A_251,A_252,B_253] :
      ( ~ r1_tarski(A_251,k4_xboole_0(A_252,A_251))
      | r1_tarski(A_251,B_253) ) ),
    inference(resolution,[status(thm)],[c_6,c_3018])).

tff(c_3121,plain,(
    ! [A_14,B_253,A_252] :
      ( r1_tarski(A_14,B_253)
      | k4_xboole_0(A_14,k4_xboole_0(A_252,A_14)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_3085])).

tff(c_4109,plain,(
    ! [B_317,B_253,A_316] :
      ( r1_tarski(B_317,B_253)
      | k4_xboole_0(B_317,A_316) != k1_xboole_0
      | k1_xboole_0 != A_316 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4076,c_3121])).

tff(c_8680,plain,(
    ! [A_479,B_253,B_480] :
      ( r1_tarski(A_479,B_253)
      | r2_hidden('#skF_4'(A_479),A_479)
      | k1_xboole_0 != B_480 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8222,c_4109])).

tff(c_8739,plain,(
    ! [B_480] : k1_xboole_0 != B_480 ),
    inference(splitLeft,[status(thm)],[c_8680])).

tff(c_154,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1858,plain,(
    ! [A_198,B_199,B_200] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_198,B_199),B_200),A_198)
      | r1_tarski(k4_xboole_0(A_198,B_199),B_200) ) ),
    inference(resolution,[status(thm)],[c_154,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1928,plain,(
    ! [A_201,B_202] : r1_tarski(k4_xboole_0(A_201,B_202),A_201) ),
    inference(resolution,[status(thm)],[c_1858,c_4])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1981,plain,(
    ! [A_201,B_202] : k4_xboole_0(k4_xboole_0(A_201,B_202),A_201) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1928,c_30])).

tff(c_8792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8739,c_1981])).

tff(c_8794,plain,(
    ! [A_481,B_482] :
      ( r1_tarski(A_481,B_482)
      | r2_hidden('#skF_4'(A_481),A_481) ) ),
    inference(splitRight,[status(thm)],[c_8680])).

tff(c_99,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_11','#skF_12'),k2_zfmisc_1('#skF_13','#skF_14')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_99])).

tff(c_327,plain,(
    ! [D_101,A_102,B_103] :
      ( r2_hidden(D_101,k4_xboole_0(A_102,B_103))
      | r2_hidden(D_101,B_103)
      | ~ r2_hidden(D_101,A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_463,plain,(
    ! [D_110] :
      ( r2_hidden(D_110,k1_xboole_0)
      | r2_hidden(D_110,k2_zfmisc_1('#skF_13','#skF_14'))
      | ~ r2_hidden(D_110,k2_zfmisc_1('#skF_11','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_327])).

tff(c_479,plain,
    ( r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k1_xboole_0)
    | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_13','#skF_14'))
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_463])).

tff(c_485,plain,
    ( r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k1_xboole_0)
    | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_479])).

tff(c_697,plain,(
    r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_241,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_4'(A_85),B_86)
      | ~ r1_tarski(A_85,B_86)
      | k1_xboole_0 = A_85 ) ),
    inference(resolution,[status(thm)],[c_26,c_234])).

tff(c_261,plain,(
    ! [A_85,B_7,A_6] :
      ( ~ r2_hidden('#skF_4'(A_85),B_7)
      | ~ r1_tarski(A_85,k4_xboole_0(A_6,B_7))
      | k1_xboole_0 = A_85 ) ),
    inference(resolution,[status(thm)],[c_241,c_10])).

tff(c_781,plain,(
    ! [A_6] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_11','#skF_12'),k4_xboole_0(A_6,k2_zfmisc_1('#skF_13','#skF_14')))
      | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_697,c_261])).

tff(c_786,plain,(
    ! [A_6] : ~ r1_tarski(k2_zfmisc_1('#skF_11','#skF_12'),k4_xboole_0(A_6,k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_781])).

tff(c_8966,plain,(
    r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(resolution,[status(thm)],[c_8794,c_786])).

tff(c_13379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12652,c_8966])).

tff(c_13545,plain,(
    ! [A_555] :
      ( r2_hidden(A_555,'#skF_13')
      | ~ r2_hidden(A_555,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_11877])).

tff(c_17480,plain,(
    ! [B_632] :
      ( r2_hidden('#skF_1'('#skF_11',B_632),'#skF_13')
      | r1_tarski('#skF_11',B_632) ) ),
    inference(resolution,[status(thm)],[c_6,c_13545])).

tff(c_17502,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_17480,c_4])).

tff(c_17514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_98,c_17502])).

tff(c_17515,plain,(
    r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_293,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_98,B_99)),B_99)
      | k4_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_132])).

tff(c_306,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_4'(A_16),k1_xboole_0)
      | k4_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_293])).

tff(c_313,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_4'(A_16),k1_xboole_0)
      | k1_xboole_0 = A_16 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_306])).

tff(c_17521,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17515,c_313])).

tff(c_17534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_17521])).

tff(c_17535,plain,(
    ~ r1_tarski('#skF_12','#skF_14') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_17536,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_17537,plain,(
    ! [A_633,B_634] :
      ( k4_xboole_0(A_633,B_634) = k1_xboole_0
      | ~ r1_tarski(A_633,B_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_17545,plain,(
    k4_xboole_0('#skF_11','#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17536,c_17537])).

tff(c_17802,plain,(
    ! [D_675,A_676,B_677] :
      ( r2_hidden(D_675,k4_xboole_0(A_676,B_677))
      | r2_hidden(D_675,B_677)
      | ~ r2_hidden(D_675,A_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17834,plain,(
    ! [D_678] :
      ( r2_hidden(D_678,k1_xboole_0)
      | r2_hidden(D_678,'#skF_13')
      | ~ r2_hidden(D_678,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17545,c_17802])).

tff(c_17648,plain,(
    ! [D_649,B_650,A_651] :
      ( ~ r2_hidden(D_649,B_650)
      | ~ r2_hidden(D_649,k4_xboole_0(A_651,B_650)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17668,plain,(
    ! [D_649,A_16] :
      ( ~ r2_hidden(D_649,k1_xboole_0)
      | ~ r2_hidden(D_649,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_17648])).

tff(c_17868,plain,(
    ! [D_681,A_682] :
      ( ~ r2_hidden(D_681,A_682)
      | r2_hidden(D_681,'#skF_13')
      | ~ r2_hidden(D_681,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_17834,c_17668])).

tff(c_18042,plain,(
    ! [A_695] :
      ( r2_hidden('#skF_4'(A_695),'#skF_13')
      | ~ r2_hidden('#skF_4'(A_695),'#skF_11')
      | k1_xboole_0 = A_695 ) ),
    inference(resolution,[status(thm)],[c_26,c_17868])).

tff(c_18057,plain,
    ( r2_hidden('#skF_4'('#skF_11'),'#skF_13')
    | k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_26,c_18042])).

tff(c_18058,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_18057])).

tff(c_18080,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_68])).

tff(c_18078,plain,(
    ! [A_16] : k4_xboole_0(A_16,'#skF_11') = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_32])).

tff(c_18073,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_28])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18800,plain,(
    ! [A_752,B_753,C_754] :
      ( ~ r2_hidden('#skF_2'(A_752,B_753,C_754),C_754)
      | r2_hidden('#skF_3'(A_752,B_753,C_754),C_754)
      | k4_xboole_0(A_752,B_753) = C_754 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18809,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k4_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_18800])).

tff(c_18811,plain,(
    ! [A_755,B_756] :
      ( r2_hidden('#skF_3'(A_755,B_756,A_755),A_755)
      | k4_xboole_0(A_755,B_756) = A_755 ) ),
    inference(resolution,[status(thm)],[c_24,c_18800])).

tff(c_22099,plain,(
    ! [A_932,B_933,B_934] :
      ( r2_hidden('#skF_3'(A_932,B_933,A_932),B_934)
      | ~ r1_tarski(A_932,B_934)
      | k4_xboole_0(A_932,B_933) = A_932 ) ),
    inference(resolution,[status(thm)],[c_18811,c_2])).

tff(c_18069,plain,(
    ! [D_649,A_16] :
      ( ~ r2_hidden(D_649,'#skF_11')
      | ~ r2_hidden(D_649,A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_17668])).

tff(c_22203,plain,(
    ! [A_937,B_938,A_939] :
      ( ~ r2_hidden('#skF_3'(A_937,B_938,A_937),A_939)
      | ~ r1_tarski(A_937,'#skF_11')
      | k4_xboole_0(A_937,B_938) = A_937 ) ),
    inference(resolution,[status(thm)],[c_22099,c_18069])).

tff(c_22254,plain,(
    ! [A_945,B_946] :
      ( ~ r1_tarski(A_945,'#skF_11')
      | k4_xboole_0(A_945,B_946) = A_945 ) ),
    inference(resolution,[status(thm)],[c_18809,c_22203])).

tff(c_22272,plain,(
    ! [A_14,B_946] :
      ( k4_xboole_0(A_14,B_946) = A_14
      | k4_xboole_0(A_14,'#skF_11') != '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_18073,c_22254])).

tff(c_22286,plain,(
    ! [B_946] : k4_xboole_0('#skF_11',B_946) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18078,c_22272])).

tff(c_17564,plain,(
    ! [A_639,B_640] :
      ( ~ r2_hidden('#skF_1'(A_639,B_640),B_640)
      | r1_tarski(A_639,B_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17570,plain,(
    ! [A_641] : r1_tarski(A_641,A_641) ),
    inference(resolution,[status(thm)],[c_6,c_17564])).

tff(c_17574,plain,(
    ! [A_641] : k4_xboole_0(A_641,A_641) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17570,c_30])).

tff(c_18071,plain,(
    ! [A_641] : k4_xboole_0(A_641,A_641) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_17574])).

tff(c_19238,plain,(
    ! [A_779,B_780,C_781] :
      ( ~ r2_hidden('#skF_2'(A_779,B_780,C_781),B_780)
      | r2_hidden('#skF_3'(A_779,B_780,C_781),C_781)
      | k4_xboole_0(A_779,B_780) = C_781 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_19241,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_19238])).

tff(c_19246,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | C_8 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18071,c_19241])).

tff(c_42,plain,(
    ! [A_18,B_19,D_45] :
      ( r2_hidden('#skF_9'(A_18,B_19,k2_zfmisc_1(A_18,B_19),D_45),A_18)
      | ~ r2_hidden(D_45,k2_zfmisc_1(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_17921,plain,(
    ! [A_685,B_686,C_687,D_688] :
      ( r2_hidden(k4_tarski(A_685,B_686),k2_zfmisc_1(C_687,D_688))
      | ~ r2_hidden(B_686,D_688)
      | ~ r2_hidden(A_685,C_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24818,plain,(
    ! [C_1032,D_1035,B_1034,A_1033,B_1036] :
      ( r2_hidden(k4_tarski(A_1033,B_1036),B_1034)
      | ~ r1_tarski(k2_zfmisc_1(C_1032,D_1035),B_1034)
      | ~ r2_hidden(B_1036,D_1035)
      | ~ r2_hidden(A_1033,C_1032) ) ),
    inference(resolution,[status(thm)],[c_17921,c_2])).

tff(c_24892,plain,(
    ! [A_1039,B_1040] :
      ( r2_hidden(k4_tarski(A_1039,B_1040),k2_zfmisc_1('#skF_13','#skF_14'))
      | ~ r2_hidden(B_1040,'#skF_12')
      | ~ r2_hidden(A_1039,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_70,c_24818])).

tff(c_62,plain,(
    ! [B_53,D_55,A_52,C_54] :
      ( r2_hidden(B_53,D_55)
      | ~ r2_hidden(k4_tarski(A_52,B_53),k2_zfmisc_1(C_54,D_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24916,plain,(
    ! [B_1040,A_1039] :
      ( r2_hidden(B_1040,'#skF_14')
      | ~ r2_hidden(B_1040,'#skF_12')
      | ~ r2_hidden(A_1039,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_24892,c_62])).

tff(c_24923,plain,(
    ! [A_1041] : ~ r2_hidden(A_1041,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_24916])).

tff(c_25053,plain,(
    ! [D_1042,B_1043] : ~ r2_hidden(D_1042,k2_zfmisc_1('#skF_11',B_1043)) ),
    inference(resolution,[status(thm)],[c_42,c_24923])).

tff(c_25172,plain,(
    ! [B_1043] : k2_zfmisc_1('#skF_11',B_1043) = '#skF_11' ),
    inference(resolution,[status(thm)],[c_19246,c_25053])).

tff(c_17544,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_11','#skF_12'),k2_zfmisc_1('#skF_13','#skF_14')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_17537])).

tff(c_18014,plain,(
    ! [D_694] :
      ( r2_hidden(D_694,k1_xboole_0)
      | r2_hidden(D_694,k2_zfmisc_1('#skF_13','#skF_14'))
      | ~ r2_hidden(D_694,k2_zfmisc_1('#skF_11','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17544,c_17802])).

tff(c_18034,plain,
    ( r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k1_xboole_0)
    | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_13','#skF_14'))
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_18014])).

tff(c_18041,plain,
    ( r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k1_xboole_0)
    | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_18034])).

tff(c_18294,plain,
    ( r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),'#skF_11')
    | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_18041])).

tff(c_18295,plain,(
    r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_18294])).

tff(c_17684,plain,(
    ! [C_654,B_655,A_656] :
      ( r2_hidden(C_654,B_655)
      | ~ r2_hidden(C_654,A_656)
      | ~ r1_tarski(A_656,B_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17706,plain,(
    ! [A_660,B_661] :
      ( r2_hidden('#skF_4'(A_660),B_661)
      | ~ r1_tarski(A_660,B_661)
      | k1_xboole_0 = A_660 ) ),
    inference(resolution,[status(thm)],[c_26,c_17684])).

tff(c_17725,plain,(
    ! [A_660,B_7,A_6] :
      ( ~ r2_hidden('#skF_4'(A_660),B_7)
      | ~ r1_tarski(A_660,k4_xboole_0(A_6,B_7))
      | k1_xboole_0 = A_660 ) ),
    inference(resolution,[status(thm)],[c_17706,c_10])).

tff(c_18708,plain,(
    ! [A_744,B_745,A_746] :
      ( ~ r2_hidden('#skF_4'(A_744),B_745)
      | ~ r1_tarski(A_744,k4_xboole_0(A_746,B_745))
      | A_744 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_17725])).

tff(c_18716,plain,(
    ! [A_746] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_11','#skF_12'),k4_xboole_0(A_746,k2_zfmisc_1('#skF_13','#skF_14')))
      | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_18295,c_18708])).

tff(c_18782,plain,(
    ! [A_751] : ~ r1_tarski(k2_zfmisc_1('#skF_11','#skF_12'),k4_xboole_0(A_751,k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(negUnitSimplification,[status(thm)],[c_18080,c_18716])).

tff(c_18794,plain,(
    ! [A_751] : k4_xboole_0(k2_zfmisc_1('#skF_11','#skF_12'),k4_xboole_0(A_751,k2_zfmisc_1('#skF_13','#skF_14'))) != '#skF_11' ),
    inference(resolution,[status(thm)],[c_18073,c_18782])).

tff(c_25204,plain,(
    ! [A_751] : k4_xboole_0('#skF_11',k4_xboole_0(A_751,k2_zfmisc_1('#skF_13','#skF_14'))) != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25172,c_18794])).

tff(c_25226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22286,c_25204])).

tff(c_25228,plain,(
    ! [B_1044] :
      ( r2_hidden(B_1044,'#skF_14')
      | ~ r2_hidden(B_1044,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_24916])).

tff(c_25355,plain,(
    ! [A_1049] :
      ( r1_tarski(A_1049,'#skF_14')
      | ~ r2_hidden('#skF_1'(A_1049,'#skF_14'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_25228,c_4])).

tff(c_25367,plain,(
    r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_6,c_25355])).

tff(c_25373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17535,c_17535,c_25367])).

tff(c_25374,plain,(
    r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11','#skF_12')),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_18294])).

tff(c_17884,plain,(
    ! [A_683,B_684] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_683,B_684)),B_684)
      | k4_xboole_0(A_683,B_684) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_17648])).

tff(c_17908,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_4'(A_16),k1_xboole_0)
      | k4_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_17884])).

tff(c_17919,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_4'(A_16),k1_xboole_0)
      | k1_xboole_0 = A_16 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_17908])).

tff(c_18063,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_4'(A_16),'#skF_11')
      | A_16 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18058,c_18058,c_17919])).

tff(c_25378,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_25374,c_18063])).

tff(c_25388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18080,c_25378])).

tff(c_25390,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_18057])).

tff(c_26182,plain,(
    ! [A_1108,B_1109,C_1110] :
      ( r2_hidden('#skF_2'(A_1108,B_1109,C_1110),A_1108)
      | r2_hidden('#skF_3'(A_1108,B_1109,C_1110),C_1110)
      | k4_xboole_0(A_1108,B_1109) = C_1110 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26189,plain,(
    ! [A_1108,C_1110] :
      ( r2_hidden('#skF_3'(A_1108,A_1108,C_1110),C_1110)
      | k4_xboole_0(A_1108,A_1108) = C_1110 ) ),
    inference(resolution,[status(thm)],[c_26182,c_22])).

tff(c_26236,plain,(
    ! [A_1108,C_1110] :
      ( r2_hidden('#skF_3'(A_1108,A_1108,C_1110),C_1110)
      | k1_xboole_0 = C_1110 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17574,c_26189])).

tff(c_32620,plain,(
    ! [C_1376,B_1380,A_1377,D_1379,B_1378] :
      ( r2_hidden(k4_tarski(A_1377,B_1380),B_1378)
      | ~ r1_tarski(k2_zfmisc_1(C_1376,D_1379),B_1378)
      | ~ r2_hidden(B_1380,D_1379)
      | ~ r2_hidden(A_1377,C_1376) ) ),
    inference(resolution,[status(thm)],[c_17921,c_2])).

tff(c_32682,plain,(
    ! [A_1383,B_1384] :
      ( r2_hidden(k4_tarski(A_1383,B_1384),k2_zfmisc_1('#skF_13','#skF_14'))
      | ~ r2_hidden(B_1384,'#skF_12')
      | ~ r2_hidden(A_1383,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_70,c_32620])).

tff(c_32703,plain,(
    ! [B_1384,A_1383] :
      ( r2_hidden(B_1384,'#skF_14')
      | ~ r2_hidden(B_1384,'#skF_12')
      | ~ r2_hidden(A_1383,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_32682,c_62])).

tff(c_32707,plain,(
    ! [A_1385] : ~ r2_hidden(A_1385,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_32703])).

tff(c_32769,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_26236,c_32707])).

tff(c_32832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25390,c_32769])).

tff(c_32834,plain,(
    ! [B_1386] :
      ( r2_hidden(B_1386,'#skF_14')
      | ~ r2_hidden(B_1386,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_32703])).

tff(c_32918,plain,(
    ! [A_1387] :
      ( r1_tarski(A_1387,'#skF_14')
      | ~ r2_hidden('#skF_1'(A_1387,'#skF_14'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_32834,c_4])).

tff(c_32930,plain,(
    r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_6,c_32918])).

tff(c_32936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17535,c_17535,c_32930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:58:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.33/4.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.33/4.37  
% 12.33/4.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.33/4.37  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_11 > #skF_6 > #skF_10 > #skF_9 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_12
% 12.33/4.37  
% 12.33/4.37  %Foreground sorts:
% 12.33/4.37  
% 12.33/4.37  
% 12.33/4.37  %Background operators:
% 12.33/4.37  
% 12.33/4.37  
% 12.33/4.37  %Foreground operators:
% 12.33/4.37  tff('#skF_4', type, '#skF_4': $i > $i).
% 12.33/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.33/4.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.33/4.37  tff('#skF_11', type, '#skF_11': $i).
% 12.33/4.37  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 12.33/4.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.33/4.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.33/4.37  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 12.33/4.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.33/4.37  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 12.33/4.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.33/4.37  tff('#skF_14', type, '#skF_14': $i).
% 12.33/4.37  tff('#skF_13', type, '#skF_13': $i).
% 12.33/4.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 12.33/4.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.33/4.37  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 12.33/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.33/4.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.33/4.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.33/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.33/4.37  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 12.33/4.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.33/4.37  tff('#skF_12', type, '#skF_12': $i).
% 12.33/4.37  
% 12.45/4.40  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 12.45/4.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.45/4.40  tff(f_70, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 12.45/4.40  tff(f_76, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 12.45/4.40  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.45/4.40  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 12.45/4.40  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.45/4.40  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 12.45/4.40  tff(c_68, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.45/4.40  tff(c_66, plain, (~r1_tarski('#skF_12', '#skF_14') | ~r1_tarski('#skF_11', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.45/4.40  tff(c_98, plain, (~r1_tarski('#skF_11', '#skF_13')), inference(splitLeft, [status(thm)], [c_66])).
% 12.45/4.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.45/4.40  tff(c_40, plain, (![A_18, B_19, D_45]: (r2_hidden('#skF_10'(A_18, B_19, k2_zfmisc_1(A_18, B_19), D_45), B_19) | ~r2_hidden(D_45, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.45/4.40  tff(c_70, plain, (r1_tarski(k2_zfmisc_1('#skF_11', '#skF_12'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.45/4.40  tff(c_615, plain, (![A_124, B_125, C_126, D_127]: (r2_hidden(k4_tarski(A_124, B_125), k2_zfmisc_1(C_126, D_127)) | ~r2_hidden(B_125, D_127) | ~r2_hidden(A_124, C_126))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.45/4.40  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.45/4.40  tff(c_8993, plain, (![A_483, D_484, B_485, C_486, B_487]: (r2_hidden(k4_tarski(A_483, B_485), B_487) | ~r1_tarski(k2_zfmisc_1(C_486, D_484), B_487) | ~r2_hidden(B_485, D_484) | ~r2_hidden(A_483, C_486))), inference(resolution, [status(thm)], [c_615, c_2])).
% 12.45/4.40  tff(c_11849, plain, (![A_520, B_521]: (r2_hidden(k4_tarski(A_520, B_521), k2_zfmisc_1('#skF_13', '#skF_14')) | ~r2_hidden(B_521, '#skF_12') | ~r2_hidden(A_520, '#skF_11'))), inference(resolution, [status(thm)], [c_70, c_8993])).
% 12.45/4.40  tff(c_64, plain, (![A_52, C_54, B_53, D_55]: (r2_hidden(A_52, C_54) | ~r2_hidden(k4_tarski(A_52, B_53), k2_zfmisc_1(C_54, D_55)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.45/4.40  tff(c_11877, plain, (![A_520, B_521]: (r2_hidden(A_520, '#skF_13') | ~r2_hidden(B_521, '#skF_12') | ~r2_hidden(A_520, '#skF_11'))), inference(resolution, [status(thm)], [c_11849, c_64])).
% 12.45/4.40  tff(c_12509, plain, (![B_529]: (~r2_hidden(B_529, '#skF_12'))), inference(splitLeft, [status(thm)], [c_11877])).
% 12.45/4.40  tff(c_12652, plain, (![D_45, A_18]: (~r2_hidden(D_45, k2_zfmisc_1(A_18, '#skF_12')))), inference(resolution, [status(thm)], [c_40, c_12509])).
% 12.45/4.40  tff(c_3541, plain, (![A_280, B_281, C_282]: (r2_hidden('#skF_2'(A_280, B_281, C_282), A_280) | r2_hidden('#skF_3'(A_280, B_281, C_282), C_282) | k4_xboole_0(A_280, B_281)=C_282)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_3591, plain, (![A_280, B_281]: (r2_hidden('#skF_3'(A_280, B_281, A_280), A_280) | k4_xboole_0(A_280, B_281)=A_280)), inference(resolution, [status(thm)], [c_3541, c_20])).
% 12.45/4.40  tff(c_4828, plain, (![A_349, B_350, C_351]: (r2_hidden('#skF_2'(A_349, B_350, C_351), A_349) | r2_hidden('#skF_3'(A_349, B_350, C_351), B_350) | ~r2_hidden('#skF_3'(A_349, B_350, C_351), A_349) | k4_xboole_0(A_349, B_350)=C_351)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_14, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_7596, plain, (![A_468, B_469]: (r2_hidden('#skF_3'(A_468, B_469, A_468), B_469) | ~r2_hidden('#skF_3'(A_468, B_469, A_468), A_468) | k4_xboole_0(A_468, B_469)=A_468)), inference(resolution, [status(thm)], [c_4828, c_14])).
% 12.45/4.40  tff(c_7623, plain, (![A_470, B_471]: (r2_hidden('#skF_3'(A_470, B_471, A_470), B_471) | k4_xboole_0(A_470, B_471)=A_470)), inference(resolution, [status(thm)], [c_3591, c_7596])).
% 12.45/4.40  tff(c_32, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.45/4.40  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.45/4.40  tff(c_234, plain, (![C_82, B_83, A_84]: (r2_hidden(C_82, B_83) | ~r2_hidden(C_82, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.45/4.40  tff(c_486, plain, (![A_111, B_112, B_113]: (r2_hidden('#skF_1'(A_111, B_112), B_113) | ~r1_tarski(A_111, B_113) | r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_6, c_234])).
% 12.45/4.40  tff(c_132, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_142, plain, (![D_66, A_16]: (~r2_hidden(D_66, k1_xboole_0) | ~r2_hidden(D_66, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_132])).
% 12.45/4.40  tff(c_632, plain, (![A_128, B_129, A_130]: (~r2_hidden('#skF_1'(A_128, B_129), A_130) | ~r1_tarski(A_128, k1_xboole_0) | r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_486, c_142])).
% 12.45/4.40  tff(c_646, plain, (![A_131, B_132]: (~r1_tarski(A_131, k1_xboole_0) | r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_6, c_632])).
% 12.45/4.40  tff(c_655, plain, (![A_14, B_132]: (r1_tarski(A_14, B_132) | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_646])).
% 12.45/4.40  tff(c_661, plain, (![A_14, B_132]: (r1_tarski(A_14, B_132) | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_655])).
% 12.45/4.40  tff(c_3640, plain, (![A_285, B_286]: (r2_hidden('#skF_3'(A_285, B_286, A_285), A_285) | k4_xboole_0(A_285, B_286)=A_285)), inference(resolution, [status(thm)], [c_3541, c_20])).
% 12.45/4.40  tff(c_3841, plain, (![A_299, B_300, B_301]: (r2_hidden('#skF_3'(A_299, B_300, A_299), B_301) | ~r1_tarski(A_299, B_301) | k4_xboole_0(A_299, B_300)=A_299)), inference(resolution, [status(thm)], [c_3640, c_2])).
% 12.45/4.40  tff(c_3966, plain, (![A_309, B_310, A_311]: (~r2_hidden('#skF_3'(A_309, B_310, A_309), A_311) | ~r1_tarski(A_309, k1_xboole_0) | k4_xboole_0(A_309, B_310)=A_309)), inference(resolution, [status(thm)], [c_3841, c_142])).
% 12.45/4.40  tff(c_4043, plain, (![A_314, B_315]: (~r1_tarski(A_314, k1_xboole_0) | k4_xboole_0(A_314, B_315)=A_314)), inference(resolution, [status(thm)], [c_3591, c_3966])).
% 12.45/4.40  tff(c_4076, plain, (![A_316, B_317]: (k4_xboole_0(A_316, B_317)=A_316 | k1_xboole_0!=A_316)), inference(resolution, [status(thm)], [c_661, c_4043])).
% 12.45/4.40  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_4442, plain, (![D_327, B_328, A_329]: (~r2_hidden(D_327, B_328) | ~r2_hidden(D_327, A_329) | k1_xboole_0!=A_329)), inference(superposition, [status(thm), theory('equality')], [c_4076, c_10])).
% 12.45/4.40  tff(c_4504, plain, (![A_280, B_281, A_329]: (~r2_hidden('#skF_3'(A_280, B_281, A_280), A_329) | k1_xboole_0!=A_329 | k4_xboole_0(A_280, B_281)=A_280)), inference(resolution, [status(thm)], [c_3591, c_4442])).
% 12.45/4.40  tff(c_7689, plain, (![B_472, A_473]: (k1_xboole_0!=B_472 | k4_xboole_0(A_473, B_472)=A_473)), inference(resolution, [status(thm)], [c_7623, c_4504])).
% 12.45/4.40  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.45/4.40  tff(c_117, plain, (![D_63, A_64, B_65]: (r2_hidden(D_63, A_64) | ~r2_hidden(D_63, k4_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_131, plain, (![A_64, B_65]: (r2_hidden('#skF_4'(k4_xboole_0(A_64, B_65)), A_64) | k4_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_117])).
% 12.45/4.40  tff(c_8222, plain, (![A_479, B_480]: (r2_hidden('#skF_4'(A_479), A_479) | k4_xboole_0(A_479, B_480)=k1_xboole_0 | k1_xboole_0!=B_480)), inference(superposition, [status(thm), theory('equality')], [c_7689, c_131])).
% 12.45/4.40  tff(c_3018, plain, (![A_244, B_245, B_246, A_247]: (~r2_hidden('#skF_1'(A_244, B_245), B_246) | ~r1_tarski(A_244, k4_xboole_0(A_247, B_246)) | r1_tarski(A_244, B_245))), inference(resolution, [status(thm)], [c_486, c_10])).
% 12.45/4.40  tff(c_3085, plain, (![A_251, A_252, B_253]: (~r1_tarski(A_251, k4_xboole_0(A_252, A_251)) | r1_tarski(A_251, B_253))), inference(resolution, [status(thm)], [c_6, c_3018])).
% 12.45/4.40  tff(c_3121, plain, (![A_14, B_253, A_252]: (r1_tarski(A_14, B_253) | k4_xboole_0(A_14, k4_xboole_0(A_252, A_14))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_3085])).
% 12.45/4.40  tff(c_4109, plain, (![B_317, B_253, A_316]: (r1_tarski(B_317, B_253) | k4_xboole_0(B_317, A_316)!=k1_xboole_0 | k1_xboole_0!=A_316)), inference(superposition, [status(thm), theory('equality')], [c_4076, c_3121])).
% 12.45/4.40  tff(c_8680, plain, (![A_479, B_253, B_480]: (r1_tarski(A_479, B_253) | r2_hidden('#skF_4'(A_479), A_479) | k1_xboole_0!=B_480)), inference(superposition, [status(thm), theory('equality')], [c_8222, c_4109])).
% 12.45/4.40  tff(c_8739, plain, (![B_480]: (k1_xboole_0!=B_480)), inference(splitLeft, [status(thm)], [c_8680])).
% 12.45/4.40  tff(c_154, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.45/4.40  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_1858, plain, (![A_198, B_199, B_200]: (r2_hidden('#skF_1'(k4_xboole_0(A_198, B_199), B_200), A_198) | r1_tarski(k4_xboole_0(A_198, B_199), B_200))), inference(resolution, [status(thm)], [c_154, c_12])).
% 12.45/4.40  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.45/4.40  tff(c_1928, plain, (![A_201, B_202]: (r1_tarski(k4_xboole_0(A_201, B_202), A_201))), inference(resolution, [status(thm)], [c_1858, c_4])).
% 12.45/4.40  tff(c_30, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.45/4.40  tff(c_1981, plain, (![A_201, B_202]: (k4_xboole_0(k4_xboole_0(A_201, B_202), A_201)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1928, c_30])).
% 12.45/4.40  tff(c_8792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8739, c_1981])).
% 12.45/4.40  tff(c_8794, plain, (![A_481, B_482]: (r1_tarski(A_481, B_482) | r2_hidden('#skF_4'(A_481), A_481))), inference(splitRight, [status(thm)], [c_8680])).
% 12.45/4.40  tff(c_99, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.45/4.40  tff(c_103, plain, (k4_xboole_0(k2_zfmisc_1('#skF_11', '#skF_12'), k2_zfmisc_1('#skF_13', '#skF_14'))=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_99])).
% 12.45/4.40  tff(c_327, plain, (![D_101, A_102, B_103]: (r2_hidden(D_101, k4_xboole_0(A_102, B_103)) | r2_hidden(D_101, B_103) | ~r2_hidden(D_101, A_102))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_463, plain, (![D_110]: (r2_hidden(D_110, k1_xboole_0) | r2_hidden(D_110, k2_zfmisc_1('#skF_13', '#skF_14')) | ~r2_hidden(D_110, k2_zfmisc_1('#skF_11', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_103, c_327])).
% 12.45/4.40  tff(c_479, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k1_xboole_0) | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_13', '#skF_14')) | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_463])).
% 12.45/4.40  tff(c_485, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k1_xboole_0) | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_68, c_479])).
% 12.45/4.40  tff(c_697, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(splitLeft, [status(thm)], [c_485])).
% 12.45/4.40  tff(c_241, plain, (![A_85, B_86]: (r2_hidden('#skF_4'(A_85), B_86) | ~r1_tarski(A_85, B_86) | k1_xboole_0=A_85)), inference(resolution, [status(thm)], [c_26, c_234])).
% 12.45/4.40  tff(c_261, plain, (![A_85, B_7, A_6]: (~r2_hidden('#skF_4'(A_85), B_7) | ~r1_tarski(A_85, k4_xboole_0(A_6, B_7)) | k1_xboole_0=A_85)), inference(resolution, [status(thm)], [c_241, c_10])).
% 12.45/4.40  tff(c_781, plain, (![A_6]: (~r1_tarski(k2_zfmisc_1('#skF_11', '#skF_12'), k4_xboole_0(A_6, k2_zfmisc_1('#skF_13', '#skF_14'))) | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0)), inference(resolution, [status(thm)], [c_697, c_261])).
% 12.45/4.40  tff(c_786, plain, (![A_6]: (~r1_tarski(k2_zfmisc_1('#skF_11', '#skF_12'), k4_xboole_0(A_6, k2_zfmisc_1('#skF_13', '#skF_14'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_781])).
% 12.45/4.40  tff(c_8966, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(resolution, [status(thm)], [c_8794, c_786])).
% 12.45/4.40  tff(c_13379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12652, c_8966])).
% 12.45/4.40  tff(c_13545, plain, (![A_555]: (r2_hidden(A_555, '#skF_13') | ~r2_hidden(A_555, '#skF_11'))), inference(splitRight, [status(thm)], [c_11877])).
% 12.45/4.40  tff(c_17480, plain, (![B_632]: (r2_hidden('#skF_1'('#skF_11', B_632), '#skF_13') | r1_tarski('#skF_11', B_632))), inference(resolution, [status(thm)], [c_6, c_13545])).
% 12.45/4.40  tff(c_17502, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_17480, c_4])).
% 12.45/4.40  tff(c_17514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_98, c_17502])).
% 12.45/4.40  tff(c_17515, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_485])).
% 12.45/4.40  tff(c_293, plain, (![A_98, B_99]: (~r2_hidden('#skF_4'(k4_xboole_0(A_98, B_99)), B_99) | k4_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_132])).
% 12.45/4.40  tff(c_306, plain, (![A_16]: (~r2_hidden('#skF_4'(A_16), k1_xboole_0) | k4_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_293])).
% 12.45/4.40  tff(c_313, plain, (![A_16]: (~r2_hidden('#skF_4'(A_16), k1_xboole_0) | k1_xboole_0=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_306])).
% 12.45/4.40  tff(c_17521, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_17515, c_313])).
% 12.45/4.40  tff(c_17534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_17521])).
% 12.45/4.40  tff(c_17535, plain, (~r1_tarski('#skF_12', '#skF_14')), inference(splitRight, [status(thm)], [c_66])).
% 12.45/4.40  tff(c_17536, plain, (r1_tarski('#skF_11', '#skF_13')), inference(splitRight, [status(thm)], [c_66])).
% 12.45/4.40  tff(c_17537, plain, (![A_633, B_634]: (k4_xboole_0(A_633, B_634)=k1_xboole_0 | ~r1_tarski(A_633, B_634))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.45/4.40  tff(c_17545, plain, (k4_xboole_0('#skF_11', '#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_17536, c_17537])).
% 12.45/4.40  tff(c_17802, plain, (![D_675, A_676, B_677]: (r2_hidden(D_675, k4_xboole_0(A_676, B_677)) | r2_hidden(D_675, B_677) | ~r2_hidden(D_675, A_676))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_17834, plain, (![D_678]: (r2_hidden(D_678, k1_xboole_0) | r2_hidden(D_678, '#skF_13') | ~r2_hidden(D_678, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_17545, c_17802])).
% 12.45/4.40  tff(c_17648, plain, (![D_649, B_650, A_651]: (~r2_hidden(D_649, B_650) | ~r2_hidden(D_649, k4_xboole_0(A_651, B_650)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_17668, plain, (![D_649, A_16]: (~r2_hidden(D_649, k1_xboole_0) | ~r2_hidden(D_649, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_17648])).
% 12.45/4.40  tff(c_17868, plain, (![D_681, A_682]: (~r2_hidden(D_681, A_682) | r2_hidden(D_681, '#skF_13') | ~r2_hidden(D_681, '#skF_11'))), inference(resolution, [status(thm)], [c_17834, c_17668])).
% 12.45/4.40  tff(c_18042, plain, (![A_695]: (r2_hidden('#skF_4'(A_695), '#skF_13') | ~r2_hidden('#skF_4'(A_695), '#skF_11') | k1_xboole_0=A_695)), inference(resolution, [status(thm)], [c_26, c_17868])).
% 12.45/4.40  tff(c_18057, plain, (r2_hidden('#skF_4'('#skF_11'), '#skF_13') | k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_26, c_18042])).
% 12.45/4.40  tff(c_18058, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_18057])).
% 12.45/4.40  tff(c_18080, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_68])).
% 12.45/4.40  tff(c_18078, plain, (![A_16]: (k4_xboole_0(A_16, '#skF_11')=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_32])).
% 12.45/4.40  tff(c_18073, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_28])).
% 12.45/4.40  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_18800, plain, (![A_752, B_753, C_754]: (~r2_hidden('#skF_2'(A_752, B_753, C_754), C_754) | r2_hidden('#skF_3'(A_752, B_753, C_754), C_754) | k4_xboole_0(A_752, B_753)=C_754)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_18809, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k4_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_18800])).
% 12.45/4.40  tff(c_18811, plain, (![A_755, B_756]: (r2_hidden('#skF_3'(A_755, B_756, A_755), A_755) | k4_xboole_0(A_755, B_756)=A_755)), inference(resolution, [status(thm)], [c_24, c_18800])).
% 12.45/4.40  tff(c_22099, plain, (![A_932, B_933, B_934]: (r2_hidden('#skF_3'(A_932, B_933, A_932), B_934) | ~r1_tarski(A_932, B_934) | k4_xboole_0(A_932, B_933)=A_932)), inference(resolution, [status(thm)], [c_18811, c_2])).
% 12.45/4.40  tff(c_18069, plain, (![D_649, A_16]: (~r2_hidden(D_649, '#skF_11') | ~r2_hidden(D_649, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_17668])).
% 12.45/4.40  tff(c_22203, plain, (![A_937, B_938, A_939]: (~r2_hidden('#skF_3'(A_937, B_938, A_937), A_939) | ~r1_tarski(A_937, '#skF_11') | k4_xboole_0(A_937, B_938)=A_937)), inference(resolution, [status(thm)], [c_22099, c_18069])).
% 12.45/4.40  tff(c_22254, plain, (![A_945, B_946]: (~r1_tarski(A_945, '#skF_11') | k4_xboole_0(A_945, B_946)=A_945)), inference(resolution, [status(thm)], [c_18809, c_22203])).
% 12.45/4.40  tff(c_22272, plain, (![A_14, B_946]: (k4_xboole_0(A_14, B_946)=A_14 | k4_xboole_0(A_14, '#skF_11')!='#skF_11')), inference(resolution, [status(thm)], [c_18073, c_22254])).
% 12.45/4.40  tff(c_22286, plain, (![B_946]: (k4_xboole_0('#skF_11', B_946)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_18078, c_22272])).
% 12.45/4.40  tff(c_17564, plain, (![A_639, B_640]: (~r2_hidden('#skF_1'(A_639, B_640), B_640) | r1_tarski(A_639, B_640))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.45/4.40  tff(c_17570, plain, (![A_641]: (r1_tarski(A_641, A_641))), inference(resolution, [status(thm)], [c_6, c_17564])).
% 12.45/4.40  tff(c_17574, plain, (![A_641]: (k4_xboole_0(A_641, A_641)=k1_xboole_0)), inference(resolution, [status(thm)], [c_17570, c_30])).
% 12.45/4.40  tff(c_18071, plain, (![A_641]: (k4_xboole_0(A_641, A_641)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_17574])).
% 12.45/4.40  tff(c_19238, plain, (![A_779, B_780, C_781]: (~r2_hidden('#skF_2'(A_779, B_780, C_781), B_780) | r2_hidden('#skF_3'(A_779, B_780, C_781), C_781) | k4_xboole_0(A_779, B_780)=C_781)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_19241, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_19238])).
% 12.45/4.40  tff(c_19246, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | C_8='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_18071, c_19241])).
% 12.45/4.40  tff(c_42, plain, (![A_18, B_19, D_45]: (r2_hidden('#skF_9'(A_18, B_19, k2_zfmisc_1(A_18, B_19), D_45), A_18) | ~r2_hidden(D_45, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.45/4.40  tff(c_17921, plain, (![A_685, B_686, C_687, D_688]: (r2_hidden(k4_tarski(A_685, B_686), k2_zfmisc_1(C_687, D_688)) | ~r2_hidden(B_686, D_688) | ~r2_hidden(A_685, C_687))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.45/4.40  tff(c_24818, plain, (![C_1032, D_1035, B_1034, A_1033, B_1036]: (r2_hidden(k4_tarski(A_1033, B_1036), B_1034) | ~r1_tarski(k2_zfmisc_1(C_1032, D_1035), B_1034) | ~r2_hidden(B_1036, D_1035) | ~r2_hidden(A_1033, C_1032))), inference(resolution, [status(thm)], [c_17921, c_2])).
% 12.45/4.40  tff(c_24892, plain, (![A_1039, B_1040]: (r2_hidden(k4_tarski(A_1039, B_1040), k2_zfmisc_1('#skF_13', '#skF_14')) | ~r2_hidden(B_1040, '#skF_12') | ~r2_hidden(A_1039, '#skF_11'))), inference(resolution, [status(thm)], [c_70, c_24818])).
% 12.45/4.40  tff(c_62, plain, (![B_53, D_55, A_52, C_54]: (r2_hidden(B_53, D_55) | ~r2_hidden(k4_tarski(A_52, B_53), k2_zfmisc_1(C_54, D_55)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.45/4.40  tff(c_24916, plain, (![B_1040, A_1039]: (r2_hidden(B_1040, '#skF_14') | ~r2_hidden(B_1040, '#skF_12') | ~r2_hidden(A_1039, '#skF_11'))), inference(resolution, [status(thm)], [c_24892, c_62])).
% 12.45/4.40  tff(c_24923, plain, (![A_1041]: (~r2_hidden(A_1041, '#skF_11'))), inference(splitLeft, [status(thm)], [c_24916])).
% 12.45/4.40  tff(c_25053, plain, (![D_1042, B_1043]: (~r2_hidden(D_1042, k2_zfmisc_1('#skF_11', B_1043)))), inference(resolution, [status(thm)], [c_42, c_24923])).
% 12.45/4.40  tff(c_25172, plain, (![B_1043]: (k2_zfmisc_1('#skF_11', B_1043)='#skF_11')), inference(resolution, [status(thm)], [c_19246, c_25053])).
% 12.45/4.40  tff(c_17544, plain, (k4_xboole_0(k2_zfmisc_1('#skF_11', '#skF_12'), k2_zfmisc_1('#skF_13', '#skF_14'))=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_17537])).
% 12.45/4.40  tff(c_18014, plain, (![D_694]: (r2_hidden(D_694, k1_xboole_0) | r2_hidden(D_694, k2_zfmisc_1('#skF_13', '#skF_14')) | ~r2_hidden(D_694, k2_zfmisc_1('#skF_11', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_17544, c_17802])).
% 12.45/4.40  tff(c_18034, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k1_xboole_0) | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_13', '#skF_14')) | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_18014])).
% 12.45/4.40  tff(c_18041, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k1_xboole_0) | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_68, c_18034])).
% 12.45/4.40  tff(c_18294, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), '#skF_11') | r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_18041])).
% 12.45/4.40  tff(c_18295, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(splitLeft, [status(thm)], [c_18294])).
% 12.45/4.40  tff(c_17684, plain, (![C_654, B_655, A_656]: (r2_hidden(C_654, B_655) | ~r2_hidden(C_654, A_656) | ~r1_tarski(A_656, B_655))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.45/4.40  tff(c_17706, plain, (![A_660, B_661]: (r2_hidden('#skF_4'(A_660), B_661) | ~r1_tarski(A_660, B_661) | k1_xboole_0=A_660)), inference(resolution, [status(thm)], [c_26, c_17684])).
% 12.45/4.40  tff(c_17725, plain, (![A_660, B_7, A_6]: (~r2_hidden('#skF_4'(A_660), B_7) | ~r1_tarski(A_660, k4_xboole_0(A_6, B_7)) | k1_xboole_0=A_660)), inference(resolution, [status(thm)], [c_17706, c_10])).
% 12.45/4.40  tff(c_18708, plain, (![A_744, B_745, A_746]: (~r2_hidden('#skF_4'(A_744), B_745) | ~r1_tarski(A_744, k4_xboole_0(A_746, B_745)) | A_744='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_17725])).
% 12.45/4.40  tff(c_18716, plain, (![A_746]: (~r1_tarski(k2_zfmisc_1('#skF_11', '#skF_12'), k4_xboole_0(A_746, k2_zfmisc_1('#skF_13', '#skF_14'))) | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_11')), inference(resolution, [status(thm)], [c_18295, c_18708])).
% 12.45/4.40  tff(c_18782, plain, (![A_751]: (~r1_tarski(k2_zfmisc_1('#skF_11', '#skF_12'), k4_xboole_0(A_751, k2_zfmisc_1('#skF_13', '#skF_14'))))), inference(negUnitSimplification, [status(thm)], [c_18080, c_18716])).
% 12.45/4.40  tff(c_18794, plain, (![A_751]: (k4_xboole_0(k2_zfmisc_1('#skF_11', '#skF_12'), k4_xboole_0(A_751, k2_zfmisc_1('#skF_13', '#skF_14')))!='#skF_11')), inference(resolution, [status(thm)], [c_18073, c_18782])).
% 12.45/4.40  tff(c_25204, plain, (![A_751]: (k4_xboole_0('#skF_11', k4_xboole_0(A_751, k2_zfmisc_1('#skF_13', '#skF_14')))!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_25172, c_18794])).
% 12.45/4.40  tff(c_25226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22286, c_25204])).
% 12.45/4.40  tff(c_25228, plain, (![B_1044]: (r2_hidden(B_1044, '#skF_14') | ~r2_hidden(B_1044, '#skF_12'))), inference(splitRight, [status(thm)], [c_24916])).
% 12.45/4.40  tff(c_25355, plain, (![A_1049]: (r1_tarski(A_1049, '#skF_14') | ~r2_hidden('#skF_1'(A_1049, '#skF_14'), '#skF_12'))), inference(resolution, [status(thm)], [c_25228, c_4])).
% 12.45/4.40  tff(c_25367, plain, (r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_6, c_25355])).
% 12.45/4.40  tff(c_25373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17535, c_17535, c_25367])).
% 12.45/4.40  tff(c_25374, plain, (r2_hidden('#skF_4'(k2_zfmisc_1('#skF_11', '#skF_12')), '#skF_11')), inference(splitRight, [status(thm)], [c_18294])).
% 12.45/4.40  tff(c_17884, plain, (![A_683, B_684]: (~r2_hidden('#skF_4'(k4_xboole_0(A_683, B_684)), B_684) | k4_xboole_0(A_683, B_684)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_17648])).
% 12.45/4.40  tff(c_17908, plain, (![A_16]: (~r2_hidden('#skF_4'(A_16), k1_xboole_0) | k4_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_17884])).
% 12.45/4.40  tff(c_17919, plain, (![A_16]: (~r2_hidden('#skF_4'(A_16), k1_xboole_0) | k1_xboole_0=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_17908])).
% 12.45/4.40  tff(c_18063, plain, (![A_16]: (~r2_hidden('#skF_4'(A_16), '#skF_11') | A_16='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_18058, c_18058, c_17919])).
% 12.45/4.40  tff(c_25378, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_25374, c_18063])).
% 12.45/4.40  tff(c_25388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18080, c_25378])).
% 12.45/4.40  tff(c_25390, plain, (k1_xboole_0!='#skF_11'), inference(splitRight, [status(thm)], [c_18057])).
% 12.45/4.40  tff(c_26182, plain, (![A_1108, B_1109, C_1110]: (r2_hidden('#skF_2'(A_1108, B_1109, C_1110), A_1108) | r2_hidden('#skF_3'(A_1108, B_1109, C_1110), C_1110) | k4_xboole_0(A_1108, B_1109)=C_1110)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.45/4.40  tff(c_26189, plain, (![A_1108, C_1110]: (r2_hidden('#skF_3'(A_1108, A_1108, C_1110), C_1110) | k4_xboole_0(A_1108, A_1108)=C_1110)), inference(resolution, [status(thm)], [c_26182, c_22])).
% 12.45/4.40  tff(c_26236, plain, (![A_1108, C_1110]: (r2_hidden('#skF_3'(A_1108, A_1108, C_1110), C_1110) | k1_xboole_0=C_1110)), inference(demodulation, [status(thm), theory('equality')], [c_17574, c_26189])).
% 12.45/4.40  tff(c_32620, plain, (![C_1376, B_1380, A_1377, D_1379, B_1378]: (r2_hidden(k4_tarski(A_1377, B_1380), B_1378) | ~r1_tarski(k2_zfmisc_1(C_1376, D_1379), B_1378) | ~r2_hidden(B_1380, D_1379) | ~r2_hidden(A_1377, C_1376))), inference(resolution, [status(thm)], [c_17921, c_2])).
% 12.45/4.40  tff(c_32682, plain, (![A_1383, B_1384]: (r2_hidden(k4_tarski(A_1383, B_1384), k2_zfmisc_1('#skF_13', '#skF_14')) | ~r2_hidden(B_1384, '#skF_12') | ~r2_hidden(A_1383, '#skF_11'))), inference(resolution, [status(thm)], [c_70, c_32620])).
% 12.45/4.40  tff(c_32703, plain, (![B_1384, A_1383]: (r2_hidden(B_1384, '#skF_14') | ~r2_hidden(B_1384, '#skF_12') | ~r2_hidden(A_1383, '#skF_11'))), inference(resolution, [status(thm)], [c_32682, c_62])).
% 12.45/4.40  tff(c_32707, plain, (![A_1385]: (~r2_hidden(A_1385, '#skF_11'))), inference(splitLeft, [status(thm)], [c_32703])).
% 12.45/4.40  tff(c_32769, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_26236, c_32707])).
% 12.45/4.40  tff(c_32832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25390, c_32769])).
% 12.45/4.40  tff(c_32834, plain, (![B_1386]: (r2_hidden(B_1386, '#skF_14') | ~r2_hidden(B_1386, '#skF_12'))), inference(splitRight, [status(thm)], [c_32703])).
% 12.45/4.40  tff(c_32918, plain, (![A_1387]: (r1_tarski(A_1387, '#skF_14') | ~r2_hidden('#skF_1'(A_1387, '#skF_14'), '#skF_12'))), inference(resolution, [status(thm)], [c_32834, c_4])).
% 12.45/4.40  tff(c_32930, plain, (r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_6, c_32918])).
% 12.45/4.40  tff(c_32936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17535, c_17535, c_32930])).
% 12.45/4.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.45/4.40  
% 12.45/4.40  Inference rules
% 12.45/4.40  ----------------------
% 12.45/4.40  #Ref     : 0
% 12.45/4.40  #Sup     : 8271
% 12.45/4.40  #Fact    : 4
% 12.45/4.40  #Define  : 0
% 12.45/4.40  #Split   : 27
% 12.45/4.40  #Chain   : 0
% 12.45/4.40  #Close   : 0
% 12.45/4.40  
% 12.45/4.40  Ordering : KBO
% 12.45/4.40  
% 12.45/4.40  Simplification rules
% 12.45/4.40  ----------------------
% 12.45/4.40  #Subsume      : 4695
% 12.45/4.40  #Demod        : 2566
% 12.45/4.40  #Tautology    : 1663
% 12.45/4.40  #SimpNegUnit  : 409
% 12.45/4.40  #BackRed      : 252
% 12.45/4.40  
% 12.45/4.40  #Partial instantiations: 0
% 12.45/4.40  #Strategies tried      : 1
% 12.45/4.40  
% 12.45/4.40  Timing (in seconds)
% 12.45/4.40  ----------------------
% 12.45/4.41  Preprocessing        : 0.30
% 12.45/4.41  Parsing              : 0.16
% 12.45/4.41  CNF conversion       : 0.03
% 12.45/4.41  Main loop            : 3.32
% 12.45/4.41  Inferencing          : 0.87
% 12.45/4.41  Reduction            : 1.06
% 12.45/4.41  Demodulation         : 0.72
% 12.45/4.41  BG Simplification    : 0.08
% 12.45/4.41  Subsumption          : 1.10
% 12.45/4.41  Abstraction          : 0.13
% 12.45/4.41  MUC search           : 0.00
% 12.45/4.41  Cooper               : 0.00
% 12.45/4.41  Total                : 3.68
% 12.45/4.41  Index Insertion      : 0.00
% 12.45/4.41  Index Deletion       : 0.00
% 12.45/4.41  Index Matching       : 0.00
% 12.45/4.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
