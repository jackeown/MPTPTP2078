%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:43 EST 2020

% Result     : Theorem 6.29s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 303 expanded)
%              Number of leaves         :   32 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 779 expanded)
%              Number of equality atoms :  152 ( 459 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_90,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_5'(A_29),A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_79,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,A_48)
      | ~ r2_hidden(D_47,k4_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_48,B_49)),A_48)
      | k4_xboole_0(A_48,B_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_3516,plain,(
    ! [D_368,B_369,A_370] :
      ( ~ r2_hidden(D_368,B_369)
      | ~ r2_hidden(D_368,k4_xboole_0(A_370,B_369)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3638,plain,(
    ! [A_401,B_402] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_401,B_402)),B_402)
      | k4_xboole_0(A_401,B_402) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_3516])).

tff(c_3649,plain,(
    ! [A_403] : k4_xboole_0(A_403,A_403) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_3638])).

tff(c_44,plain,(
    ! [A_15,C_17,B_16] :
      ( ~ r2_hidden(A_15,C_17)
      | k4_xboole_0(k2_tarski(A_15,B_16),C_17) != k2_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3664,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,k2_tarski(A_15,B_16))
      | k2_tarski(A_15,B_16) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3649,c_44])).

tff(c_3677,plain,(
    ! [A_15,B_16] : k2_tarski(A_15,B_16) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3664])).

tff(c_3557,plain,(
    ! [D_377,B_378,A_379] :
      ( D_377 = B_378
      | D_377 = A_379
      | ~ r2_hidden(D_377,k2_tarski(A_379,B_378)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3568,plain,(
    ! [A_379,B_378] :
      ( '#skF_5'(k2_tarski(A_379,B_378)) = B_378
      | '#skF_5'(k2_tarski(A_379,B_378)) = A_379
      | k2_tarski(A_379,B_378) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_3557])).

tff(c_4233,plain,(
    ! [A_379,B_378] :
      ( '#skF_5'(k2_tarski(A_379,B_378)) = B_378
      | '#skF_5'(k2_tarski(A_379,B_378)) = A_379 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3677,c_3568])).

tff(c_4244,plain,(
    ! [B_378] : '#skF_5'(k2_tarski(B_378,B_378)) = B_378 ),
    inference(factorization,[status(thm),theory(equality)],[c_4233])).

tff(c_4361,plain,(
    ! [B_513] : '#skF_5'(k2_tarski(B_513,B_513)) = B_513 ),
    inference(factorization,[status(thm),theory(equality)],[c_4233])).

tff(c_46,plain,(
    ! [A_18,B_19,C_20] : k4_tarski(k4_tarski(A_18,B_19),C_20) = k3_mcart_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3584,plain,(
    ! [D_385,A_386,C_387] :
      ( ~ r2_hidden(D_385,A_386)
      | k4_tarski(C_387,D_385) != '#skF_5'(A_386)
      | k1_xboole_0 = A_386 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3595,plain,(
    ! [C_391,A_392] :
      ( k4_tarski(C_391,'#skF_5'(A_392)) != '#skF_5'(A_392)
      | k1_xboole_0 = A_392 ) ),
    inference(resolution,[status(thm)],[c_52,c_3584])).

tff(c_3599,plain,(
    ! [A_18,B_19,A_392] :
      ( k3_mcart_1(A_18,B_19,'#skF_5'(A_392)) != '#skF_5'(A_392)
      | k1_xboole_0 = A_392 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3595])).

tff(c_4399,plain,(
    ! [A_18,B_19,B_513] :
      ( k3_mcart_1(A_18,B_19,B_513) != '#skF_5'(k2_tarski(B_513,B_513))
      | k2_tarski(B_513,B_513) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4361,c_3599])).

tff(c_4421,plain,(
    ! [A_18,B_19,B_513] :
      ( k3_mcart_1(A_18,B_19,B_513) != B_513
      | k2_tarski(B_513,B_513) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4244,c_4399])).

tff(c_4422,plain,(
    ! [A_18,B_19,B_513] : k3_mcart_1(A_18,B_19,B_513) != B_513 ),
    inference(negUnitSimplification,[status(thm)],[c_3677,c_4421])).

tff(c_58,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_85,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_1160,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( k3_mcart_1(k5_mcart_1(A_232,B_233,C_234,D_235),k6_mcart_1(A_232,B_233,C_234,D_235),k7_mcart_1(A_232,B_233,C_234,D_235)) = D_235
      | ~ m1_subset_1(D_235,k3_zfmisc_1(A_232,B_233,C_234))
      | k1_xboole_0 = C_234
      | k1_xboole_0 = B_233
      | k1_xboole_0 = A_232 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1191,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_1160])).

tff(c_1197,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1191])).

tff(c_1198,plain,(
    k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_64,c_62,c_1197])).

tff(c_90,plain,(
    ! [D_50,B_51,A_52] :
      ( ~ r2_hidden(D_50,B_51)
      | ~ r2_hidden(D_50,k4_xboole_0(A_52,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_192,plain,(
    ! [A_80,B_81] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_80,B_81)),B_81)
      | k4_xboole_0(A_80,B_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_198,plain,(
    ! [A_82] : k4_xboole_0(A_82,A_82) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_192])).

tff(c_210,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,k2_tarski(A_15,B_16))
      | k2_tarski(A_15,B_16) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_44])).

tff(c_223,plain,(
    ! [A_15,B_16] : k2_tarski(A_15,B_16) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_210])).

tff(c_96,plain,(
    ! [D_53,B_54,A_55] :
      ( D_53 = B_54
      | D_53 = A_55
      | ~ r2_hidden(D_53,k2_tarski(A_55,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,(
    ! [A_55,B_54] :
      ( '#skF_5'(k2_tarski(A_55,B_54)) = B_54
      | '#skF_5'(k2_tarski(A_55,B_54)) = A_55
      | k2_tarski(A_55,B_54) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_96])).

tff(c_720,plain,(
    ! [A_173,B_174] :
      ( '#skF_5'(k2_tarski(A_173,B_174)) = B_174
      | '#skF_5'(k2_tarski(A_173,B_174)) = A_173 ) ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_107])).

tff(c_142,plain,(
    ! [C_62,A_63,D_64] :
      ( ~ r2_hidden(C_62,A_63)
      | k4_tarski(C_62,D_64) != '#skF_5'(A_63)
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_151,plain,(
    ! [D_12,D_64,B_8] :
      ( k4_tarski(D_12,D_64) != '#skF_5'(k2_tarski(D_12,B_8))
      | k2_tarski(D_12,B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_142])).

tff(c_317,plain,(
    ! [D_12,D_64,B_8] : k4_tarski(D_12,D_64) != '#skF_5'(k2_tarski(D_12,B_8)) ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_151])).

tff(c_1115,plain,(
    ! [A_215,D_216,B_217] :
      ( k4_tarski(A_215,D_216) != B_217
      | '#skF_5'(k2_tarski(A_215,B_217)) = A_215 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_317])).

tff(c_2969,plain,(
    ! [A_349,B_350,C_351,B_352] :
      ( k3_mcart_1(A_349,B_350,C_351) != B_352
      | '#skF_5'(k2_tarski(k4_tarski(A_349,B_350),B_352)) = k4_tarski(A_349,B_350) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1115])).

tff(c_3288,plain,(
    ! [B_363] :
      ( B_363 != '#skF_9'
      | '#skF_5'(k2_tarski(k4_tarski('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')),B_363)) = k4_tarski('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1198,c_2969])).

tff(c_22,plain,(
    ! [D_12,A_7] : r2_hidden(D_12,k2_tarski(A_7,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_150,plain,(
    ! [D_12,D_64,A_7] :
      ( k4_tarski(D_12,D_64) != '#skF_5'(k2_tarski(A_7,D_12))
      | k2_tarski(A_7,D_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_370,plain,(
    ! [D_12,D_64,A_7] : k4_tarski(D_12,D_64) != '#skF_5'(k2_tarski(A_7,D_12)) ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_150])).

tff(c_3337,plain,(
    ! [B_363,D_64] :
      ( k4_tarski(B_363,D_64) != k4_tarski('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'))
      | B_363 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3288,c_370])).

tff(c_3513,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3337])).

tff(c_3514,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3552,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_3514])).

tff(c_4606,plain,(
    ! [A_548,B_549,C_550,D_551] :
      ( k3_mcart_1(k5_mcart_1(A_548,B_549,C_550,D_551),k6_mcart_1(A_548,B_549,C_550,D_551),k7_mcart_1(A_548,B_549,C_550,D_551)) = D_551
      | ~ m1_subset_1(D_551,k3_zfmisc_1(A_548,B_549,C_550))
      | k1_xboole_0 = C_550
      | k1_xboole_0 = B_549
      | k1_xboole_0 = A_548 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4633,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3552,c_4606])).

tff(c_4637,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4633])).

tff(c_4639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_64,c_62,c_4422,c_4637])).

tff(c_4640,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3514])).

tff(c_5650,plain,(
    ! [A_714,B_715,C_716,D_717] :
      ( k3_mcart_1(k5_mcart_1(A_714,B_715,C_716,D_717),k6_mcart_1(A_714,B_715,C_716,D_717),k7_mcart_1(A_714,B_715,C_716,D_717)) = D_717
      | ~ m1_subset_1(D_717,k3_zfmisc_1(A_714,B_715,C_716))
      | k1_xboole_0 = C_716
      | k1_xboole_0 = B_715
      | k1_xboole_0 = A_714 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5681,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4640,c_5650])).

tff(c_5687,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5681])).

tff(c_5688,plain,(
    k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_64,c_62,c_5687])).

tff(c_4726,plain,(
    ! [A_573,B_574] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_573,B_574)),B_574)
      | k4_xboole_0(A_573,B_574) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_3516])).

tff(c_4736,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_4726])).

tff(c_4777,plain,(
    ! [A_578,C_579,B_580] :
      ( ~ r2_hidden(A_578,C_579)
      | k4_xboole_0(k2_tarski(A_578,B_580),C_579) != k2_tarski(A_578,B_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4781,plain,(
    ! [A_578,B_580] :
      ( ~ r2_hidden(A_578,k2_tarski(A_578,B_580))
      | k2_tarski(A_578,B_580) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4736,c_4777])).

tff(c_4783,plain,(
    ! [A_578,B_580] : k2_tarski(A_578,B_580) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4781])).

tff(c_4646,plain,(
    ! [D_552,B_553,A_554] :
      ( D_552 = B_553
      | D_552 = A_554
      | ~ r2_hidden(D_552,k2_tarski(A_554,B_553)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4657,plain,(
    ! [A_554,B_553] :
      ( '#skF_5'(k2_tarski(A_554,B_553)) = B_553
      | '#skF_5'(k2_tarski(A_554,B_553)) = A_554
      | k2_tarski(A_554,B_553) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_4646])).

tff(c_4992,plain,(
    ! [A_636,B_637] :
      ( '#skF_5'(k2_tarski(A_636,B_637)) = B_637
      | '#skF_5'(k2_tarski(A_636,B_637)) = A_636 ) ),
    inference(negUnitSimplification,[status(thm)],[c_4783,c_4657])).

tff(c_4662,plain,(
    ! [C_555,A_556,D_557] :
      ( ~ r2_hidden(C_555,A_556)
      | k4_tarski(C_555,D_557) != '#skF_5'(A_556)
      | k1_xboole_0 = A_556 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4670,plain,(
    ! [D_12,D_557,A_7] :
      ( k4_tarski(D_12,D_557) != '#skF_5'(k2_tarski(A_7,D_12))
      | k2_tarski(A_7,D_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_4662])).

tff(c_4883,plain,(
    ! [D_12,D_557,A_7] : k4_tarski(D_12,D_557) != '#skF_5'(k2_tarski(A_7,D_12)) ),
    inference(negUnitSimplification,[status(thm)],[c_4783,c_4670])).

tff(c_5355,plain,(
    ! [B_668,D_669,A_670] :
      ( k4_tarski(B_668,D_669) != A_670
      | '#skF_5'(k2_tarski(A_670,B_668)) = B_668 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4992,c_4883])).

tff(c_7563,plain,(
    ! [A_841,B_842,C_843,A_844] :
      ( k3_mcart_1(A_841,B_842,C_843) != A_844
      | '#skF_5'(k2_tarski(A_844,k4_tarski(A_841,B_842))) = k4_tarski(A_841,B_842) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_5355])).

tff(c_7573,plain,(
    ! [A_845] :
      ( A_845 != '#skF_9'
      | '#skF_5'(k2_tarski(A_845,k4_tarski(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9'))) = k4_tarski(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5688,c_7563])).

tff(c_4673,plain,(
    ! [D_560,A_561,C_562] :
      ( ~ r2_hidden(D_560,A_561)
      | k4_tarski(C_562,D_560) != '#skF_5'(A_561)
      | k1_xboole_0 = A_561 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4682,plain,(
    ! [C_562,D_12,B_8] :
      ( k4_tarski(C_562,D_12) != '#skF_5'(k2_tarski(D_12,B_8))
      | k2_tarski(D_12,B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_4673])).

tff(c_4913,plain,(
    ! [C_562,D_12,B_8] : k4_tarski(C_562,D_12) != '#skF_5'(k2_tarski(D_12,B_8)) ),
    inference(negUnitSimplification,[status(thm)],[c_4783,c_4682])).

tff(c_7609,plain,(
    ! [C_562,A_845] :
      ( k4_tarski(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') != k4_tarski(C_562,A_845)
      | A_845 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7573,c_4913])).

tff(c_7667,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:18:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.29/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.29  
% 6.29/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.29  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 6.29/2.29  
% 6.29/2.29  %Foreground sorts:
% 6.29/2.29  
% 6.29/2.29  
% 6.29/2.29  %Background operators:
% 6.29/2.29  
% 6.29/2.29  
% 6.29/2.29  %Foreground operators:
% 6.29/2.29  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.29/2.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.29/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.29/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.29/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.29/2.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.29/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.29/2.29  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.29/2.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.29/2.29  tff('#skF_7', type, '#skF_7': $i).
% 6.29/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.29/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.29/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.29/2.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.29/2.29  tff('#skF_9', type, '#skF_9': $i).
% 6.29/2.29  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 6.29/2.29  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.29/2.29  tff('#skF_8', type, '#skF_8': $i).
% 6.29/2.29  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 6.29/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.29/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.29/2.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.29/2.29  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 6.29/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.29/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.29/2.29  
% 6.52/2.31  tff(f_114, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 6.52/2.31  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.52/2.31  tff(f_90, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 6.52/2.31  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.52/2.31  tff(f_54, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 6.52/2.31  tff(f_56, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.52/2.31  tff(f_74, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 6.52/2.31  tff(c_66, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.52/2.31  tff(c_64, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.52/2.31  tff(c_62, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.52/2.31  tff(c_60, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.52/2.31  tff(c_24, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.52/2.31  tff(c_52, plain, (![A_29]: (r2_hidden('#skF_5'(A_29), A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.52/2.31  tff(c_79, plain, (![D_47, A_48, B_49]: (r2_hidden(D_47, A_48) | ~r2_hidden(D_47, k4_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.52/2.31  tff(c_84, plain, (![A_48, B_49]: (r2_hidden('#skF_5'(k4_xboole_0(A_48, B_49)), A_48) | k4_xboole_0(A_48, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_79])).
% 6.52/2.31  tff(c_3516, plain, (![D_368, B_369, A_370]: (~r2_hidden(D_368, B_369) | ~r2_hidden(D_368, k4_xboole_0(A_370, B_369)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.52/2.31  tff(c_3638, plain, (![A_401, B_402]: (~r2_hidden('#skF_5'(k4_xboole_0(A_401, B_402)), B_402) | k4_xboole_0(A_401, B_402)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_3516])).
% 6.52/2.31  tff(c_3649, plain, (![A_403]: (k4_xboole_0(A_403, A_403)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_3638])).
% 6.52/2.31  tff(c_44, plain, (![A_15, C_17, B_16]: (~r2_hidden(A_15, C_17) | k4_xboole_0(k2_tarski(A_15, B_16), C_17)!=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.52/2.31  tff(c_3664, plain, (![A_15, B_16]: (~r2_hidden(A_15, k2_tarski(A_15, B_16)) | k2_tarski(A_15, B_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3649, c_44])).
% 6.52/2.31  tff(c_3677, plain, (![A_15, B_16]: (k2_tarski(A_15, B_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3664])).
% 6.52/2.31  tff(c_3557, plain, (![D_377, B_378, A_379]: (D_377=B_378 | D_377=A_379 | ~r2_hidden(D_377, k2_tarski(A_379, B_378)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.52/2.31  tff(c_3568, plain, (![A_379, B_378]: ('#skF_5'(k2_tarski(A_379, B_378))=B_378 | '#skF_5'(k2_tarski(A_379, B_378))=A_379 | k2_tarski(A_379, B_378)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_3557])).
% 6.52/2.31  tff(c_4233, plain, (![A_379, B_378]: ('#skF_5'(k2_tarski(A_379, B_378))=B_378 | '#skF_5'(k2_tarski(A_379, B_378))=A_379)), inference(negUnitSimplification, [status(thm)], [c_3677, c_3568])).
% 6.52/2.31  tff(c_4244, plain, (![B_378]: ('#skF_5'(k2_tarski(B_378, B_378))=B_378)), inference(factorization, [status(thm), theory('equality')], [c_4233])).
% 6.52/2.31  tff(c_4361, plain, (![B_513]: ('#skF_5'(k2_tarski(B_513, B_513))=B_513)), inference(factorization, [status(thm), theory('equality')], [c_4233])).
% 6.52/2.31  tff(c_46, plain, (![A_18, B_19, C_20]: (k4_tarski(k4_tarski(A_18, B_19), C_20)=k3_mcart_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.52/2.31  tff(c_3584, plain, (![D_385, A_386, C_387]: (~r2_hidden(D_385, A_386) | k4_tarski(C_387, D_385)!='#skF_5'(A_386) | k1_xboole_0=A_386)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.52/2.31  tff(c_3595, plain, (![C_391, A_392]: (k4_tarski(C_391, '#skF_5'(A_392))!='#skF_5'(A_392) | k1_xboole_0=A_392)), inference(resolution, [status(thm)], [c_52, c_3584])).
% 6.52/2.31  tff(c_3599, plain, (![A_18, B_19, A_392]: (k3_mcart_1(A_18, B_19, '#skF_5'(A_392))!='#skF_5'(A_392) | k1_xboole_0=A_392)), inference(superposition, [status(thm), theory('equality')], [c_46, c_3595])).
% 6.52/2.31  tff(c_4399, plain, (![A_18, B_19, B_513]: (k3_mcart_1(A_18, B_19, B_513)!='#skF_5'(k2_tarski(B_513, B_513)) | k2_tarski(B_513, B_513)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4361, c_3599])).
% 6.52/2.31  tff(c_4421, plain, (![A_18, B_19, B_513]: (k3_mcart_1(A_18, B_19, B_513)!=B_513 | k2_tarski(B_513, B_513)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4244, c_4399])).
% 6.52/2.31  tff(c_4422, plain, (![A_18, B_19, B_513]: (k3_mcart_1(A_18, B_19, B_513)!=B_513)), inference(negUnitSimplification, [status(thm)], [c_3677, c_4421])).
% 6.52/2.31  tff(c_58, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.52/2.31  tff(c_85, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_58])).
% 6.52/2.31  tff(c_1160, plain, (![A_232, B_233, C_234, D_235]: (k3_mcart_1(k5_mcart_1(A_232, B_233, C_234, D_235), k6_mcart_1(A_232, B_233, C_234, D_235), k7_mcart_1(A_232, B_233, C_234, D_235))=D_235 | ~m1_subset_1(D_235, k3_zfmisc_1(A_232, B_233, C_234)) | k1_xboole_0=C_234 | k1_xboole_0=B_233 | k1_xboole_0=A_232)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.52/2.31  tff(c_1191, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_85, c_1160])).
% 6.52/2.31  tff(c_1197, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1191])).
% 6.52/2.31  tff(c_1198, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_66, c_64, c_62, c_1197])).
% 6.52/2.31  tff(c_90, plain, (![D_50, B_51, A_52]: (~r2_hidden(D_50, B_51) | ~r2_hidden(D_50, k4_xboole_0(A_52, B_51)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.52/2.31  tff(c_192, plain, (![A_80, B_81]: (~r2_hidden('#skF_5'(k4_xboole_0(A_80, B_81)), B_81) | k4_xboole_0(A_80, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_90])).
% 6.52/2.31  tff(c_198, plain, (![A_82]: (k4_xboole_0(A_82, A_82)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_192])).
% 6.52/2.31  tff(c_210, plain, (![A_15, B_16]: (~r2_hidden(A_15, k2_tarski(A_15, B_16)) | k2_tarski(A_15, B_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_198, c_44])).
% 6.52/2.31  tff(c_223, plain, (![A_15, B_16]: (k2_tarski(A_15, B_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_210])).
% 6.52/2.31  tff(c_96, plain, (![D_53, B_54, A_55]: (D_53=B_54 | D_53=A_55 | ~r2_hidden(D_53, k2_tarski(A_55, B_54)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.52/2.31  tff(c_107, plain, (![A_55, B_54]: ('#skF_5'(k2_tarski(A_55, B_54))=B_54 | '#skF_5'(k2_tarski(A_55, B_54))=A_55 | k2_tarski(A_55, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_96])).
% 6.52/2.31  tff(c_720, plain, (![A_173, B_174]: ('#skF_5'(k2_tarski(A_173, B_174))=B_174 | '#skF_5'(k2_tarski(A_173, B_174))=A_173)), inference(negUnitSimplification, [status(thm)], [c_223, c_107])).
% 6.52/2.31  tff(c_142, plain, (![C_62, A_63, D_64]: (~r2_hidden(C_62, A_63) | k4_tarski(C_62, D_64)!='#skF_5'(A_63) | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.52/2.31  tff(c_151, plain, (![D_12, D_64, B_8]: (k4_tarski(D_12, D_64)!='#skF_5'(k2_tarski(D_12, B_8)) | k2_tarski(D_12, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_142])).
% 6.52/2.31  tff(c_317, plain, (![D_12, D_64, B_8]: (k4_tarski(D_12, D_64)!='#skF_5'(k2_tarski(D_12, B_8)))), inference(negUnitSimplification, [status(thm)], [c_223, c_151])).
% 6.52/2.31  tff(c_1115, plain, (![A_215, D_216, B_217]: (k4_tarski(A_215, D_216)!=B_217 | '#skF_5'(k2_tarski(A_215, B_217))=A_215)), inference(superposition, [status(thm), theory('equality')], [c_720, c_317])).
% 6.52/2.31  tff(c_2969, plain, (![A_349, B_350, C_351, B_352]: (k3_mcart_1(A_349, B_350, C_351)!=B_352 | '#skF_5'(k2_tarski(k4_tarski(A_349, B_350), B_352))=k4_tarski(A_349, B_350))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1115])).
% 6.52/2.31  tff(c_3288, plain, (![B_363]: (B_363!='#skF_9' | '#skF_5'(k2_tarski(k4_tarski('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')), B_363))=k4_tarski('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1198, c_2969])).
% 6.52/2.31  tff(c_22, plain, (![D_12, A_7]: (r2_hidden(D_12, k2_tarski(A_7, D_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.52/2.31  tff(c_150, plain, (![D_12, D_64, A_7]: (k4_tarski(D_12, D_64)!='#skF_5'(k2_tarski(A_7, D_12)) | k2_tarski(A_7, D_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_142])).
% 6.52/2.31  tff(c_370, plain, (![D_12, D_64, A_7]: (k4_tarski(D_12, D_64)!='#skF_5'(k2_tarski(A_7, D_12)))), inference(negUnitSimplification, [status(thm)], [c_223, c_150])).
% 6.52/2.31  tff(c_3337, plain, (![B_363, D_64]: (k4_tarski(B_363, D_64)!=k4_tarski('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')) | B_363!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3288, c_370])).
% 6.52/2.31  tff(c_3513, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3337])).
% 6.52/2.31  tff(c_3514, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 6.52/2.31  tff(c_3552, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_3514])).
% 6.52/2.31  tff(c_4606, plain, (![A_548, B_549, C_550, D_551]: (k3_mcart_1(k5_mcart_1(A_548, B_549, C_550, D_551), k6_mcart_1(A_548, B_549, C_550, D_551), k7_mcart_1(A_548, B_549, C_550, D_551))=D_551 | ~m1_subset_1(D_551, k3_zfmisc_1(A_548, B_549, C_550)) | k1_xboole_0=C_550 | k1_xboole_0=B_549 | k1_xboole_0=A_548)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.52/2.31  tff(c_4633, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3552, c_4606])).
% 6.52/2.31  tff(c_4637, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4633])).
% 6.52/2.31  tff(c_4639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_64, c_62, c_4422, c_4637])).
% 6.52/2.31  tff(c_4640, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_3514])).
% 6.52/2.31  tff(c_5650, plain, (![A_714, B_715, C_716, D_717]: (k3_mcart_1(k5_mcart_1(A_714, B_715, C_716, D_717), k6_mcart_1(A_714, B_715, C_716, D_717), k7_mcart_1(A_714, B_715, C_716, D_717))=D_717 | ~m1_subset_1(D_717, k3_zfmisc_1(A_714, B_715, C_716)) | k1_xboole_0=C_716 | k1_xboole_0=B_715 | k1_xboole_0=A_714)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.52/2.31  tff(c_5681, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4640, c_5650])).
% 6.52/2.31  tff(c_5687, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5681])).
% 6.52/2.31  tff(c_5688, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_66, c_64, c_62, c_5687])).
% 6.52/2.31  tff(c_4726, plain, (![A_573, B_574]: (~r2_hidden('#skF_5'(k4_xboole_0(A_573, B_574)), B_574) | k4_xboole_0(A_573, B_574)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_3516])).
% 6.52/2.31  tff(c_4736, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_4726])).
% 6.52/2.31  tff(c_4777, plain, (![A_578, C_579, B_580]: (~r2_hidden(A_578, C_579) | k4_xboole_0(k2_tarski(A_578, B_580), C_579)!=k2_tarski(A_578, B_580))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.52/2.31  tff(c_4781, plain, (![A_578, B_580]: (~r2_hidden(A_578, k2_tarski(A_578, B_580)) | k2_tarski(A_578, B_580)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4736, c_4777])).
% 6.52/2.31  tff(c_4783, plain, (![A_578, B_580]: (k2_tarski(A_578, B_580)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4781])).
% 6.52/2.31  tff(c_4646, plain, (![D_552, B_553, A_554]: (D_552=B_553 | D_552=A_554 | ~r2_hidden(D_552, k2_tarski(A_554, B_553)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.52/2.31  tff(c_4657, plain, (![A_554, B_553]: ('#skF_5'(k2_tarski(A_554, B_553))=B_553 | '#skF_5'(k2_tarski(A_554, B_553))=A_554 | k2_tarski(A_554, B_553)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_4646])).
% 6.52/2.31  tff(c_4992, plain, (![A_636, B_637]: ('#skF_5'(k2_tarski(A_636, B_637))=B_637 | '#skF_5'(k2_tarski(A_636, B_637))=A_636)), inference(negUnitSimplification, [status(thm)], [c_4783, c_4657])).
% 6.52/2.31  tff(c_4662, plain, (![C_555, A_556, D_557]: (~r2_hidden(C_555, A_556) | k4_tarski(C_555, D_557)!='#skF_5'(A_556) | k1_xboole_0=A_556)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.52/2.31  tff(c_4670, plain, (![D_12, D_557, A_7]: (k4_tarski(D_12, D_557)!='#skF_5'(k2_tarski(A_7, D_12)) | k2_tarski(A_7, D_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_4662])).
% 6.52/2.31  tff(c_4883, plain, (![D_12, D_557, A_7]: (k4_tarski(D_12, D_557)!='#skF_5'(k2_tarski(A_7, D_12)))), inference(negUnitSimplification, [status(thm)], [c_4783, c_4670])).
% 6.52/2.31  tff(c_5355, plain, (![B_668, D_669, A_670]: (k4_tarski(B_668, D_669)!=A_670 | '#skF_5'(k2_tarski(A_670, B_668))=B_668)), inference(superposition, [status(thm), theory('equality')], [c_4992, c_4883])).
% 6.52/2.31  tff(c_7563, plain, (![A_841, B_842, C_843, A_844]: (k3_mcart_1(A_841, B_842, C_843)!=A_844 | '#skF_5'(k2_tarski(A_844, k4_tarski(A_841, B_842)))=k4_tarski(A_841, B_842))), inference(superposition, [status(thm), theory('equality')], [c_46, c_5355])).
% 6.52/2.31  tff(c_7573, plain, (![A_845]: (A_845!='#skF_9' | '#skF_5'(k2_tarski(A_845, k4_tarski(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')))=k4_tarski(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5688, c_7563])).
% 6.52/2.31  tff(c_4673, plain, (![D_560, A_561, C_562]: (~r2_hidden(D_560, A_561) | k4_tarski(C_562, D_560)!='#skF_5'(A_561) | k1_xboole_0=A_561)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.52/2.31  tff(c_4682, plain, (![C_562, D_12, B_8]: (k4_tarski(C_562, D_12)!='#skF_5'(k2_tarski(D_12, B_8)) | k2_tarski(D_12, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_4673])).
% 6.52/2.31  tff(c_4913, plain, (![C_562, D_12, B_8]: (k4_tarski(C_562, D_12)!='#skF_5'(k2_tarski(D_12, B_8)))), inference(negUnitSimplification, [status(thm)], [c_4783, c_4682])).
% 6.52/2.31  tff(c_7609, plain, (![C_562, A_845]: (k4_tarski(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')!=k4_tarski(C_562, A_845) | A_845!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7573, c_4913])).
% 6.52/2.31  tff(c_7667, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_7609])).
% 6.52/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.52/2.31  
% 6.52/2.31  Inference rules
% 6.52/2.31  ----------------------
% 6.52/2.31  #Ref     : 21
% 6.52/2.31  #Sup     : 1760
% 6.52/2.31  #Fact    : 12
% 6.52/2.31  #Define  : 0
% 6.52/2.31  #Split   : 2
% 6.52/2.31  #Chain   : 0
% 6.52/2.31  #Close   : 0
% 6.52/2.31  
% 6.52/2.31  Ordering : KBO
% 6.52/2.31  
% 6.52/2.31  Simplification rules
% 6.52/2.31  ----------------------
% 6.52/2.31  #Subsume      : 592
% 6.52/2.31  #Demod        : 617
% 6.52/2.31  #Tautology    : 557
% 6.52/2.31  #SimpNegUnit  : 235
% 6.52/2.31  #BackRed      : 0
% 6.52/2.31  
% 6.52/2.31  #Partial instantiations: 0
% 6.52/2.31  #Strategies tried      : 1
% 6.52/2.31  
% 6.52/2.31  Timing (in seconds)
% 6.52/2.31  ----------------------
% 6.52/2.31  Preprocessing        : 0.32
% 6.52/2.31  Parsing              : 0.16
% 6.52/2.31  CNF conversion       : 0.03
% 6.52/2.31  Main loop            : 1.23
% 6.52/2.31  Inferencing          : 0.44
% 6.52/2.31  Reduction            : 0.38
% 6.52/2.31  Demodulation         : 0.24
% 6.52/2.32  BG Simplification    : 0.05
% 6.52/2.32  Subsumption          : 0.26
% 6.52/2.32  Abstraction          : 0.07
% 6.52/2.32  MUC search           : 0.00
% 6.52/2.32  Cooper               : 0.00
% 6.52/2.32  Total                : 1.59
% 6.52/2.32  Index Insertion      : 0.00
% 6.52/2.32  Index Deletion       : 0.00
% 6.52/2.32  Index Matching       : 0.00
% 6.52/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
