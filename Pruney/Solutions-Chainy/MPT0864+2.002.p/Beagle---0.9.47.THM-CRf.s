%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:08 EST 2020

% Result     : Theorem 17.92s
% Output     : CNFRefutation 18.15s
% Verified   : 
% Statistics : Number of formulae       :  184 (1347 expanded)
%              Number of leaves         :   45 ( 449 expanded)
%              Depth                    :   20
%              Number of atoms          :  304 (2642 expanded)
%              Number of equality atoms :  220 (2192 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_17 > #skF_6 > #skF_15 > #skF_10 > #skF_4 > #skF_13 > #skF_16 > #skF_12 > #skF_2 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_14 > #skF_3 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_88,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_130,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_104,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_69] : k2_zfmisc_1(A_69,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_367,plain,(
    ! [A_176,B_177,C_178] :
      ( k1_mcart_1(A_176) = B_177
      | ~ r2_hidden(A_176,k2_zfmisc_1(k1_tarski(B_177),C_178)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_381,plain,(
    ! [A_179,B_180] :
      ( k1_mcart_1(A_179) = B_180
      | ~ r2_hidden(A_179,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_367])).

tff(c_420,plain,(
    ! [B_184] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_184)) = '#skF_16'
      | r1_tarski(k1_xboole_0,B_184) ) ),
    inference(resolution,[status(thm)],[c_6,c_381])).

tff(c_388,plain,(
    ! [B_2,B_180] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_2)) = B_180
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_381])).

tff(c_423,plain,(
    ! [B_180,B_184] :
      ( B_180 = '#skF_16'
      | r1_tarski(k1_xboole_0,B_184)
      | r1_tarski(k1_xboole_0,B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_388])).

tff(c_867,plain,(
    ! [B_184] :
      ( r1_tarski(k1_xboole_0,B_184)
      | r1_tarski(k1_xboole_0,B_184) ) ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_876,plain,(
    ! [B_184] : r1_tarski(k1_xboole_0,B_184) ),
    inference(factorization,[status(thm),theory(equality)],[c_867])).

tff(c_118,plain,(
    k4_tarski('#skF_16','#skF_17') = '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_152,plain,(
    ! [A_118,B_119] : k1_mcart_1(k4_tarski(A_118,B_119)) = A_118 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_161,plain,(
    k1_mcart_1('#skF_15') = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_152])).

tff(c_116,plain,
    ( k2_mcart_1('#skF_15') = '#skF_15'
    | k1_mcart_1('#skF_15') = '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_180,plain,
    ( k2_mcart_1('#skF_15') = '#skF_15'
    | '#skF_15' = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_116])).

tff(c_181,plain,(
    '#skF_15' = '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_183,plain,(
    k4_tarski('#skF_16','#skF_17') = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_118])).

tff(c_110,plain,(
    ! [A_99] :
      ( r2_hidden('#skF_14'(A_99),A_99)
      | k1_xboole_0 = A_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_106,plain,(
    ! [A_97,B_98] : k1_mcart_1(k4_tarski(A_97,B_98)) = A_97 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1164,plain,(
    ! [E_3034,F_3035,A_3036,B_3037] :
      ( r2_hidden(k4_tarski(E_3034,F_3035),k2_zfmisc_1(A_3036,B_3037))
      | ~ r2_hidden(F_3035,B_3037)
      | ~ r2_hidden(E_3034,A_3036) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_104,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_mcart_1(A_94) = B_95
      | ~ r2_hidden(A_94,k2_zfmisc_1(k1_tarski(B_95),C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1176,plain,(
    ! [E_3034,F_3035,B_95,B_3037] :
      ( k1_mcart_1(k4_tarski(E_3034,F_3035)) = B_95
      | ~ r2_hidden(F_3035,B_3037)
      | ~ r2_hidden(E_3034,k1_tarski(B_95)) ) ),
    inference(resolution,[status(thm)],[c_1164,c_104])).

tff(c_1196,plain,(
    ! [E_3034,B_95,F_3035,B_3037] :
      ( E_3034 = B_95
      | ~ r2_hidden(F_3035,B_3037)
      | ~ r2_hidden(E_3034,k1_tarski(B_95)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1176])).

tff(c_1201,plain,(
    ! [F_3035,B_3037] : ~ r2_hidden(F_3035,B_3037) ),
    inference(splitLeft,[status(thm)],[c_1196])).

tff(c_18,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1201,c_18])).

tff(c_1220,plain,(
    ! [E_3038,B_3039] :
      ( E_3038 = B_3039
      | ~ r2_hidden(E_3038,k1_tarski(B_3039)) ) ),
    inference(splitRight,[status(thm)],[c_1196])).

tff(c_1235,plain,(
    ! [B_3039] :
      ( '#skF_14'(k1_tarski(B_3039)) = B_3039
      | k1_tarski(B_3039) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_1220])).

tff(c_1271,plain,(
    ! [B_3042] :
      ( '#skF_14'(k1_tarski(B_3042)) = B_3042
      | k1_tarski(B_3042) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_1220])).

tff(c_1538,plain,(
    ! [B_3061] :
      ( r2_hidden(B_3061,k1_tarski(B_3061))
      | k1_tarski(B_3061) = k1_xboole_0
      | k1_tarski(B_3061) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1271,c_110])).

tff(c_112,plain,(
    ! [D_108,A_99,C_107] :
      ( ~ r2_hidden(D_108,A_99)
      | k4_tarski(C_107,D_108) != '#skF_14'(A_99)
      | k1_xboole_0 = A_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1557,plain,(
    ! [C_3062,B_3063] :
      ( k4_tarski(C_3062,B_3063) != '#skF_14'(k1_tarski(B_3063))
      | k1_tarski(B_3063) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1538,c_112])).

tff(c_1722,plain,(
    ! [C_3085,B_3086] :
      ( k4_tarski(C_3085,B_3086) != B_3086
      | k1_tarski(B_3086) = k1_xboole_0
      | k1_tarski(B_3086) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_1557])).

tff(c_1725,plain,
    ( '#skF_17' != '#skF_16'
    | k1_tarski('#skF_17') = k1_xboole_0
    | k1_tarski('#skF_17') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_1722])).

tff(c_1727,plain,(
    '#skF_17' != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_1725])).

tff(c_108,plain,(
    ! [A_97,B_98] : k2_mcart_1(k4_tarski(A_97,B_98)) = B_98 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_100,plain,(
    ! [B_85,C_86,B_87] :
      ( k4_tarski('#skF_12'(k4_tarski(B_85,C_86),B_87),'#skF_13'(k4_tarski(B_85,C_86),B_87)) = k4_tarski(B_85,C_86)
      | k1_mcart_1(k4_tarski(B_85,C_86)) = B_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2223,plain,(
    ! [B_3130,C_3131,B_3132] :
      ( k4_tarski('#skF_12'(k4_tarski(B_3130,C_3131),B_3132),'#skF_13'(k4_tarski(B_3130,C_3131),B_3132)) = k4_tarski(B_3130,C_3131)
      | B_3132 = B_3130 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_100])).

tff(c_2259,plain,(
    ! [B_3130,C_3131,B_3132] :
      ( k2_mcart_1(k4_tarski(B_3130,C_3131)) = '#skF_13'(k4_tarski(B_3130,C_3131),B_3132)
      | B_3132 = B_3130 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2223,c_108])).

tff(c_2286,plain,(
    ! [B_3133,C_3134,B_3135] :
      ( '#skF_13'(k4_tarski(B_3133,C_3134),B_3135) = C_3134
      | B_3135 = B_3133 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2259])).

tff(c_2301,plain,(
    ! [B_3135] :
      ( '#skF_13'('#skF_16',B_3135) = '#skF_17'
      | B_3135 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2286])).

tff(c_339,plain,(
    ! [D_170,B_171,A_172] :
      ( D_170 = B_171
      | D_170 = A_172
      | ~ r2_hidden(D_170,k2_tarski(A_172,B_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_355,plain,(
    ! [A_172,B_171] :
      ( '#skF_14'(k2_tarski(A_172,B_171)) = B_171
      | '#skF_14'(k2_tarski(A_172,B_171)) = A_172
      | k2_tarski(A_172,B_171) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_339])).

tff(c_26764,plain,(
    ! [B_205716] :
      ( k2_tarski(B_205716,B_205716) = k1_xboole_0
      | '#skF_14'(k2_tarski(B_205716,B_205716)) = B_205716 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_355])).

tff(c_2262,plain,(
    ! [B_3130,C_3131,B_3132] :
      ( k1_mcart_1(k4_tarski(B_3130,C_3131)) = '#skF_12'(k4_tarski(B_3130,C_3131),B_3132)
      | B_3132 = B_3130 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2223,c_106])).

tff(c_2315,plain,(
    ! [B_3137,C_3138,B_3139] :
      ( '#skF_12'(k4_tarski(B_3137,C_3138),B_3139) = B_3137
      | B_3139 = B_3137 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2262])).

tff(c_2333,plain,(
    ! [B_3139] :
      ( '#skF_12'('#skF_16',B_3139) = '#skF_16'
      | B_3139 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2315])).

tff(c_2277,plain,(
    ! [B_3132] :
      ( k4_tarski('#skF_12'(k4_tarski('#skF_16','#skF_17'),B_3132),'#skF_13'('#skF_16',B_3132)) = k4_tarski('#skF_16','#skF_17')
      | B_3132 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2223])).

tff(c_2352,plain,(
    ! [B_3141] :
      ( k4_tarski('#skF_12'('#skF_16',B_3141),'#skF_13'('#skF_16',B_3141)) = '#skF_16'
      | B_3141 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_183,c_2277])).

tff(c_2403,plain,(
    ! [B_3139] :
      ( k4_tarski('#skF_16','#skF_13'('#skF_16',B_3139)) = '#skF_16'
      | B_3139 = '#skF_16'
      | B_3139 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2333,c_2352])).

tff(c_42,plain,(
    ! [D_20,B_16] : r2_hidden(D_20,k2_tarski(D_20,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_973,plain,(
    ! [C_2995,A_2996,D_2997] :
      ( ~ r2_hidden(C_2995,A_2996)
      | k4_tarski(C_2995,D_2997) != '#skF_14'(A_2996)
      | k1_xboole_0 = A_2996 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2589,plain,(
    ! [D_3152,D_3153,B_3154] :
      ( k4_tarski(D_3152,D_3153) != '#skF_14'(k2_tarski(D_3152,B_3154))
      | k2_tarski(D_3152,B_3154) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_973])).

tff(c_2592,plain,(
    ! [B_3154,B_3139] :
      ( '#skF_14'(k2_tarski('#skF_16',B_3154)) != '#skF_16'
      | k2_tarski('#skF_16',B_3154) = k1_xboole_0
      | B_3139 = '#skF_16'
      | B_3139 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2403,c_2589])).

tff(c_22692,plain,(
    ! [B_3139] :
      ( B_3139 = '#skF_16'
      | B_3139 = '#skF_16' ) ),
    inference(splitLeft,[status(thm)],[c_2592])).

tff(c_23376,plain,(
    ! [B_174008] : B_174008 = '#skF_16' ),
    inference(factorization,[status(thm),theory(equality)],[c_22692])).

tff(c_2279,plain,(
    ! [B_3130,C_3131,B_3132] :
      ( '#skF_13'(k4_tarski(B_3130,C_3131),B_3132) = C_3131
      | B_3132 = B_3130 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2259])).

tff(c_2671,plain,(
    ! [B_3169,B_3168] :
      ( '#skF_13'('#skF_16',B_3169) = '#skF_13'('#skF_16',B_3168)
      | B_3169 = '#skF_12'('#skF_16',B_3168)
      | B_3168 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_2279])).

tff(c_3332,plain,(
    ! [B_3175] :
      ( '#skF_13'('#skF_16','#skF_17') = '#skF_17'
      | '#skF_12'('#skF_16',B_3175) = '#skF_17'
      | B_3175 = '#skF_16'
      | B_3175 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2301,c_2671])).

tff(c_3335,plain,(
    ! [B_3175] :
      ( '#skF_17' = '#skF_16'
      | B_3175 = '#skF_16'
      | '#skF_13'('#skF_16','#skF_17') = '#skF_17'
      | B_3175 = '#skF_16'
      | B_3175 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3332,c_2333])).

tff(c_4063,plain,(
    ! [B_3175] :
      ( B_3175 = '#skF_16'
      | '#skF_13'('#skF_16','#skF_17') = '#skF_17'
      | B_3175 = '#skF_16'
      | B_3175 = '#skF_16' ) ),
    inference(negUnitSimplification,[status(thm)],[c_1727,c_3335])).

tff(c_4081,plain,(
    '#skF_13'('#skF_16','#skF_17') = '#skF_17' ),
    inference(splitLeft,[status(thm)],[c_4063])).

tff(c_23685,plain,(
    '#skF_17' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_23376,c_4081])).

tff(c_24000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1727,c_23685])).

tff(c_24001,plain,(
    ! [B_3154] :
      ( '#skF_14'(k2_tarski('#skF_16',B_3154)) != '#skF_16'
      | k2_tarski('#skF_16',B_3154) = k1_xboole_0 ) ),
    inference(splitRight,[status(thm)],[c_2592])).

tff(c_27207,plain,(
    k2_tarski('#skF_16','#skF_16') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26764,c_24001])).

tff(c_210,plain,(
    ! [B_123,A_124] :
      ( ~ r1_tarski(B_123,A_124)
      | ~ r2_hidden(A_124,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_222,plain,(
    ! [D_20,B_16] : ~ r1_tarski(k2_tarski(D_20,B_16),D_20) ),
    inference(resolution,[status(thm)],[c_42,c_210])).

tff(c_27265,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_27207,c_222])).

tff(c_27487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_27265])).

tff(c_27489,plain,(
    '#skF_13'('#skF_16','#skF_17') != '#skF_17' ),
    inference(splitRight,[status(thm)],[c_4063])).

tff(c_27504,plain,(
    '#skF_17' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_2301,c_27489])).

tff(c_27510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1727,c_27504])).

tff(c_27512,plain,(
    '#skF_17' = '#skF_16' ),
    inference(splitRight,[status(thm)],[c_1725])).

tff(c_27518,plain,(
    k4_tarski('#skF_16','#skF_16') = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27512,c_183])).

tff(c_68831,plain,(
    ! [B_450635] :
      ( k2_tarski(B_450635,B_450635) = k1_xboole_0
      | '#skF_14'(k2_tarski(B_450635,B_450635)) = B_450635 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_355])).

tff(c_40,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1022,plain,(
    ! [D_3008,A_3009,C_3010] :
      ( ~ r2_hidden(D_3008,A_3009)
      | k4_tarski(C_3010,D_3008) != '#skF_14'(A_3009)
      | k1_xboole_0 = A_3009 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1042,plain,(
    ! [C_3010,D_20,A_15] :
      ( k4_tarski(C_3010,D_20) != '#skF_14'(k2_tarski(A_15,D_20))
      | k2_tarski(A_15,D_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_1022])).

tff(c_69420,plain,(
    ! [C_451727,B_451728] :
      ( k4_tarski(C_451727,B_451728) != B_451728
      | k2_tarski(B_451728,B_451728) = k1_xboole_0
      | k2_tarski(B_451728,B_451728) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68831,c_1042])).

tff(c_69618,plain,(
    k2_tarski('#skF_16','#skF_16') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27518,c_69420])).

tff(c_69668,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_69618,c_222])).

tff(c_69888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_69668])).

tff(c_69890,plain,(
    ! [B_452817] : B_452817 = '#skF_16' ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_235,plain,(
    ! [E_135,A_136,C_137] : r2_hidden(E_135,k1_enumset1(A_136,E_135,C_137)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,(
    ! [B_72,A_71] :
      ( ~ r1_tarski(B_72,A_71)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_239,plain,(
    ! [A_136,E_135,C_137] : ~ r1_tarski(k1_enumset1(A_136,E_135,C_137),E_135) ),
    inference(resolution,[status(thm)],[c_235,c_94])).

tff(c_69967,plain,(
    ! [E_455334] : ~ r1_tarski('#skF_16',E_455334) ),
    inference(superposition,[status(thm),theory(equality)],[c_69890,c_239])).

tff(c_69973,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_69967])).

tff(c_69975,plain,(
    '#skF_15' != '#skF_16' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_69974,plain,(
    k2_mcart_1('#skF_15') = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_168,plain,(
    ! [A_120,B_121] : k2_mcart_1(k4_tarski(A_120,B_121)) = B_121 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_177,plain,(
    k2_mcart_1('#skF_15') = '#skF_17' ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_168])).

tff(c_69981,plain,(
    '#skF_17' = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69974,c_177])).

tff(c_69986,plain,(
    k4_tarski('#skF_16','#skF_15') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69981,c_118])).

tff(c_71861,plain,(
    ! [B_458189,C_458190,B_458191] :
      ( k4_tarski('#skF_12'(k4_tarski(B_458189,C_458190),B_458191),'#skF_13'(k4_tarski(B_458189,C_458190),B_458191)) = k4_tarski(B_458189,C_458190)
      | B_458191 = B_458189 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_100])).

tff(c_71900,plain,(
    ! [B_458189,C_458190,B_458191] :
      ( k2_mcart_1(k4_tarski(B_458189,C_458190)) = '#skF_13'(k4_tarski(B_458189,C_458190),B_458191)
      | B_458191 = B_458189 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71861,c_108])).

tff(c_71927,plain,(
    ! [B_458192,C_458193,B_458194] :
      ( '#skF_13'(k4_tarski(B_458192,C_458193),B_458194) = C_458193
      | B_458194 = B_458192 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_71900])).

tff(c_71942,plain,(
    ! [B_458194] :
      ( '#skF_13'('#skF_15',B_458194) = '#skF_15'
      | B_458194 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69986,c_71927])).

tff(c_70124,plain,(
    ! [A_455516,B_455517,C_455518] :
      ( k1_mcart_1(A_455516) = B_455517
      | ~ r2_hidden(A_455516,k2_zfmisc_1(k1_tarski(B_455517),C_455518)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_70138,plain,(
    ! [A_455519,B_455520] :
      ( k1_mcart_1(A_455519) = B_455520
      | ~ r2_hidden(A_455519,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_70124])).

tff(c_70168,plain,(
    ! [B_455521] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_455521)) = '#skF_17'
      | r1_tarski(k1_xboole_0,B_455521) ) ),
    inference(resolution,[status(thm)],[c_6,c_70138])).

tff(c_70145,plain,(
    ! [B_2,B_455520] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_2)) = B_455520
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_70138])).

tff(c_70171,plain,(
    ! [B_455520,B_455521] :
      ( B_455520 = '#skF_17'
      | r1_tarski(k1_xboole_0,B_455521)
      | r1_tarski(k1_xboole_0,B_455521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70168,c_70145])).

tff(c_70607,plain,(
    ! [B_455520,B_455521] :
      ( B_455520 = '#skF_15'
      | r1_tarski(k1_xboole_0,B_455521)
      | r1_tarski(k1_xboole_0,B_455521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69981,c_70171])).

tff(c_70609,plain,(
    ! [B_455521] :
      ( r1_tarski(k1_xboole_0,B_455521)
      | r1_tarski(k1_xboole_0,B_455521) ) ),
    inference(splitLeft,[status(thm)],[c_70607])).

tff(c_70618,plain,(
    ! [B_455521] : r1_tarski(k1_xboole_0,B_455521) ),
    inference(factorization,[status(thm),theory(equality)],[c_70609])).

tff(c_70103,plain,(
    ! [D_455513,B_455514,A_455515] :
      ( D_455513 = B_455514
      | D_455513 = A_455515
      | ~ r2_hidden(D_455513,k2_tarski(A_455515,B_455514)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70119,plain,(
    ! [A_455515,B_455514] :
      ( '#skF_14'(k2_tarski(A_455515,B_455514)) = B_455514
      | '#skF_14'(k2_tarski(A_455515,B_455514)) = A_455515
      | k2_tarski(A_455515,B_455514) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_70103])).

tff(c_94605,plain,(
    ! [B_648126] :
      ( k2_tarski(B_648126,B_648126) = k1_xboole_0
      | '#skF_14'(k2_tarski(B_648126,B_648126)) = B_648126 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_70119])).

tff(c_71918,plain,(
    ! [B_458191] :
      ( k4_tarski('#skF_12'(k4_tarski('#skF_16','#skF_15'),B_458191),'#skF_13'('#skF_15',B_458191)) = k4_tarski('#skF_16','#skF_15')
      | B_458191 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69986,c_71861])).

tff(c_71993,plain,(
    ! [B_458200] :
      ( k4_tarski('#skF_12'('#skF_15',B_458200),'#skF_13'('#skF_15',B_458200)) = '#skF_15'
      | B_458200 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69986,c_69986,c_71918])).

tff(c_71920,plain,(
    ! [B_458189,C_458190,B_458191] :
      ( '#skF_13'(k4_tarski(B_458189,C_458190),B_458191) = C_458190
      | B_458191 = B_458189 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_71900])).

tff(c_72456,plain,(
    ! [B_458228,B_458227] :
      ( '#skF_13'('#skF_15',B_458228) = '#skF_13'('#skF_15',B_458227)
      | B_458228 = '#skF_12'('#skF_15',B_458227)
      | B_458227 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71993,c_71920])).

tff(c_73132,plain,(
    ! [B_458234] :
      ( '#skF_13'('#skF_15','#skF_17') = '#skF_15'
      | '#skF_12'('#skF_15',B_458234) = '#skF_17'
      | B_458234 = '#skF_16'
      | B_458234 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71942,c_72456])).

tff(c_71903,plain,(
    ! [B_458189,C_458190,B_458191] :
      ( k1_mcart_1(k4_tarski(B_458189,C_458190)) = '#skF_12'(k4_tarski(B_458189,C_458190),B_458191)
      | B_458191 = B_458189 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71861,c_106])).

tff(c_71956,plain,(
    ! [B_458196,C_458197,B_458198] :
      ( '#skF_12'(k4_tarski(B_458196,C_458197),B_458198) = B_458196
      | B_458198 = B_458196 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_71903])).

tff(c_71974,plain,(
    ! [B_458198] :
      ( '#skF_12'('#skF_15',B_458198) = '#skF_16'
      | B_458198 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69986,c_71956])).

tff(c_73135,plain,(
    ! [B_458234] :
      ( '#skF_17' = '#skF_16'
      | B_458234 = '#skF_16'
      | '#skF_13'('#skF_15','#skF_17') = '#skF_15'
      | B_458234 = '#skF_16'
      | B_458234 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73132,c_71974])).

tff(c_73846,plain,(
    ! [B_458234] :
      ( '#skF_15' = '#skF_16'
      | B_458234 = '#skF_16'
      | '#skF_13'('#skF_15','#skF_15') = '#skF_15'
      | B_458234 = '#skF_16'
      | B_458234 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69981,c_69981,c_73135])).

tff(c_73847,plain,(
    ! [B_458234] :
      ( B_458234 = '#skF_16'
      | '#skF_13'('#skF_15','#skF_15') = '#skF_15'
      | B_458234 = '#skF_16'
      | B_458234 = '#skF_16' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69975,c_73846])).

tff(c_73864,plain,(
    '#skF_13'('#skF_15','#skF_15') = '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_73847])).

tff(c_71924,plain,(
    ! [B_458191] :
      ( k4_tarski('#skF_12'('#skF_15',B_458191),'#skF_13'('#skF_15',B_458191)) = '#skF_15'
      | B_458191 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69986,c_69986,c_71918])).

tff(c_73880,plain,
    ( k4_tarski('#skF_12'('#skF_15','#skF_15'),'#skF_15') = '#skF_15'
    | '#skF_15' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_73864,c_71924])).

tff(c_73905,plain,(
    k4_tarski('#skF_12'('#skF_15','#skF_15'),'#skF_15') = '#skF_15' ),
    inference(negUnitSimplification,[status(thm)],[c_69975,c_73880])).

tff(c_70714,plain,(
    ! [D_458054,A_458055,C_458056] :
      ( ~ r2_hidden(D_458054,A_458055)
      | k4_tarski(C_458056,D_458054) != '#skF_14'(A_458055)
      | k1_xboole_0 = A_458055 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_70734,plain,(
    ! [C_458056,D_20,A_15] :
      ( k4_tarski(C_458056,D_20) != '#skF_14'(k2_tarski(A_15,D_20))
      | k2_tarski(A_15,D_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_70714])).

tff(c_73935,plain,(
    ! [A_15] :
      ( '#skF_14'(k2_tarski(A_15,'#skF_15')) != '#skF_15'
      | k2_tarski(A_15,'#skF_15') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73905,c_70734])).

tff(c_95048,plain,(
    k2_tarski('#skF_15','#skF_15') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94605,c_73935])).

tff(c_70006,plain,(
    ! [B_455481,A_455482] :
      ( ~ r1_tarski(B_455481,A_455482)
      | ~ r2_hidden(A_455482,B_455481) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_70030,plain,(
    ! [D_20,B_16] : ~ r1_tarski(k2_tarski(D_20,B_16),D_20) ),
    inference(resolution,[status(thm)],[c_42,c_70006])).

tff(c_95106,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_95048,c_70030])).

tff(c_95331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70618,c_95106])).

tff(c_95333,plain,(
    '#skF_13'('#skF_15','#skF_15') != '#skF_15' ),
    inference(splitRight,[status(thm)],[c_73847])).

tff(c_95348,plain,(
    '#skF_15' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_71942,c_95333])).

tff(c_95354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69975,c_95348])).

tff(c_95356,plain,(
    ! [B_649283] : B_649283 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_70607])).

tff(c_95420,plain,(
    '#skF_15' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_95356,c_161])).

tff(c_95442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69975,c_95420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.92/9.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.92/9.68  
% 17.92/9.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.92/9.68  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_17 > #skF_6 > #skF_15 > #skF_10 > #skF_4 > #skF_13 > #skF_16 > #skF_12 > #skF_2 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_14 > #skF_3 > #skF_8 > #skF_1
% 17.92/9.68  
% 17.92/9.68  %Foreground sorts:
% 17.92/9.68  
% 17.92/9.68  
% 17.92/9.68  %Background operators:
% 17.92/9.68  
% 17.92/9.68  
% 17.92/9.68  %Foreground operators:
% 17.92/9.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.92/9.68  tff('#skF_17', type, '#skF_17': $i).
% 17.92/9.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.92/9.68  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 17.92/9.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.92/9.68  tff('#skF_15', type, '#skF_15': $i).
% 17.92/9.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.92/9.68  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 17.92/9.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.92/9.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_13', type, '#skF_13': ($i * $i) > $i).
% 17.92/9.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.92/9.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_16', type, '#skF_16': $i).
% 17.92/9.68  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 17.92/9.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.92/9.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.92/9.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 17.92/9.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 17.92/9.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.92/9.68  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 17.92/9.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.92/9.68  tff('#skF_14', type, '#skF_14': $i > $i).
% 17.92/9.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.92/9.68  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 17.92/9.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 17.92/9.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.92/9.68  
% 18.15/9.71  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.15/9.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 18.15/9.71  tff(f_88, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 18.15/9.71  tff(f_110, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 18.15/9.71  tff(f_140, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 18.15/9.71  tff(f_114, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 18.15/9.71  tff(f_130, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 18.15/9.71  tff(f_82, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 18.15/9.71  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 18.15/9.71  tff(f_104, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k1_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_mcart_1)).
% 18.15/9.71  tff(f_62, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 18.15/9.71  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 18.15/9.71  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.15/9.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.15/9.71  tff(c_90, plain, (![A_69]: (k2_zfmisc_1(A_69, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.15/9.71  tff(c_367, plain, (![A_176, B_177, C_178]: (k1_mcart_1(A_176)=B_177 | ~r2_hidden(A_176, k2_zfmisc_1(k1_tarski(B_177), C_178)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.15/9.71  tff(c_381, plain, (![A_179, B_180]: (k1_mcart_1(A_179)=B_180 | ~r2_hidden(A_179, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_90, c_367])).
% 18.15/9.71  tff(c_420, plain, (![B_184]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_184))='#skF_16' | r1_tarski(k1_xboole_0, B_184))), inference(resolution, [status(thm)], [c_6, c_381])).
% 18.15/9.71  tff(c_388, plain, (![B_2, B_180]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_2))=B_180 | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_381])).
% 18.15/9.71  tff(c_423, plain, (![B_180, B_184]: (B_180='#skF_16' | r1_tarski(k1_xboole_0, B_184) | r1_tarski(k1_xboole_0, B_184))), inference(superposition, [status(thm), theory('equality')], [c_420, c_388])).
% 18.15/9.71  tff(c_867, plain, (![B_184]: (r1_tarski(k1_xboole_0, B_184) | r1_tarski(k1_xboole_0, B_184))), inference(splitLeft, [status(thm)], [c_423])).
% 18.15/9.71  tff(c_876, plain, (![B_184]: (r1_tarski(k1_xboole_0, B_184))), inference(factorization, [status(thm), theory('equality')], [c_867])).
% 18.15/9.71  tff(c_118, plain, (k4_tarski('#skF_16', '#skF_17')='#skF_15'), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.15/9.71  tff(c_152, plain, (![A_118, B_119]: (k1_mcart_1(k4_tarski(A_118, B_119))=A_118)), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.15/9.71  tff(c_161, plain, (k1_mcart_1('#skF_15')='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_118, c_152])).
% 18.15/9.71  tff(c_116, plain, (k2_mcart_1('#skF_15')='#skF_15' | k1_mcart_1('#skF_15')='#skF_15'), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.15/9.71  tff(c_180, plain, (k2_mcart_1('#skF_15')='#skF_15' | '#skF_15'='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_116])).
% 18.15/9.71  tff(c_181, plain, ('#skF_15'='#skF_16'), inference(splitLeft, [status(thm)], [c_180])).
% 18.15/9.71  tff(c_183, plain, (k4_tarski('#skF_16', '#skF_17')='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_118])).
% 18.15/9.71  tff(c_110, plain, (![A_99]: (r2_hidden('#skF_14'(A_99), A_99) | k1_xboole_0=A_99)), inference(cnfTransformation, [status(thm)], [f_130])).
% 18.15/9.71  tff(c_106, plain, (![A_97, B_98]: (k1_mcart_1(k4_tarski(A_97, B_98))=A_97)), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.15/9.71  tff(c_1164, plain, (![E_3034, F_3035, A_3036, B_3037]: (r2_hidden(k4_tarski(E_3034, F_3035), k2_zfmisc_1(A_3036, B_3037)) | ~r2_hidden(F_3035, B_3037) | ~r2_hidden(E_3034, A_3036))), inference(cnfTransformation, [status(thm)], [f_82])).
% 18.15/9.71  tff(c_104, plain, (![A_94, B_95, C_96]: (k1_mcart_1(A_94)=B_95 | ~r2_hidden(A_94, k2_zfmisc_1(k1_tarski(B_95), C_96)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.15/9.71  tff(c_1176, plain, (![E_3034, F_3035, B_95, B_3037]: (k1_mcart_1(k4_tarski(E_3034, F_3035))=B_95 | ~r2_hidden(F_3035, B_3037) | ~r2_hidden(E_3034, k1_tarski(B_95)))), inference(resolution, [status(thm)], [c_1164, c_104])).
% 18.15/9.71  tff(c_1196, plain, (![E_3034, B_95, F_3035, B_3037]: (E_3034=B_95 | ~r2_hidden(F_3035, B_3037) | ~r2_hidden(E_3034, k1_tarski(B_95)))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1176])).
% 18.15/9.71  tff(c_1201, plain, (![F_3035, B_3037]: (~r2_hidden(F_3035, B_3037))), inference(splitLeft, [status(thm)], [c_1196])).
% 18.15/9.71  tff(c_18, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.15/9.71  tff(c_1218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1201, c_18])).
% 18.15/9.71  tff(c_1220, plain, (![E_3038, B_3039]: (E_3038=B_3039 | ~r2_hidden(E_3038, k1_tarski(B_3039)))), inference(splitRight, [status(thm)], [c_1196])).
% 18.15/9.71  tff(c_1235, plain, (![B_3039]: ('#skF_14'(k1_tarski(B_3039))=B_3039 | k1_tarski(B_3039)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_1220])).
% 18.15/9.71  tff(c_1271, plain, (![B_3042]: ('#skF_14'(k1_tarski(B_3042))=B_3042 | k1_tarski(B_3042)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_1220])).
% 18.15/9.71  tff(c_1538, plain, (![B_3061]: (r2_hidden(B_3061, k1_tarski(B_3061)) | k1_tarski(B_3061)=k1_xboole_0 | k1_tarski(B_3061)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1271, c_110])).
% 18.15/9.71  tff(c_112, plain, (![D_108, A_99, C_107]: (~r2_hidden(D_108, A_99) | k4_tarski(C_107, D_108)!='#skF_14'(A_99) | k1_xboole_0=A_99)), inference(cnfTransformation, [status(thm)], [f_130])).
% 18.15/9.71  tff(c_1557, plain, (![C_3062, B_3063]: (k4_tarski(C_3062, B_3063)!='#skF_14'(k1_tarski(B_3063)) | k1_tarski(B_3063)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1538, c_112])).
% 18.15/9.71  tff(c_1722, plain, (![C_3085, B_3086]: (k4_tarski(C_3085, B_3086)!=B_3086 | k1_tarski(B_3086)=k1_xboole_0 | k1_tarski(B_3086)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1235, c_1557])).
% 18.15/9.71  tff(c_1725, plain, ('#skF_17'!='#skF_16' | k1_tarski('#skF_17')=k1_xboole_0 | k1_tarski('#skF_17')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_183, c_1722])).
% 18.15/9.71  tff(c_1727, plain, ('#skF_17'!='#skF_16'), inference(splitLeft, [status(thm)], [c_1725])).
% 18.15/9.71  tff(c_108, plain, (![A_97, B_98]: (k2_mcart_1(k4_tarski(A_97, B_98))=B_98)), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.15/9.71  tff(c_100, plain, (![B_85, C_86, B_87]: (k4_tarski('#skF_12'(k4_tarski(B_85, C_86), B_87), '#skF_13'(k4_tarski(B_85, C_86), B_87))=k4_tarski(B_85, C_86) | k1_mcart_1(k4_tarski(B_85, C_86))=B_87)), inference(cnfTransformation, [status(thm)], [f_104])).
% 18.15/9.71  tff(c_2223, plain, (![B_3130, C_3131, B_3132]: (k4_tarski('#skF_12'(k4_tarski(B_3130, C_3131), B_3132), '#skF_13'(k4_tarski(B_3130, C_3131), B_3132))=k4_tarski(B_3130, C_3131) | B_3132=B_3130)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_100])).
% 18.15/9.71  tff(c_2259, plain, (![B_3130, C_3131, B_3132]: (k2_mcart_1(k4_tarski(B_3130, C_3131))='#skF_13'(k4_tarski(B_3130, C_3131), B_3132) | B_3132=B_3130)), inference(superposition, [status(thm), theory('equality')], [c_2223, c_108])).
% 18.15/9.71  tff(c_2286, plain, (![B_3133, C_3134, B_3135]: ('#skF_13'(k4_tarski(B_3133, C_3134), B_3135)=C_3134 | B_3135=B_3133)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2259])).
% 18.15/9.71  tff(c_2301, plain, (![B_3135]: ('#skF_13'('#skF_16', B_3135)='#skF_17' | B_3135='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_183, c_2286])).
% 18.15/9.71  tff(c_339, plain, (![D_170, B_171, A_172]: (D_170=B_171 | D_170=A_172 | ~r2_hidden(D_170, k2_tarski(A_172, B_171)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.15/9.71  tff(c_355, plain, (![A_172, B_171]: ('#skF_14'(k2_tarski(A_172, B_171))=B_171 | '#skF_14'(k2_tarski(A_172, B_171))=A_172 | k2_tarski(A_172, B_171)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_339])).
% 18.15/9.71  tff(c_26764, plain, (![B_205716]: (k2_tarski(B_205716, B_205716)=k1_xboole_0 | '#skF_14'(k2_tarski(B_205716, B_205716))=B_205716)), inference(factorization, [status(thm), theory('equality')], [c_355])).
% 18.15/9.71  tff(c_2262, plain, (![B_3130, C_3131, B_3132]: (k1_mcart_1(k4_tarski(B_3130, C_3131))='#skF_12'(k4_tarski(B_3130, C_3131), B_3132) | B_3132=B_3130)), inference(superposition, [status(thm), theory('equality')], [c_2223, c_106])).
% 18.15/9.71  tff(c_2315, plain, (![B_3137, C_3138, B_3139]: ('#skF_12'(k4_tarski(B_3137, C_3138), B_3139)=B_3137 | B_3139=B_3137)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2262])).
% 18.15/9.71  tff(c_2333, plain, (![B_3139]: ('#skF_12'('#skF_16', B_3139)='#skF_16' | B_3139='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_183, c_2315])).
% 18.15/9.71  tff(c_2277, plain, (![B_3132]: (k4_tarski('#skF_12'(k4_tarski('#skF_16', '#skF_17'), B_3132), '#skF_13'('#skF_16', B_3132))=k4_tarski('#skF_16', '#skF_17') | B_3132='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_183, c_2223])).
% 18.15/9.71  tff(c_2352, plain, (![B_3141]: (k4_tarski('#skF_12'('#skF_16', B_3141), '#skF_13'('#skF_16', B_3141))='#skF_16' | B_3141='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_183, c_2277])).
% 18.15/9.71  tff(c_2403, plain, (![B_3139]: (k4_tarski('#skF_16', '#skF_13'('#skF_16', B_3139))='#skF_16' | B_3139='#skF_16' | B_3139='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_2333, c_2352])).
% 18.15/9.71  tff(c_42, plain, (![D_20, B_16]: (r2_hidden(D_20, k2_tarski(D_20, B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.15/9.71  tff(c_973, plain, (![C_2995, A_2996, D_2997]: (~r2_hidden(C_2995, A_2996) | k4_tarski(C_2995, D_2997)!='#skF_14'(A_2996) | k1_xboole_0=A_2996)), inference(cnfTransformation, [status(thm)], [f_130])).
% 18.15/9.71  tff(c_2589, plain, (![D_3152, D_3153, B_3154]: (k4_tarski(D_3152, D_3153)!='#skF_14'(k2_tarski(D_3152, B_3154)) | k2_tarski(D_3152, B_3154)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_973])).
% 18.15/9.71  tff(c_2592, plain, (![B_3154, B_3139]: ('#skF_14'(k2_tarski('#skF_16', B_3154))!='#skF_16' | k2_tarski('#skF_16', B_3154)=k1_xboole_0 | B_3139='#skF_16' | B_3139='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_2403, c_2589])).
% 18.15/9.71  tff(c_22692, plain, (![B_3139]: (B_3139='#skF_16' | B_3139='#skF_16')), inference(splitLeft, [status(thm)], [c_2592])).
% 18.15/9.71  tff(c_23376, plain, (![B_174008]: (B_174008='#skF_16')), inference(factorization, [status(thm), theory('equality')], [c_22692])).
% 18.15/9.71  tff(c_2279, plain, (![B_3130, C_3131, B_3132]: ('#skF_13'(k4_tarski(B_3130, C_3131), B_3132)=C_3131 | B_3132=B_3130)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2259])).
% 18.15/9.71  tff(c_2671, plain, (![B_3169, B_3168]: ('#skF_13'('#skF_16', B_3169)='#skF_13'('#skF_16', B_3168) | B_3169='#skF_12'('#skF_16', B_3168) | B_3168='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_2352, c_2279])).
% 18.15/9.71  tff(c_3332, plain, (![B_3175]: ('#skF_13'('#skF_16', '#skF_17')='#skF_17' | '#skF_12'('#skF_16', B_3175)='#skF_17' | B_3175='#skF_16' | B_3175='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_2301, c_2671])).
% 18.15/9.71  tff(c_3335, plain, (![B_3175]: ('#skF_17'='#skF_16' | B_3175='#skF_16' | '#skF_13'('#skF_16', '#skF_17')='#skF_17' | B_3175='#skF_16' | B_3175='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_3332, c_2333])).
% 18.15/9.71  tff(c_4063, plain, (![B_3175]: (B_3175='#skF_16' | '#skF_13'('#skF_16', '#skF_17')='#skF_17' | B_3175='#skF_16' | B_3175='#skF_16')), inference(negUnitSimplification, [status(thm)], [c_1727, c_3335])).
% 18.15/9.71  tff(c_4081, plain, ('#skF_13'('#skF_16', '#skF_17')='#skF_17'), inference(splitLeft, [status(thm)], [c_4063])).
% 18.15/9.71  tff(c_23685, plain, ('#skF_17'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_23376, c_4081])).
% 18.15/9.71  tff(c_24000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1727, c_23685])).
% 18.15/9.71  tff(c_24001, plain, (![B_3154]: ('#skF_14'(k2_tarski('#skF_16', B_3154))!='#skF_16' | k2_tarski('#skF_16', B_3154)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_2592])).
% 18.15/9.71  tff(c_27207, plain, (k2_tarski('#skF_16', '#skF_16')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26764, c_24001])).
% 18.15/9.71  tff(c_210, plain, (![B_123, A_124]: (~r1_tarski(B_123, A_124) | ~r2_hidden(A_124, B_123))), inference(cnfTransformation, [status(thm)], [f_93])).
% 18.15/9.71  tff(c_222, plain, (![D_20, B_16]: (~r1_tarski(k2_tarski(D_20, B_16), D_20))), inference(resolution, [status(thm)], [c_42, c_210])).
% 18.15/9.71  tff(c_27265, plain, (~r1_tarski(k1_xboole_0, '#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_27207, c_222])).
% 18.15/9.71  tff(c_27487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_876, c_27265])).
% 18.15/9.71  tff(c_27489, plain, ('#skF_13'('#skF_16', '#skF_17')!='#skF_17'), inference(splitRight, [status(thm)], [c_4063])).
% 18.15/9.71  tff(c_27504, plain, ('#skF_17'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_2301, c_27489])).
% 18.15/9.71  tff(c_27510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1727, c_27504])).
% 18.15/9.71  tff(c_27512, plain, ('#skF_17'='#skF_16'), inference(splitRight, [status(thm)], [c_1725])).
% 18.15/9.71  tff(c_27518, plain, (k4_tarski('#skF_16', '#skF_16')='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_27512, c_183])).
% 18.15/9.71  tff(c_68831, plain, (![B_450635]: (k2_tarski(B_450635, B_450635)=k1_xboole_0 | '#skF_14'(k2_tarski(B_450635, B_450635))=B_450635)), inference(factorization, [status(thm), theory('equality')], [c_355])).
% 18.15/9.71  tff(c_40, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.15/9.71  tff(c_1022, plain, (![D_3008, A_3009, C_3010]: (~r2_hidden(D_3008, A_3009) | k4_tarski(C_3010, D_3008)!='#skF_14'(A_3009) | k1_xboole_0=A_3009)), inference(cnfTransformation, [status(thm)], [f_130])).
% 18.15/9.71  tff(c_1042, plain, (![C_3010, D_20, A_15]: (k4_tarski(C_3010, D_20)!='#skF_14'(k2_tarski(A_15, D_20)) | k2_tarski(A_15, D_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_1022])).
% 18.15/9.71  tff(c_69420, plain, (![C_451727, B_451728]: (k4_tarski(C_451727, B_451728)!=B_451728 | k2_tarski(B_451728, B_451728)=k1_xboole_0 | k2_tarski(B_451728, B_451728)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68831, c_1042])).
% 18.15/9.71  tff(c_69618, plain, (k2_tarski('#skF_16', '#skF_16')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_27518, c_69420])).
% 18.15/9.71  tff(c_69668, plain, (~r1_tarski(k1_xboole_0, '#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_69618, c_222])).
% 18.15/9.71  tff(c_69888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_876, c_69668])).
% 18.15/9.71  tff(c_69890, plain, (![B_452817]: (B_452817='#skF_16')), inference(splitRight, [status(thm)], [c_423])).
% 18.15/9.71  tff(c_235, plain, (![E_135, A_136, C_137]: (r2_hidden(E_135, k1_enumset1(A_136, E_135, C_137)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.15/9.71  tff(c_94, plain, (![B_72, A_71]: (~r1_tarski(B_72, A_71) | ~r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_93])).
% 18.15/9.71  tff(c_239, plain, (![A_136, E_135, C_137]: (~r1_tarski(k1_enumset1(A_136, E_135, C_137), E_135))), inference(resolution, [status(thm)], [c_235, c_94])).
% 18.15/9.71  tff(c_69967, plain, (![E_455334]: (~r1_tarski('#skF_16', E_455334))), inference(superposition, [status(thm), theory('equality')], [c_69890, c_239])).
% 18.15/9.71  tff(c_69973, plain, $false, inference(resolution, [status(thm)], [c_12, c_69967])).
% 18.15/9.71  tff(c_69975, plain, ('#skF_15'!='#skF_16'), inference(splitRight, [status(thm)], [c_180])).
% 18.15/9.71  tff(c_69974, plain, (k2_mcart_1('#skF_15')='#skF_15'), inference(splitRight, [status(thm)], [c_180])).
% 18.15/9.71  tff(c_168, plain, (![A_120, B_121]: (k2_mcart_1(k4_tarski(A_120, B_121))=B_121)), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.15/9.71  tff(c_177, plain, (k2_mcart_1('#skF_15')='#skF_17'), inference(superposition, [status(thm), theory('equality')], [c_118, c_168])).
% 18.15/9.71  tff(c_69981, plain, ('#skF_17'='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_69974, c_177])).
% 18.15/9.71  tff(c_69986, plain, (k4_tarski('#skF_16', '#skF_15')='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_69981, c_118])).
% 18.15/9.71  tff(c_71861, plain, (![B_458189, C_458190, B_458191]: (k4_tarski('#skF_12'(k4_tarski(B_458189, C_458190), B_458191), '#skF_13'(k4_tarski(B_458189, C_458190), B_458191))=k4_tarski(B_458189, C_458190) | B_458191=B_458189)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_100])).
% 18.15/9.71  tff(c_71900, plain, (![B_458189, C_458190, B_458191]: (k2_mcart_1(k4_tarski(B_458189, C_458190))='#skF_13'(k4_tarski(B_458189, C_458190), B_458191) | B_458191=B_458189)), inference(superposition, [status(thm), theory('equality')], [c_71861, c_108])).
% 18.15/9.71  tff(c_71927, plain, (![B_458192, C_458193, B_458194]: ('#skF_13'(k4_tarski(B_458192, C_458193), B_458194)=C_458193 | B_458194=B_458192)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_71900])).
% 18.15/9.71  tff(c_71942, plain, (![B_458194]: ('#skF_13'('#skF_15', B_458194)='#skF_15' | B_458194='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_69986, c_71927])).
% 18.15/9.71  tff(c_70124, plain, (![A_455516, B_455517, C_455518]: (k1_mcart_1(A_455516)=B_455517 | ~r2_hidden(A_455516, k2_zfmisc_1(k1_tarski(B_455517), C_455518)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.15/9.71  tff(c_70138, plain, (![A_455519, B_455520]: (k1_mcart_1(A_455519)=B_455520 | ~r2_hidden(A_455519, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_90, c_70124])).
% 18.15/9.71  tff(c_70168, plain, (![B_455521]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_455521))='#skF_17' | r1_tarski(k1_xboole_0, B_455521))), inference(resolution, [status(thm)], [c_6, c_70138])).
% 18.15/9.71  tff(c_70145, plain, (![B_2, B_455520]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_2))=B_455520 | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_70138])).
% 18.15/9.71  tff(c_70171, plain, (![B_455520, B_455521]: (B_455520='#skF_17' | r1_tarski(k1_xboole_0, B_455521) | r1_tarski(k1_xboole_0, B_455521))), inference(superposition, [status(thm), theory('equality')], [c_70168, c_70145])).
% 18.15/9.71  tff(c_70607, plain, (![B_455520, B_455521]: (B_455520='#skF_15' | r1_tarski(k1_xboole_0, B_455521) | r1_tarski(k1_xboole_0, B_455521))), inference(demodulation, [status(thm), theory('equality')], [c_69981, c_70171])).
% 18.15/9.71  tff(c_70609, plain, (![B_455521]: (r1_tarski(k1_xboole_0, B_455521) | r1_tarski(k1_xboole_0, B_455521))), inference(splitLeft, [status(thm)], [c_70607])).
% 18.15/9.71  tff(c_70618, plain, (![B_455521]: (r1_tarski(k1_xboole_0, B_455521))), inference(factorization, [status(thm), theory('equality')], [c_70609])).
% 18.15/9.71  tff(c_70103, plain, (![D_455513, B_455514, A_455515]: (D_455513=B_455514 | D_455513=A_455515 | ~r2_hidden(D_455513, k2_tarski(A_455515, B_455514)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.15/9.71  tff(c_70119, plain, (![A_455515, B_455514]: ('#skF_14'(k2_tarski(A_455515, B_455514))=B_455514 | '#skF_14'(k2_tarski(A_455515, B_455514))=A_455515 | k2_tarski(A_455515, B_455514)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_70103])).
% 18.15/9.71  tff(c_94605, plain, (![B_648126]: (k2_tarski(B_648126, B_648126)=k1_xboole_0 | '#skF_14'(k2_tarski(B_648126, B_648126))=B_648126)), inference(factorization, [status(thm), theory('equality')], [c_70119])).
% 18.15/9.71  tff(c_71918, plain, (![B_458191]: (k4_tarski('#skF_12'(k4_tarski('#skF_16', '#skF_15'), B_458191), '#skF_13'('#skF_15', B_458191))=k4_tarski('#skF_16', '#skF_15') | B_458191='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_69986, c_71861])).
% 18.15/9.71  tff(c_71993, plain, (![B_458200]: (k4_tarski('#skF_12'('#skF_15', B_458200), '#skF_13'('#skF_15', B_458200))='#skF_15' | B_458200='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_69986, c_69986, c_71918])).
% 18.15/9.71  tff(c_71920, plain, (![B_458189, C_458190, B_458191]: ('#skF_13'(k4_tarski(B_458189, C_458190), B_458191)=C_458190 | B_458191=B_458189)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_71900])).
% 18.15/9.71  tff(c_72456, plain, (![B_458228, B_458227]: ('#skF_13'('#skF_15', B_458228)='#skF_13'('#skF_15', B_458227) | B_458228='#skF_12'('#skF_15', B_458227) | B_458227='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_71993, c_71920])).
% 18.15/9.71  tff(c_73132, plain, (![B_458234]: ('#skF_13'('#skF_15', '#skF_17')='#skF_15' | '#skF_12'('#skF_15', B_458234)='#skF_17' | B_458234='#skF_16' | B_458234='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_71942, c_72456])).
% 18.15/9.71  tff(c_71903, plain, (![B_458189, C_458190, B_458191]: (k1_mcart_1(k4_tarski(B_458189, C_458190))='#skF_12'(k4_tarski(B_458189, C_458190), B_458191) | B_458191=B_458189)), inference(superposition, [status(thm), theory('equality')], [c_71861, c_106])).
% 18.15/9.71  tff(c_71956, plain, (![B_458196, C_458197, B_458198]: ('#skF_12'(k4_tarski(B_458196, C_458197), B_458198)=B_458196 | B_458198=B_458196)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_71903])).
% 18.15/9.71  tff(c_71974, plain, (![B_458198]: ('#skF_12'('#skF_15', B_458198)='#skF_16' | B_458198='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_69986, c_71956])).
% 18.15/9.71  tff(c_73135, plain, (![B_458234]: ('#skF_17'='#skF_16' | B_458234='#skF_16' | '#skF_13'('#skF_15', '#skF_17')='#skF_15' | B_458234='#skF_16' | B_458234='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_73132, c_71974])).
% 18.15/9.71  tff(c_73846, plain, (![B_458234]: ('#skF_15'='#skF_16' | B_458234='#skF_16' | '#skF_13'('#skF_15', '#skF_15')='#skF_15' | B_458234='#skF_16' | B_458234='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_69981, c_69981, c_73135])).
% 18.15/9.71  tff(c_73847, plain, (![B_458234]: (B_458234='#skF_16' | '#skF_13'('#skF_15', '#skF_15')='#skF_15' | B_458234='#skF_16' | B_458234='#skF_16')), inference(negUnitSimplification, [status(thm)], [c_69975, c_73846])).
% 18.15/9.71  tff(c_73864, plain, ('#skF_13'('#skF_15', '#skF_15')='#skF_15'), inference(splitLeft, [status(thm)], [c_73847])).
% 18.15/9.71  tff(c_71924, plain, (![B_458191]: (k4_tarski('#skF_12'('#skF_15', B_458191), '#skF_13'('#skF_15', B_458191))='#skF_15' | B_458191='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_69986, c_69986, c_71918])).
% 18.15/9.71  tff(c_73880, plain, (k4_tarski('#skF_12'('#skF_15', '#skF_15'), '#skF_15')='#skF_15' | '#skF_15'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_73864, c_71924])).
% 18.15/9.71  tff(c_73905, plain, (k4_tarski('#skF_12'('#skF_15', '#skF_15'), '#skF_15')='#skF_15'), inference(negUnitSimplification, [status(thm)], [c_69975, c_73880])).
% 18.15/9.71  tff(c_70714, plain, (![D_458054, A_458055, C_458056]: (~r2_hidden(D_458054, A_458055) | k4_tarski(C_458056, D_458054)!='#skF_14'(A_458055) | k1_xboole_0=A_458055)), inference(cnfTransformation, [status(thm)], [f_130])).
% 18.15/9.71  tff(c_70734, plain, (![C_458056, D_20, A_15]: (k4_tarski(C_458056, D_20)!='#skF_14'(k2_tarski(A_15, D_20)) | k2_tarski(A_15, D_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_70714])).
% 18.15/9.71  tff(c_73935, plain, (![A_15]: ('#skF_14'(k2_tarski(A_15, '#skF_15'))!='#skF_15' | k2_tarski(A_15, '#skF_15')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73905, c_70734])).
% 18.15/9.71  tff(c_95048, plain, (k2_tarski('#skF_15', '#skF_15')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94605, c_73935])).
% 18.15/9.71  tff(c_70006, plain, (![B_455481, A_455482]: (~r1_tarski(B_455481, A_455482) | ~r2_hidden(A_455482, B_455481))), inference(cnfTransformation, [status(thm)], [f_93])).
% 18.15/9.71  tff(c_70030, plain, (![D_20, B_16]: (~r1_tarski(k2_tarski(D_20, B_16), D_20))), inference(resolution, [status(thm)], [c_42, c_70006])).
% 18.15/9.71  tff(c_95106, plain, (~r1_tarski(k1_xboole_0, '#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_95048, c_70030])).
% 18.15/9.71  tff(c_95331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70618, c_95106])).
% 18.15/9.71  tff(c_95333, plain, ('#skF_13'('#skF_15', '#skF_15')!='#skF_15'), inference(splitRight, [status(thm)], [c_73847])).
% 18.15/9.71  tff(c_95348, plain, ('#skF_15'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_71942, c_95333])).
% 18.15/9.71  tff(c_95354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69975, c_95348])).
% 18.15/9.71  tff(c_95356, plain, (![B_649283]: (B_649283='#skF_15')), inference(splitRight, [status(thm)], [c_70607])).
% 18.15/9.71  tff(c_95420, plain, ('#skF_15'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_95356, c_161])).
% 18.15/9.71  tff(c_95442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69975, c_95420])).
% 18.15/9.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.15/9.71  
% 18.15/9.71  Inference rules
% 18.15/9.71  ----------------------
% 18.15/9.71  #Ref     : 11
% 18.15/9.71  #Sup     : 16105
% 18.15/9.71  #Fact    : 115
% 18.15/9.71  #Define  : 0
% 18.15/9.71  #Split   : 33
% 18.15/9.71  #Chain   : 0
% 18.15/9.71  #Close   : 0
% 18.15/9.71  
% 18.15/9.71  Ordering : KBO
% 18.15/9.71  
% 18.15/9.71  Simplification rules
% 18.15/9.71  ----------------------
% 18.15/9.71  #Subsume      : 4102
% 18.15/9.71  #Demod        : 3480
% 18.15/9.71  #Tautology    : 2400
% 18.15/9.71  #SimpNegUnit  : 467
% 18.15/9.71  #BackRed      : 113
% 18.15/9.71  
% 18.15/9.71  #Partial instantiations: 172346
% 18.15/9.71  #Strategies tried      : 1
% 18.15/9.71  
% 18.15/9.71  Timing (in seconds)
% 18.15/9.71  ----------------------
% 18.15/9.71  Preprocessing        : 0.38
% 18.15/9.71  Parsing              : 0.19
% 18.15/9.71  CNF conversion       : 0.04
% 18.15/9.71  Main loop            : 8.53
% 18.15/9.71  Inferencing          : 4.25
% 18.15/9.72  Reduction            : 1.52
% 18.15/9.72  Demodulation         : 1.01
% 18.15/9.72  BG Simplification    : 0.24
% 18.15/9.72  Subsumption          : 2.05
% 18.15/9.72  Abstraction          : 0.32
% 18.15/9.72  MUC search           : 0.00
% 18.15/9.72  Cooper               : 0.00
% 18.15/9.72  Total                : 8.97
% 18.15/9.72  Index Insertion      : 0.00
% 18.15/9.72  Index Deletion       : 0.00
% 18.15/9.72  Index Matching       : 0.00
% 18.15/9.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
