%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:08 EST 2020

% Result     : Theorem 18.33s
% Output     : CNFRefutation 18.47s
% Verified   : 
% Statistics : Number of formulae       :  184 (1461 expanded)
%              Number of leaves         :   44 ( 485 expanded)
%              Depth                    :   20
%              Number of atoms          :  300 (2810 expanded)
%              Number of equality atoms :  217 (2360 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_17 > #skF_6 > #skF_15 > #skF_10 > #skF_4 > #skF_13 > #skF_16 > #skF_12 > #skF_2 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_14 > #skF_3 > #skF_8 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_92,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_134,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_108,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_97,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_68] : k2_zfmisc_1(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_357,plain,(
    ! [A_169,B_170,C_171] :
      ( k1_mcart_1(A_169) = B_170
      | ~ r2_hidden(A_169,k2_zfmisc_1(k1_tarski(B_170),C_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_371,plain,(
    ! [A_172,B_173] :
      ( k1_mcart_1(A_172) = B_173
      | ~ r2_hidden(A_172,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_357])).

tff(c_439,plain,(
    ! [B_183] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_183)) = '#skF_17'
      | r1_tarski(k1_xboole_0,B_183) ) ),
    inference(resolution,[status(thm)],[c_6,c_371])).

tff(c_378,plain,(
    ! [B_2,B_173] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_2)) = B_173
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_371])).

tff(c_442,plain,(
    ! [B_173,B_183] :
      ( B_173 = '#skF_17'
      | r1_tarski(k1_xboole_0,B_183)
      | r1_tarski(k1_xboole_0,B_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_378])).

tff(c_857,plain,(
    ! [B_183] :
      ( r1_tarski(k1_xboole_0,B_183)
      | r1_tarski(k1_xboole_0,B_183) ) ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_866,plain,(
    ! [B_183] : r1_tarski(k1_xboole_0,B_183) ),
    inference(factorization,[status(thm),theory(equality)],[c_857])).

tff(c_122,plain,(
    k4_tarski('#skF_16','#skF_17') = '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_156,plain,(
    ! [A_117,B_118] : k1_mcart_1(k4_tarski(A_117,B_118)) = A_117 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_165,plain,(
    k1_mcart_1('#skF_15') = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_156])).

tff(c_120,plain,
    ( k2_mcart_1('#skF_15') = '#skF_15'
    | k1_mcart_1('#skF_15') = '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_184,plain,
    ( k2_mcart_1('#skF_15') = '#skF_15'
    | '#skF_15' = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_120])).

tff(c_185,plain,(
    '#skF_15' = '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_187,plain,(
    k4_tarski('#skF_16','#skF_17') = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_122])).

tff(c_114,plain,(
    ! [A_98] :
      ( r2_hidden('#skF_14'(A_98),A_98)
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_110,plain,(
    ! [A_96,B_97] : k1_mcart_1(k4_tarski(A_96,B_97)) = A_96 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1184,plain,(
    ! [A_2794,B_2795,C_2796,D_2797] :
      ( r2_hidden(k4_tarski(A_2794,B_2795),k2_zfmisc_1(C_2796,D_2797))
      | ~ r2_hidden(B_2795,D_2797)
      | ~ r2_hidden(A_2794,C_2796) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_108,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_mcart_1(A_93) = B_94
      | ~ r2_hidden(A_93,k2_zfmisc_1(k1_tarski(B_94),C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1202,plain,(
    ! [A_2794,B_2795,B_94,D_2797] :
      ( k1_mcart_1(k4_tarski(A_2794,B_2795)) = B_94
      | ~ r2_hidden(B_2795,D_2797)
      | ~ r2_hidden(A_2794,k1_tarski(B_94)) ) ),
    inference(resolution,[status(thm)],[c_1184,c_108])).

tff(c_1224,plain,(
    ! [B_94,A_2794,B_2795,D_2797] :
      ( B_94 = A_2794
      | ~ r2_hidden(B_2795,D_2797)
      | ~ r2_hidden(A_2794,k1_tarski(B_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1202])).

tff(c_1229,plain,(
    ! [B_2795,D_2797] : ~ r2_hidden(B_2795,D_2797) ),
    inference(splitLeft,[status(thm)],[c_1224])).

tff(c_18,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1229,c_18])).

tff(c_1252,plain,(
    ! [B_2798,A_2799] :
      ( B_2798 = A_2799
      | ~ r2_hidden(A_2799,k1_tarski(B_2798)) ) ),
    inference(splitRight,[status(thm)],[c_1224])).

tff(c_1267,plain,(
    ! [B_2798] :
      ( '#skF_14'(k1_tarski(B_2798)) = B_2798
      | k1_tarski(B_2798) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_114,c_1252])).

tff(c_1311,plain,(
    ! [B_2802] :
      ( '#skF_14'(k1_tarski(B_2802)) = B_2802
      | k1_tarski(B_2802) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_114,c_1252])).

tff(c_1579,plain,(
    ! [B_2821] :
      ( r2_hidden(B_2821,k1_tarski(B_2821))
      | k1_tarski(B_2821) = k1_xboole_0
      | k1_tarski(B_2821) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_114])).

tff(c_116,plain,(
    ! [D_107,A_98,C_106] :
      ( ~ r2_hidden(D_107,A_98)
      | k4_tarski(C_106,D_107) != '#skF_14'(A_98)
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1602,plain,(
    ! [C_2824,B_2825] :
      ( k4_tarski(C_2824,B_2825) != '#skF_14'(k1_tarski(B_2825))
      | k1_tarski(B_2825) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1579,c_116])).

tff(c_1980,plain,(
    ! [C_2857,B_2858] :
      ( k4_tarski(C_2857,B_2858) != B_2858
      | k1_tarski(B_2858) = k1_xboole_0
      | k1_tarski(B_2858) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1267,c_1602])).

tff(c_1983,plain,
    ( '#skF_17' != '#skF_16'
    | k1_tarski('#skF_17') = k1_xboole_0
    | k1_tarski('#skF_17') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_1980])).

tff(c_1984,plain,(
    '#skF_17' != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_1983])).

tff(c_104,plain,(
    ! [B_84,C_85,B_86] :
      ( k4_tarski('#skF_12'(k4_tarski(B_84,C_85),B_86),'#skF_13'(k4_tarski(B_84,C_85),B_86)) = k4_tarski(B_84,C_85)
      | k1_mcart_1(k4_tarski(B_84,C_85)) = B_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2128,plain,(
    ! [B_2883,C_2884,B_2885] :
      ( k4_tarski('#skF_12'(k4_tarski(B_2883,C_2884),B_2885),'#skF_13'(k4_tarski(B_2883,C_2884),B_2885)) = k4_tarski(B_2883,C_2884)
      | B_2885 = B_2883 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_104])).

tff(c_2173,plain,(
    ! [B_2883,C_2884,B_2885] :
      ( k1_mcart_1(k4_tarski(B_2883,C_2884)) = '#skF_12'(k4_tarski(B_2883,C_2884),B_2885)
      | B_2885 = B_2883 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_110])).

tff(c_2226,plain,(
    ! [B_2890,C_2891,B_2892] :
      ( '#skF_12'(k4_tarski(B_2890,C_2891),B_2892) = B_2890
      | B_2892 = B_2890 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2173])).

tff(c_2244,plain,(
    ! [B_2892] :
      ( '#skF_12'('#skF_16',B_2892) = '#skF_16'
      | B_2892 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_2226])).

tff(c_314,plain,(
    ! [D_163,B_164,A_165] :
      ( D_163 = B_164
      | D_163 = A_165
      | ~ r2_hidden(D_163,k2_tarski(A_165,B_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_330,plain,(
    ! [A_165,B_164] :
      ( '#skF_14'(k2_tarski(A_165,B_164)) = B_164
      | '#skF_14'(k2_tarski(A_165,B_164)) = A_165
      | k2_tarski(A_165,B_164) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_114,c_314])).

tff(c_28417,plain,(
    ! [B_202271] :
      ( k2_tarski(B_202271,B_202271) = k1_xboole_0
      | '#skF_14'(k2_tarski(B_202271,B_202271)) = B_202271 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_330])).

tff(c_2188,plain,(
    ! [B_2885] :
      ( k4_tarski('#skF_12'(k4_tarski('#skF_16','#skF_17'),B_2885),'#skF_13'('#skF_16',B_2885)) = k4_tarski('#skF_16','#skF_17')
      | B_2885 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_2128])).

tff(c_2263,plain,(
    ! [B_2894] :
      ( k4_tarski('#skF_12'('#skF_16',B_2894),'#skF_13'('#skF_16',B_2894)) = '#skF_16'
      | B_2894 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_187,c_2188])).

tff(c_2191,plain,(
    ! [B_2883,C_2884,B_2885] :
      ( '#skF_12'(k4_tarski(B_2883,C_2884),B_2885) = B_2883
      | B_2885 = B_2883 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2173])).

tff(c_2885,plain,(
    ! [B_2948,B_2947] :
      ( '#skF_12'('#skF_16',B_2948) = '#skF_12'('#skF_16',B_2947)
      | B_2948 = '#skF_12'('#skF_16',B_2947)
      | B_2947 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2263,c_2191])).

tff(c_6364,plain,(
    ! [B_19715] :
      ( '#skF_12'('#skF_16','#skF_17') = '#skF_16'
      | B_19715 = '#skF_16'
      | '#skF_12'('#skF_16',B_19715) = '#skF_17'
      | B_19715 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2885,c_2244])).

tff(c_6367,plain,(
    ! [B_19715] :
      ( '#skF_17' = '#skF_16'
      | B_19715 = '#skF_16'
      | '#skF_12'('#skF_16','#skF_17') = '#skF_16'
      | B_19715 = '#skF_16'
      | B_19715 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6364,c_2244])).

tff(c_7147,plain,(
    ! [B_19715] :
      ( B_19715 = '#skF_16'
      | '#skF_12'('#skF_16','#skF_17') = '#skF_16'
      | B_19715 = '#skF_16'
      | B_19715 = '#skF_16' ) ),
    inference(negUnitSimplification,[status(thm)],[c_1984,c_6367])).

tff(c_7181,plain,(
    '#skF_12'('#skF_16','#skF_17') = '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_7147])).

tff(c_2194,plain,(
    ! [B_2885] :
      ( k4_tarski('#skF_12'('#skF_16',B_2885),'#skF_13'('#skF_16',B_2885)) = '#skF_16'
      | B_2885 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_187,c_2188])).

tff(c_7213,plain,
    ( k4_tarski('#skF_16','#skF_13'('#skF_16','#skF_17')) = '#skF_16'
    | '#skF_17' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_7181,c_2194])).

tff(c_7296,plain,(
    k4_tarski('#skF_16','#skF_13'('#skF_16','#skF_17')) = '#skF_16' ),
    inference(negUnitSimplification,[status(thm)],[c_1984,c_7213])).

tff(c_42,plain,(
    ! [D_20,B_16] : r2_hidden(D_20,k2_tarski(D_20,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_994,plain,(
    ! [C_2753,A_2754,D_2755] :
      ( ~ r2_hidden(C_2753,A_2754)
      | k4_tarski(C_2753,D_2755) != '#skF_14'(A_2754)
      | k1_xboole_0 = A_2754 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1015,plain,(
    ! [D_20,D_2755,B_16] :
      ( k4_tarski(D_20,D_2755) != '#skF_14'(k2_tarski(D_20,B_16))
      | k2_tarski(D_20,B_16) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_994])).

tff(c_7315,plain,(
    ! [B_16] :
      ( '#skF_14'(k2_tarski('#skF_16',B_16)) != '#skF_16'
      | k2_tarski('#skF_16',B_16) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7296,c_1015])).

tff(c_28849,plain,(
    k2_tarski('#skF_16','#skF_16') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28417,c_7315])).

tff(c_215,plain,(
    ! [B_125,A_126] :
      ( ~ r1_tarski(B_125,A_126)
      | ~ r2_hidden(A_126,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_231,plain,(
    ! [D_20,B_16] : ~ r1_tarski(k2_tarski(D_20,B_16),D_20) ),
    inference(resolution,[status(thm)],[c_42,c_215])).

tff(c_28907,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_28849,c_231])).

tff(c_29129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_28907])).

tff(c_29131,plain,(
    '#skF_12'('#skF_16','#skF_17') != '#skF_16' ),
    inference(splitRight,[status(thm)],[c_7147])).

tff(c_29149,plain,(
    '#skF_17' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_29131])).

tff(c_29156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1984,c_29149])).

tff(c_29158,plain,(
    '#skF_17' = '#skF_16' ),
    inference(splitRight,[status(thm)],[c_1983])).

tff(c_29165,plain,(
    k4_tarski('#skF_16','#skF_16') = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29158,c_187])).

tff(c_68295,plain,(
    ! [B_497491] :
      ( k2_tarski(B_497491,B_497491) = k1_xboole_0
      | '#skF_14'(k2_tarski(B_497491,B_497491)) = B_497491 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_330])).

tff(c_40,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1014,plain,(
    ! [D_20,D_2755,A_15] :
      ( k4_tarski(D_20,D_2755) != '#skF_14'(k2_tarski(A_15,D_20))
      | k2_tarski(A_15,D_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_994])).

tff(c_68624,plain,(
    ! [B_497926,D_497927] :
      ( k4_tarski(B_497926,D_497927) != B_497926
      | k2_tarski(B_497926,B_497926) = k1_xboole_0
      | k2_tarski(B_497926,B_497926) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68295,c_1014])).

tff(c_68761,plain,(
    k2_tarski('#skF_16','#skF_16') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_29165,c_68624])).

tff(c_68808,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_68761,c_231])).

tff(c_68963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_68808])).

tff(c_68965,plain,(
    ! [B_498796] : B_498796 = '#skF_17' ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_234,plain,(
    ! [E_131,A_132,B_133] : r2_hidden(E_131,k1_enumset1(A_132,B_133,E_131)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_98,plain,(
    ! [B_71,A_70] :
      ( ~ r1_tarski(B_71,A_70)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_238,plain,(
    ! [A_132,B_133,E_131] : ~ r1_tarski(k1_enumset1(A_132,B_133,E_131),E_131) ),
    inference(resolution,[status(thm)],[c_234,c_98])).

tff(c_69257,plain,(
    ! [E_506552] : ~ r1_tarski('#skF_17',E_506552) ),
    inference(superposition,[status(thm),theory(equality)],[c_68965,c_238])).

tff(c_69267,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_69257])).

tff(c_69269,plain,(
    '#skF_15' != '#skF_16' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_69268,plain,(
    k2_mcart_1('#skF_15') = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_172,plain,(
    ! [A_119,B_120] : k2_mcart_1(k4_tarski(A_119,B_120)) = B_120 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_181,plain,(
    k2_mcart_1('#skF_15') = '#skF_17' ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_172])).

tff(c_69274,plain,(
    '#skF_17' = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69268,c_181])).

tff(c_69279,plain,(
    k4_tarski('#skF_16','#skF_15') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69274,c_122])).

tff(c_71479,plain,(
    ! [B_509579,C_509580,B_509581] :
      ( k4_tarski('#skF_12'(k4_tarski(B_509579,C_509580),B_509581),'#skF_13'(k4_tarski(B_509579,C_509580),B_509581)) = k4_tarski(B_509579,C_509580)
      | B_509581 = B_509579 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_104])).

tff(c_71530,plain,(
    ! [B_509579,C_509580,B_509581] :
      ( k1_mcart_1(k4_tarski(B_509579,C_509580)) = '#skF_12'(k4_tarski(B_509579,C_509580),B_509581)
      | B_509581 = B_509579 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71479,c_110])).

tff(c_71583,plain,(
    ! [B_509586,C_509587,B_509588] :
      ( '#skF_12'(k4_tarski(B_509586,C_509587),B_509588) = B_509586
      | B_509588 = B_509586 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_71530])).

tff(c_71601,plain,(
    ! [B_509588] :
      ( '#skF_12'('#skF_15',B_509588) = '#skF_16'
      | B_509588 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69279,c_71583])).

tff(c_69418,plain,(
    ! [A_506846,B_506847,C_506848] :
      ( k1_mcart_1(A_506846) = B_506847
      | ~ r2_hidden(A_506846,k2_zfmisc_1(k1_tarski(B_506847),C_506848)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_69454,plain,(
    ! [A_506852,B_506853] :
      ( k1_mcart_1(A_506852) = B_506853
      | ~ r2_hidden(A_506852,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_69418])).

tff(c_69492,plain,(
    ! [B_506863] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_506863)) = '#skF_17'
      | r1_tarski(k1_xboole_0,B_506863) ) ),
    inference(resolution,[status(thm)],[c_6,c_69454])).

tff(c_69461,plain,(
    ! [B_2,B_506853] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_2)) = B_506853
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_69454])).

tff(c_69495,plain,(
    ! [B_506853,B_506863] :
      ( B_506853 = '#skF_17'
      | r1_tarski(k1_xboole_0,B_506863)
      | r1_tarski(k1_xboole_0,B_506863) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69492,c_69461])).

tff(c_69938,plain,(
    ! [B_506853,B_506863] :
      ( B_506853 = '#skF_15'
      | r1_tarski(k1_xboole_0,B_506863)
      | r1_tarski(k1_xboole_0,B_506863) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69274,c_69495])).

tff(c_69940,plain,(
    ! [B_506863] :
      ( r1_tarski(k1_xboole_0,B_506863)
      | r1_tarski(k1_xboole_0,B_506863) ) ),
    inference(splitLeft,[status(thm)],[c_69938])).

tff(c_69949,plain,(
    ! [B_506863] : r1_tarski(k1_xboole_0,B_506863) ),
    inference(factorization,[status(thm),theory(equality)],[c_69940])).

tff(c_69397,plain,(
    ! [D_506843,B_506844,A_506845] :
      ( D_506843 = B_506844
      | D_506843 = A_506845
      | ~ r2_hidden(D_506843,k2_tarski(A_506845,B_506844)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69413,plain,(
    ! [A_506845,B_506844] :
      ( '#skF_14'(k2_tarski(A_506845,B_506844)) = B_506844
      | '#skF_14'(k2_tarski(A_506845,B_506844)) = A_506845
      | k2_tarski(A_506845,B_506844) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_114,c_69397])).

tff(c_102833,plain,(
    ! [B_766901] :
      ( k2_tarski(B_766901,B_766901) = k1_xboole_0
      | '#skF_14'(k2_tarski(B_766901,B_766901)) = B_766901 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_69413])).

tff(c_112,plain,(
    ! [A_96,B_97] : k2_mcart_1(k4_tarski(A_96,B_97)) = B_97 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_71527,plain,(
    ! [B_509579,C_509580,B_509581] :
      ( k2_mcart_1(k4_tarski(B_509579,C_509580)) = '#skF_13'(k4_tarski(B_509579,C_509580),B_509581)
      | B_509581 = B_509579 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71479,c_112])).

tff(c_71554,plain,(
    ! [B_509582,C_509583,B_509584] :
      ( '#skF_13'(k4_tarski(B_509582,C_509583),B_509584) = C_509583
      | B_509584 = B_509582 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_71527])).

tff(c_71569,plain,(
    ! [B_509584] :
      ( '#skF_13'('#skF_15',B_509584) = '#skF_15'
      | B_509584 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69279,c_71554])).

tff(c_71545,plain,(
    ! [B_509581] :
      ( k4_tarski('#skF_12'(k4_tarski('#skF_16','#skF_15'),B_509581),'#skF_13'('#skF_15',B_509581)) = k4_tarski('#skF_16','#skF_15')
      | B_509581 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69279,c_71479])).

tff(c_71620,plain,(
    ! [B_509590] :
      ( k4_tarski('#skF_12'('#skF_15',B_509590),'#skF_13'('#skF_15',B_509590)) = '#skF_15'
      | B_509590 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69279,c_69279,c_71545])).

tff(c_71758,plain,(
    ! [B_509594] :
      ( k4_tarski('#skF_12'('#skF_15',B_509594),'#skF_15') = '#skF_15'
      | B_509594 = '#skF_16'
      | B_509594 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71569,c_71620])).

tff(c_69979,plain,(
    ! [D_509409,A_509410,C_509411] :
      ( ~ r2_hidden(D_509409,A_509410)
      | k4_tarski(C_509411,D_509409) != '#skF_14'(A_509410)
      | k1_xboole_0 = A_509410 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_69999,plain,(
    ! [C_509411,D_20,A_15] :
      ( k4_tarski(C_509411,D_20) != '#skF_14'(k2_tarski(A_15,D_20))
      | k2_tarski(A_15,D_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_69979])).

tff(c_71776,plain,(
    ! [A_15,B_509594] :
      ( '#skF_14'(k2_tarski(A_15,'#skF_15')) != '#skF_15'
      | k2_tarski(A_15,'#skF_15') = k1_xboole_0
      | B_509594 = '#skF_16'
      | B_509594 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71758,c_69999])).

tff(c_92868,plain,(
    ! [B_509594] :
      ( B_509594 = '#skF_16'
      | B_509594 = '#skF_16' ) ),
    inference(splitLeft,[status(thm)],[c_71776])).

tff(c_93779,plain,(
    ! [B_682523] : B_682523 = '#skF_16' ),
    inference(factorization,[status(thm),theory(equality)],[c_92868])).

tff(c_71548,plain,(
    ! [B_509579,C_509580,B_509581] :
      ( '#skF_12'(k4_tarski(B_509579,C_509580),B_509581) = B_509579
      | B_509581 = B_509579 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_71530])).

tff(c_74192,plain,(
    ! [B_527327,B_527326] :
      ( '#skF_12'('#skF_15',B_527327) = '#skF_12'('#skF_15',B_527326)
      | B_527327 = '#skF_12'('#skF_15',B_527326)
      | B_527326 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71620,c_71548])).

tff(c_76294,plain,(
    ! [B_529354] :
      ( '#skF_12'('#skF_15','#skF_17') = '#skF_16'
      | '#skF_12'('#skF_15',B_529354) = '#skF_17'
      | B_529354 = '#skF_16'
      | B_529354 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71601,c_74192])).

tff(c_76297,plain,(
    ! [B_529354] :
      ( '#skF_17' = '#skF_16'
      | B_529354 = '#skF_16'
      | '#skF_12'('#skF_15','#skF_17') = '#skF_16'
      | B_529354 = '#skF_16'
      | B_529354 = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76294,c_71601])).

tff(c_77196,plain,(
    ! [B_529354] :
      ( '#skF_15' = '#skF_16'
      | B_529354 = '#skF_16'
      | '#skF_12'('#skF_15','#skF_15') = '#skF_16'
      | B_529354 = '#skF_16'
      | B_529354 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69274,c_69274,c_76297])).

tff(c_77197,plain,(
    ! [B_529354] :
      ( B_529354 = '#skF_16'
      | '#skF_12'('#skF_15','#skF_15') = '#skF_16'
      | B_529354 = '#skF_16'
      | B_529354 = '#skF_16' ) ),
    inference(negUnitSimplification,[status(thm)],[c_69269,c_77196])).

tff(c_77217,plain,(
    '#skF_12'('#skF_15','#skF_15') = '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_77197])).

tff(c_71551,plain,(
    ! [B_509581] :
      ( k4_tarski('#skF_12'('#skF_15',B_509581),'#skF_13'('#skF_15',B_509581)) = '#skF_15'
      | B_509581 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69279,c_69279,c_71545])).

tff(c_77249,plain,
    ( k4_tarski('#skF_16','#skF_13'('#skF_15','#skF_15')) = '#skF_15'
    | '#skF_15' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_77217,c_71551])).

tff(c_77329,plain,(
    k4_tarski('#skF_16','#skF_13'('#skF_15','#skF_15')) = '#skF_15' ),
    inference(negUnitSimplification,[status(thm)],[c_69269,c_77249])).

tff(c_77390,plain,(
    k2_mcart_1('#skF_15') = '#skF_13'('#skF_15','#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_77329,c_112])).

tff(c_77420,plain,(
    '#skF_13'('#skF_15','#skF_15') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69268,c_77390])).

tff(c_94025,plain,(
    '#skF_15' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_93779,c_77420])).

tff(c_94464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69269,c_94025])).

tff(c_94465,plain,(
    ! [A_15] :
      ( '#skF_14'(k2_tarski(A_15,'#skF_15')) != '#skF_15'
      | k2_tarski(A_15,'#skF_15') = k1_xboole_0 ) ),
    inference(splitRight,[status(thm)],[c_71776])).

tff(c_103265,plain,(
    k2_tarski('#skF_15','#skF_15') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102833,c_94465])).

tff(c_69299,plain,(
    ! [B_506808,A_506809] :
      ( ~ r1_tarski(B_506808,A_506809)
      | ~ r2_hidden(A_506809,B_506808) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_69319,plain,(
    ! [D_20,B_16] : ~ r1_tarski(k2_tarski(D_20,B_16),D_20) ),
    inference(resolution,[status(thm)],[c_42,c_69299])).

tff(c_103323,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_103265,c_69319])).

tff(c_103545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69949,c_103323])).

tff(c_103547,plain,(
    '#skF_12'('#skF_15','#skF_15') != '#skF_16' ),
    inference(splitRight,[status(thm)],[c_77197])).

tff(c_103565,plain,(
    '#skF_15' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_71601,c_103547])).

tff(c_103572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69269,c_103565])).

tff(c_103587,plain,(
    ! [B_768144] : B_768144 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_69938])).

tff(c_103663,plain,(
    '#skF_15' = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_103587,c_165])).

tff(c_103686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69269,c_103663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.33/10.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.33/10.26  
% 18.33/10.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.33/10.26  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_17 > #skF_6 > #skF_15 > #skF_10 > #skF_4 > #skF_13 > #skF_16 > #skF_12 > #skF_2 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_14 > #skF_3 > #skF_8 > #skF_1
% 18.33/10.26  
% 18.33/10.26  %Foreground sorts:
% 18.33/10.26  
% 18.33/10.26  
% 18.33/10.26  %Background operators:
% 18.33/10.26  
% 18.33/10.26  
% 18.33/10.26  %Foreground operators:
% 18.33/10.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.33/10.26  tff('#skF_17', type, '#skF_17': $i).
% 18.33/10.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.33/10.26  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 18.33/10.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.33/10.26  tff('#skF_15', type, '#skF_15': $i).
% 18.33/10.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 18.33/10.26  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 18.33/10.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.33/10.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_13', type, '#skF_13': ($i * $i) > $i).
% 18.33/10.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.33/10.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_16', type, '#skF_16': $i).
% 18.33/10.26  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 18.33/10.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.33/10.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 18.33/10.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 18.33/10.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.33/10.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 18.33/10.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.33/10.26  tff('#skF_14', type, '#skF_14': $i > $i).
% 18.33/10.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.33/10.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 18.33/10.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 18.33/10.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.33/10.26  
% 18.47/10.29  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.47/10.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 18.47/10.29  tff(f_92, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 18.47/10.29  tff(f_114, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 18.47/10.29  tff(f_144, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 18.47/10.29  tff(f_118, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 18.47/10.29  tff(f_134, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 18.47/10.29  tff(f_86, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 18.47/10.29  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 18.47/10.29  tff(f_108, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k1_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_mcart_1)).
% 18.47/10.29  tff(f_62, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 18.47/10.29  tff(f_97, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 18.47/10.29  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.47/10.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.47/10.29  tff(c_94, plain, (![A_68]: (k2_zfmisc_1(A_68, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_92])).
% 18.47/10.29  tff(c_357, plain, (![A_169, B_170, C_171]: (k1_mcart_1(A_169)=B_170 | ~r2_hidden(A_169, k2_zfmisc_1(k1_tarski(B_170), C_171)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.47/10.29  tff(c_371, plain, (![A_172, B_173]: (k1_mcart_1(A_172)=B_173 | ~r2_hidden(A_172, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_94, c_357])).
% 18.47/10.29  tff(c_439, plain, (![B_183]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_183))='#skF_17' | r1_tarski(k1_xboole_0, B_183))), inference(resolution, [status(thm)], [c_6, c_371])).
% 18.47/10.29  tff(c_378, plain, (![B_2, B_173]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_2))=B_173 | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_371])).
% 18.47/10.29  tff(c_442, plain, (![B_173, B_183]: (B_173='#skF_17' | r1_tarski(k1_xboole_0, B_183) | r1_tarski(k1_xboole_0, B_183))), inference(superposition, [status(thm), theory('equality')], [c_439, c_378])).
% 18.47/10.29  tff(c_857, plain, (![B_183]: (r1_tarski(k1_xboole_0, B_183) | r1_tarski(k1_xboole_0, B_183))), inference(splitLeft, [status(thm)], [c_442])).
% 18.47/10.29  tff(c_866, plain, (![B_183]: (r1_tarski(k1_xboole_0, B_183))), inference(factorization, [status(thm), theory('equality')], [c_857])).
% 18.47/10.29  tff(c_122, plain, (k4_tarski('#skF_16', '#skF_17')='#skF_15'), inference(cnfTransformation, [status(thm)], [f_144])).
% 18.47/10.29  tff(c_156, plain, (![A_117, B_118]: (k1_mcart_1(k4_tarski(A_117, B_118))=A_117)), inference(cnfTransformation, [status(thm)], [f_118])).
% 18.47/10.29  tff(c_165, plain, (k1_mcart_1('#skF_15')='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_122, c_156])).
% 18.47/10.29  tff(c_120, plain, (k2_mcart_1('#skF_15')='#skF_15' | k1_mcart_1('#skF_15')='#skF_15'), inference(cnfTransformation, [status(thm)], [f_144])).
% 18.47/10.29  tff(c_184, plain, (k2_mcart_1('#skF_15')='#skF_15' | '#skF_15'='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_120])).
% 18.47/10.29  tff(c_185, plain, ('#skF_15'='#skF_16'), inference(splitLeft, [status(thm)], [c_184])).
% 18.47/10.29  tff(c_187, plain, (k4_tarski('#skF_16', '#skF_17')='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_122])).
% 18.47/10.29  tff(c_114, plain, (![A_98]: (r2_hidden('#skF_14'(A_98), A_98) | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_134])).
% 18.47/10.29  tff(c_110, plain, (![A_96, B_97]: (k1_mcart_1(k4_tarski(A_96, B_97))=A_96)), inference(cnfTransformation, [status(thm)], [f_118])).
% 18.47/10.29  tff(c_1184, plain, (![A_2794, B_2795, C_2796, D_2797]: (r2_hidden(k4_tarski(A_2794, B_2795), k2_zfmisc_1(C_2796, D_2797)) | ~r2_hidden(B_2795, D_2797) | ~r2_hidden(A_2794, C_2796))), inference(cnfTransformation, [status(thm)], [f_86])).
% 18.47/10.29  tff(c_108, plain, (![A_93, B_94, C_95]: (k1_mcart_1(A_93)=B_94 | ~r2_hidden(A_93, k2_zfmisc_1(k1_tarski(B_94), C_95)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.47/10.29  tff(c_1202, plain, (![A_2794, B_2795, B_94, D_2797]: (k1_mcart_1(k4_tarski(A_2794, B_2795))=B_94 | ~r2_hidden(B_2795, D_2797) | ~r2_hidden(A_2794, k1_tarski(B_94)))), inference(resolution, [status(thm)], [c_1184, c_108])).
% 18.47/10.29  tff(c_1224, plain, (![B_94, A_2794, B_2795, D_2797]: (B_94=A_2794 | ~r2_hidden(B_2795, D_2797) | ~r2_hidden(A_2794, k1_tarski(B_94)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1202])).
% 18.47/10.29  tff(c_1229, plain, (![B_2795, D_2797]: (~r2_hidden(B_2795, D_2797))), inference(splitLeft, [status(thm)], [c_1224])).
% 18.47/10.29  tff(c_18, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.47/10.29  tff(c_1250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1229, c_18])).
% 18.47/10.29  tff(c_1252, plain, (![B_2798, A_2799]: (B_2798=A_2799 | ~r2_hidden(A_2799, k1_tarski(B_2798)))), inference(splitRight, [status(thm)], [c_1224])).
% 18.47/10.29  tff(c_1267, plain, (![B_2798]: ('#skF_14'(k1_tarski(B_2798))=B_2798 | k1_tarski(B_2798)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_1252])).
% 18.47/10.29  tff(c_1311, plain, (![B_2802]: ('#skF_14'(k1_tarski(B_2802))=B_2802 | k1_tarski(B_2802)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_1252])).
% 18.47/10.29  tff(c_1579, plain, (![B_2821]: (r2_hidden(B_2821, k1_tarski(B_2821)) | k1_tarski(B_2821)=k1_xboole_0 | k1_tarski(B_2821)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1311, c_114])).
% 18.47/10.29  tff(c_116, plain, (![D_107, A_98, C_106]: (~r2_hidden(D_107, A_98) | k4_tarski(C_106, D_107)!='#skF_14'(A_98) | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_134])).
% 18.47/10.29  tff(c_1602, plain, (![C_2824, B_2825]: (k4_tarski(C_2824, B_2825)!='#skF_14'(k1_tarski(B_2825)) | k1_tarski(B_2825)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1579, c_116])).
% 18.47/10.29  tff(c_1980, plain, (![C_2857, B_2858]: (k4_tarski(C_2857, B_2858)!=B_2858 | k1_tarski(B_2858)=k1_xboole_0 | k1_tarski(B_2858)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1267, c_1602])).
% 18.47/10.29  tff(c_1983, plain, ('#skF_17'!='#skF_16' | k1_tarski('#skF_17')=k1_xboole_0 | k1_tarski('#skF_17')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_187, c_1980])).
% 18.47/10.29  tff(c_1984, plain, ('#skF_17'!='#skF_16'), inference(splitLeft, [status(thm)], [c_1983])).
% 18.47/10.29  tff(c_104, plain, (![B_84, C_85, B_86]: (k4_tarski('#skF_12'(k4_tarski(B_84, C_85), B_86), '#skF_13'(k4_tarski(B_84, C_85), B_86))=k4_tarski(B_84, C_85) | k1_mcart_1(k4_tarski(B_84, C_85))=B_86)), inference(cnfTransformation, [status(thm)], [f_108])).
% 18.47/10.29  tff(c_2128, plain, (![B_2883, C_2884, B_2885]: (k4_tarski('#skF_12'(k4_tarski(B_2883, C_2884), B_2885), '#skF_13'(k4_tarski(B_2883, C_2884), B_2885))=k4_tarski(B_2883, C_2884) | B_2885=B_2883)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_104])).
% 18.47/10.29  tff(c_2173, plain, (![B_2883, C_2884, B_2885]: (k1_mcart_1(k4_tarski(B_2883, C_2884))='#skF_12'(k4_tarski(B_2883, C_2884), B_2885) | B_2885=B_2883)), inference(superposition, [status(thm), theory('equality')], [c_2128, c_110])).
% 18.47/10.29  tff(c_2226, plain, (![B_2890, C_2891, B_2892]: ('#skF_12'(k4_tarski(B_2890, C_2891), B_2892)=B_2890 | B_2892=B_2890)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2173])).
% 18.47/10.29  tff(c_2244, plain, (![B_2892]: ('#skF_12'('#skF_16', B_2892)='#skF_16' | B_2892='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_187, c_2226])).
% 18.47/10.29  tff(c_314, plain, (![D_163, B_164, A_165]: (D_163=B_164 | D_163=A_165 | ~r2_hidden(D_163, k2_tarski(A_165, B_164)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.47/10.29  tff(c_330, plain, (![A_165, B_164]: ('#skF_14'(k2_tarski(A_165, B_164))=B_164 | '#skF_14'(k2_tarski(A_165, B_164))=A_165 | k2_tarski(A_165, B_164)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_314])).
% 18.47/10.29  tff(c_28417, plain, (![B_202271]: (k2_tarski(B_202271, B_202271)=k1_xboole_0 | '#skF_14'(k2_tarski(B_202271, B_202271))=B_202271)), inference(factorization, [status(thm), theory('equality')], [c_330])).
% 18.47/10.29  tff(c_2188, plain, (![B_2885]: (k4_tarski('#skF_12'(k4_tarski('#skF_16', '#skF_17'), B_2885), '#skF_13'('#skF_16', B_2885))=k4_tarski('#skF_16', '#skF_17') | B_2885='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_187, c_2128])).
% 18.47/10.29  tff(c_2263, plain, (![B_2894]: (k4_tarski('#skF_12'('#skF_16', B_2894), '#skF_13'('#skF_16', B_2894))='#skF_16' | B_2894='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_187, c_2188])).
% 18.47/10.29  tff(c_2191, plain, (![B_2883, C_2884, B_2885]: ('#skF_12'(k4_tarski(B_2883, C_2884), B_2885)=B_2883 | B_2885=B_2883)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2173])).
% 18.47/10.29  tff(c_2885, plain, (![B_2948, B_2947]: ('#skF_12'('#skF_16', B_2948)='#skF_12'('#skF_16', B_2947) | B_2948='#skF_12'('#skF_16', B_2947) | B_2947='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_2263, c_2191])).
% 18.47/10.29  tff(c_6364, plain, (![B_19715]: ('#skF_12'('#skF_16', '#skF_17')='#skF_16' | B_19715='#skF_16' | '#skF_12'('#skF_16', B_19715)='#skF_17' | B_19715='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_2885, c_2244])).
% 18.47/10.29  tff(c_6367, plain, (![B_19715]: ('#skF_17'='#skF_16' | B_19715='#skF_16' | '#skF_12'('#skF_16', '#skF_17')='#skF_16' | B_19715='#skF_16' | B_19715='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_6364, c_2244])).
% 18.47/10.29  tff(c_7147, plain, (![B_19715]: (B_19715='#skF_16' | '#skF_12'('#skF_16', '#skF_17')='#skF_16' | B_19715='#skF_16' | B_19715='#skF_16')), inference(negUnitSimplification, [status(thm)], [c_1984, c_6367])).
% 18.47/10.29  tff(c_7181, plain, ('#skF_12'('#skF_16', '#skF_17')='#skF_16'), inference(splitLeft, [status(thm)], [c_7147])).
% 18.47/10.29  tff(c_2194, plain, (![B_2885]: (k4_tarski('#skF_12'('#skF_16', B_2885), '#skF_13'('#skF_16', B_2885))='#skF_16' | B_2885='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_187, c_2188])).
% 18.47/10.29  tff(c_7213, plain, (k4_tarski('#skF_16', '#skF_13'('#skF_16', '#skF_17'))='#skF_16' | '#skF_17'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_7181, c_2194])).
% 18.47/10.29  tff(c_7296, plain, (k4_tarski('#skF_16', '#skF_13'('#skF_16', '#skF_17'))='#skF_16'), inference(negUnitSimplification, [status(thm)], [c_1984, c_7213])).
% 18.47/10.29  tff(c_42, plain, (![D_20, B_16]: (r2_hidden(D_20, k2_tarski(D_20, B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.47/10.29  tff(c_994, plain, (![C_2753, A_2754, D_2755]: (~r2_hidden(C_2753, A_2754) | k4_tarski(C_2753, D_2755)!='#skF_14'(A_2754) | k1_xboole_0=A_2754)), inference(cnfTransformation, [status(thm)], [f_134])).
% 18.47/10.29  tff(c_1015, plain, (![D_20, D_2755, B_16]: (k4_tarski(D_20, D_2755)!='#skF_14'(k2_tarski(D_20, B_16)) | k2_tarski(D_20, B_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_994])).
% 18.47/10.29  tff(c_7315, plain, (![B_16]: ('#skF_14'(k2_tarski('#skF_16', B_16))!='#skF_16' | k2_tarski('#skF_16', B_16)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7296, c_1015])).
% 18.47/10.29  tff(c_28849, plain, (k2_tarski('#skF_16', '#skF_16')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_28417, c_7315])).
% 18.47/10.29  tff(c_215, plain, (![B_125, A_126]: (~r1_tarski(B_125, A_126) | ~r2_hidden(A_126, B_125))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.47/10.29  tff(c_231, plain, (![D_20, B_16]: (~r1_tarski(k2_tarski(D_20, B_16), D_20))), inference(resolution, [status(thm)], [c_42, c_215])).
% 18.47/10.29  tff(c_28907, plain, (~r1_tarski(k1_xboole_0, '#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_28849, c_231])).
% 18.47/10.29  tff(c_29129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_866, c_28907])).
% 18.47/10.29  tff(c_29131, plain, ('#skF_12'('#skF_16', '#skF_17')!='#skF_16'), inference(splitRight, [status(thm)], [c_7147])).
% 18.47/10.29  tff(c_29149, plain, ('#skF_17'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_2244, c_29131])).
% 18.47/10.29  tff(c_29156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1984, c_29149])).
% 18.47/10.29  tff(c_29158, plain, ('#skF_17'='#skF_16'), inference(splitRight, [status(thm)], [c_1983])).
% 18.47/10.29  tff(c_29165, plain, (k4_tarski('#skF_16', '#skF_16')='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_29158, c_187])).
% 18.47/10.29  tff(c_68295, plain, (![B_497491]: (k2_tarski(B_497491, B_497491)=k1_xboole_0 | '#skF_14'(k2_tarski(B_497491, B_497491))=B_497491)), inference(factorization, [status(thm), theory('equality')], [c_330])).
% 18.47/10.29  tff(c_40, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.47/10.29  tff(c_1014, plain, (![D_20, D_2755, A_15]: (k4_tarski(D_20, D_2755)!='#skF_14'(k2_tarski(A_15, D_20)) | k2_tarski(A_15, D_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_994])).
% 18.47/10.29  tff(c_68624, plain, (![B_497926, D_497927]: (k4_tarski(B_497926, D_497927)!=B_497926 | k2_tarski(B_497926, B_497926)=k1_xboole_0 | k2_tarski(B_497926, B_497926)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68295, c_1014])).
% 18.47/10.29  tff(c_68761, plain, (k2_tarski('#skF_16', '#skF_16')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_29165, c_68624])).
% 18.47/10.29  tff(c_68808, plain, (~r1_tarski(k1_xboole_0, '#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_68761, c_231])).
% 18.47/10.29  tff(c_68963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_866, c_68808])).
% 18.47/10.29  tff(c_68965, plain, (![B_498796]: (B_498796='#skF_17')), inference(splitRight, [status(thm)], [c_442])).
% 18.47/10.29  tff(c_234, plain, (![E_131, A_132, B_133]: (r2_hidden(E_131, k1_enumset1(A_132, B_133, E_131)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.47/10.29  tff(c_98, plain, (![B_71, A_70]: (~r1_tarski(B_71, A_70) | ~r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.47/10.29  tff(c_238, plain, (![A_132, B_133, E_131]: (~r1_tarski(k1_enumset1(A_132, B_133, E_131), E_131))), inference(resolution, [status(thm)], [c_234, c_98])).
% 18.47/10.29  tff(c_69257, plain, (![E_506552]: (~r1_tarski('#skF_17', E_506552))), inference(superposition, [status(thm), theory('equality')], [c_68965, c_238])).
% 18.47/10.29  tff(c_69267, plain, $false, inference(resolution, [status(thm)], [c_12, c_69257])).
% 18.47/10.29  tff(c_69269, plain, ('#skF_15'!='#skF_16'), inference(splitRight, [status(thm)], [c_184])).
% 18.47/10.29  tff(c_69268, plain, (k2_mcart_1('#skF_15')='#skF_15'), inference(splitRight, [status(thm)], [c_184])).
% 18.47/10.29  tff(c_172, plain, (![A_119, B_120]: (k2_mcart_1(k4_tarski(A_119, B_120))=B_120)), inference(cnfTransformation, [status(thm)], [f_118])).
% 18.47/10.29  tff(c_181, plain, (k2_mcart_1('#skF_15')='#skF_17'), inference(superposition, [status(thm), theory('equality')], [c_122, c_172])).
% 18.47/10.29  tff(c_69274, plain, ('#skF_17'='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_69268, c_181])).
% 18.47/10.29  tff(c_69279, plain, (k4_tarski('#skF_16', '#skF_15')='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_69274, c_122])).
% 18.47/10.29  tff(c_71479, plain, (![B_509579, C_509580, B_509581]: (k4_tarski('#skF_12'(k4_tarski(B_509579, C_509580), B_509581), '#skF_13'(k4_tarski(B_509579, C_509580), B_509581))=k4_tarski(B_509579, C_509580) | B_509581=B_509579)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_104])).
% 18.47/10.29  tff(c_71530, plain, (![B_509579, C_509580, B_509581]: (k1_mcart_1(k4_tarski(B_509579, C_509580))='#skF_12'(k4_tarski(B_509579, C_509580), B_509581) | B_509581=B_509579)), inference(superposition, [status(thm), theory('equality')], [c_71479, c_110])).
% 18.47/10.29  tff(c_71583, plain, (![B_509586, C_509587, B_509588]: ('#skF_12'(k4_tarski(B_509586, C_509587), B_509588)=B_509586 | B_509588=B_509586)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_71530])).
% 18.47/10.29  tff(c_71601, plain, (![B_509588]: ('#skF_12'('#skF_15', B_509588)='#skF_16' | B_509588='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_69279, c_71583])).
% 18.47/10.29  tff(c_69418, plain, (![A_506846, B_506847, C_506848]: (k1_mcart_1(A_506846)=B_506847 | ~r2_hidden(A_506846, k2_zfmisc_1(k1_tarski(B_506847), C_506848)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.47/10.29  tff(c_69454, plain, (![A_506852, B_506853]: (k1_mcart_1(A_506852)=B_506853 | ~r2_hidden(A_506852, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_94, c_69418])).
% 18.47/10.29  tff(c_69492, plain, (![B_506863]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_506863))='#skF_17' | r1_tarski(k1_xboole_0, B_506863))), inference(resolution, [status(thm)], [c_6, c_69454])).
% 18.47/10.29  tff(c_69461, plain, (![B_2, B_506853]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_2))=B_506853 | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_69454])).
% 18.47/10.29  tff(c_69495, plain, (![B_506853, B_506863]: (B_506853='#skF_17' | r1_tarski(k1_xboole_0, B_506863) | r1_tarski(k1_xboole_0, B_506863))), inference(superposition, [status(thm), theory('equality')], [c_69492, c_69461])).
% 18.47/10.29  tff(c_69938, plain, (![B_506853, B_506863]: (B_506853='#skF_15' | r1_tarski(k1_xboole_0, B_506863) | r1_tarski(k1_xboole_0, B_506863))), inference(demodulation, [status(thm), theory('equality')], [c_69274, c_69495])).
% 18.47/10.29  tff(c_69940, plain, (![B_506863]: (r1_tarski(k1_xboole_0, B_506863) | r1_tarski(k1_xboole_0, B_506863))), inference(splitLeft, [status(thm)], [c_69938])).
% 18.47/10.29  tff(c_69949, plain, (![B_506863]: (r1_tarski(k1_xboole_0, B_506863))), inference(factorization, [status(thm), theory('equality')], [c_69940])).
% 18.47/10.29  tff(c_69397, plain, (![D_506843, B_506844, A_506845]: (D_506843=B_506844 | D_506843=A_506845 | ~r2_hidden(D_506843, k2_tarski(A_506845, B_506844)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.47/10.29  tff(c_69413, plain, (![A_506845, B_506844]: ('#skF_14'(k2_tarski(A_506845, B_506844))=B_506844 | '#skF_14'(k2_tarski(A_506845, B_506844))=A_506845 | k2_tarski(A_506845, B_506844)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_69397])).
% 18.47/10.29  tff(c_102833, plain, (![B_766901]: (k2_tarski(B_766901, B_766901)=k1_xboole_0 | '#skF_14'(k2_tarski(B_766901, B_766901))=B_766901)), inference(factorization, [status(thm), theory('equality')], [c_69413])).
% 18.47/10.29  tff(c_112, plain, (![A_96, B_97]: (k2_mcart_1(k4_tarski(A_96, B_97))=B_97)), inference(cnfTransformation, [status(thm)], [f_118])).
% 18.47/10.29  tff(c_71527, plain, (![B_509579, C_509580, B_509581]: (k2_mcart_1(k4_tarski(B_509579, C_509580))='#skF_13'(k4_tarski(B_509579, C_509580), B_509581) | B_509581=B_509579)), inference(superposition, [status(thm), theory('equality')], [c_71479, c_112])).
% 18.47/10.29  tff(c_71554, plain, (![B_509582, C_509583, B_509584]: ('#skF_13'(k4_tarski(B_509582, C_509583), B_509584)=C_509583 | B_509584=B_509582)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_71527])).
% 18.47/10.29  tff(c_71569, plain, (![B_509584]: ('#skF_13'('#skF_15', B_509584)='#skF_15' | B_509584='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_69279, c_71554])).
% 18.47/10.29  tff(c_71545, plain, (![B_509581]: (k4_tarski('#skF_12'(k4_tarski('#skF_16', '#skF_15'), B_509581), '#skF_13'('#skF_15', B_509581))=k4_tarski('#skF_16', '#skF_15') | B_509581='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_69279, c_71479])).
% 18.47/10.29  tff(c_71620, plain, (![B_509590]: (k4_tarski('#skF_12'('#skF_15', B_509590), '#skF_13'('#skF_15', B_509590))='#skF_15' | B_509590='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_69279, c_69279, c_71545])).
% 18.47/10.29  tff(c_71758, plain, (![B_509594]: (k4_tarski('#skF_12'('#skF_15', B_509594), '#skF_15')='#skF_15' | B_509594='#skF_16' | B_509594='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_71569, c_71620])).
% 18.47/10.29  tff(c_69979, plain, (![D_509409, A_509410, C_509411]: (~r2_hidden(D_509409, A_509410) | k4_tarski(C_509411, D_509409)!='#skF_14'(A_509410) | k1_xboole_0=A_509410)), inference(cnfTransformation, [status(thm)], [f_134])).
% 18.47/10.29  tff(c_69999, plain, (![C_509411, D_20, A_15]: (k4_tarski(C_509411, D_20)!='#skF_14'(k2_tarski(A_15, D_20)) | k2_tarski(A_15, D_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_69979])).
% 18.47/10.29  tff(c_71776, plain, (![A_15, B_509594]: ('#skF_14'(k2_tarski(A_15, '#skF_15'))!='#skF_15' | k2_tarski(A_15, '#skF_15')=k1_xboole_0 | B_509594='#skF_16' | B_509594='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_71758, c_69999])).
% 18.47/10.29  tff(c_92868, plain, (![B_509594]: (B_509594='#skF_16' | B_509594='#skF_16')), inference(splitLeft, [status(thm)], [c_71776])).
% 18.47/10.29  tff(c_93779, plain, (![B_682523]: (B_682523='#skF_16')), inference(factorization, [status(thm), theory('equality')], [c_92868])).
% 18.47/10.29  tff(c_71548, plain, (![B_509579, C_509580, B_509581]: ('#skF_12'(k4_tarski(B_509579, C_509580), B_509581)=B_509579 | B_509581=B_509579)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_71530])).
% 18.47/10.29  tff(c_74192, plain, (![B_527327, B_527326]: ('#skF_12'('#skF_15', B_527327)='#skF_12'('#skF_15', B_527326) | B_527327='#skF_12'('#skF_15', B_527326) | B_527326='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_71620, c_71548])).
% 18.47/10.29  tff(c_76294, plain, (![B_529354]: ('#skF_12'('#skF_15', '#skF_17')='#skF_16' | '#skF_12'('#skF_15', B_529354)='#skF_17' | B_529354='#skF_16' | B_529354='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_71601, c_74192])).
% 18.47/10.29  tff(c_76297, plain, (![B_529354]: ('#skF_17'='#skF_16' | B_529354='#skF_16' | '#skF_12'('#skF_15', '#skF_17')='#skF_16' | B_529354='#skF_16' | B_529354='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_76294, c_71601])).
% 18.47/10.29  tff(c_77196, plain, (![B_529354]: ('#skF_15'='#skF_16' | B_529354='#skF_16' | '#skF_12'('#skF_15', '#skF_15')='#skF_16' | B_529354='#skF_16' | B_529354='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_69274, c_69274, c_76297])).
% 18.47/10.29  tff(c_77197, plain, (![B_529354]: (B_529354='#skF_16' | '#skF_12'('#skF_15', '#skF_15')='#skF_16' | B_529354='#skF_16' | B_529354='#skF_16')), inference(negUnitSimplification, [status(thm)], [c_69269, c_77196])).
% 18.47/10.29  tff(c_77217, plain, ('#skF_12'('#skF_15', '#skF_15')='#skF_16'), inference(splitLeft, [status(thm)], [c_77197])).
% 18.47/10.29  tff(c_71551, plain, (![B_509581]: (k4_tarski('#skF_12'('#skF_15', B_509581), '#skF_13'('#skF_15', B_509581))='#skF_15' | B_509581='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_69279, c_69279, c_71545])).
% 18.47/10.29  tff(c_77249, plain, (k4_tarski('#skF_16', '#skF_13'('#skF_15', '#skF_15'))='#skF_15' | '#skF_15'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_77217, c_71551])).
% 18.47/10.29  tff(c_77329, plain, (k4_tarski('#skF_16', '#skF_13'('#skF_15', '#skF_15'))='#skF_15'), inference(negUnitSimplification, [status(thm)], [c_69269, c_77249])).
% 18.47/10.29  tff(c_77390, plain, (k2_mcart_1('#skF_15')='#skF_13'('#skF_15', '#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_77329, c_112])).
% 18.47/10.29  tff(c_77420, plain, ('#skF_13'('#skF_15', '#skF_15')='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_69268, c_77390])).
% 18.47/10.29  tff(c_94025, plain, ('#skF_15'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_93779, c_77420])).
% 18.47/10.29  tff(c_94464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69269, c_94025])).
% 18.47/10.29  tff(c_94465, plain, (![A_15]: ('#skF_14'(k2_tarski(A_15, '#skF_15'))!='#skF_15' | k2_tarski(A_15, '#skF_15')=k1_xboole_0)), inference(splitRight, [status(thm)], [c_71776])).
% 18.47/10.29  tff(c_103265, plain, (k2_tarski('#skF_15', '#skF_15')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102833, c_94465])).
% 18.47/10.29  tff(c_69299, plain, (![B_506808, A_506809]: (~r1_tarski(B_506808, A_506809) | ~r2_hidden(A_506809, B_506808))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.47/10.29  tff(c_69319, plain, (![D_20, B_16]: (~r1_tarski(k2_tarski(D_20, B_16), D_20))), inference(resolution, [status(thm)], [c_42, c_69299])).
% 18.47/10.29  tff(c_103323, plain, (~r1_tarski(k1_xboole_0, '#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_103265, c_69319])).
% 18.47/10.29  tff(c_103545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69949, c_103323])).
% 18.47/10.29  tff(c_103547, plain, ('#skF_12'('#skF_15', '#skF_15')!='#skF_16'), inference(splitRight, [status(thm)], [c_77197])).
% 18.47/10.29  tff(c_103565, plain, ('#skF_15'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_71601, c_103547])).
% 18.47/10.29  tff(c_103572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69269, c_103565])).
% 18.47/10.29  tff(c_103587, plain, (![B_768144]: (B_768144='#skF_15')), inference(splitRight, [status(thm)], [c_69938])).
% 18.47/10.29  tff(c_103663, plain, ('#skF_15'='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_103587, c_165])).
% 18.47/10.29  tff(c_103686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69269, c_103663])).
% 18.47/10.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.47/10.29  
% 18.47/10.29  Inference rules
% 18.47/10.29  ----------------------
% 18.47/10.29  #Ref     : 10
% 18.47/10.29  #Sup     : 18101
% 18.47/10.29  #Fact    : 135
% 18.47/10.29  #Define  : 0
% 18.47/10.29  #Split   : 54
% 18.47/10.29  #Chain   : 0
% 18.47/10.29  #Close   : 0
% 18.47/10.29  
% 18.47/10.29  Ordering : KBO
% 18.47/10.29  
% 18.47/10.29  Simplification rules
% 18.47/10.29  ----------------------
% 18.47/10.29  #Subsume      : 4835
% 18.47/10.29  #Demod        : 3578
% 18.47/10.29  #Tautology    : 2320
% 18.47/10.29  #SimpNegUnit  : 535
% 18.47/10.29  #BackRed      : 117
% 18.47/10.29  
% 18.47/10.29  #Partial instantiations: 172427
% 18.47/10.29  #Strategies tried      : 1
% 18.47/10.29  
% 18.47/10.29  Timing (in seconds)
% 18.47/10.29  ----------------------
% 18.47/10.29  Preprocessing        : 0.37
% 18.47/10.29  Parsing              : 0.18
% 18.47/10.29  CNF conversion       : 0.03
% 18.47/10.29  Main loop            : 9.14
% 18.47/10.29  Inferencing          : 4.56
% 18.47/10.29  Reduction            : 1.62
% 18.47/10.29  Demodulation         : 1.06
% 18.47/10.29  BG Simplification    : 0.25
% 18.47/10.29  Subsumption          : 2.24
% 18.47/10.29  Abstraction          : 0.32
% 18.47/10.29  MUC search           : 0.00
% 18.47/10.29  Cooper               : 0.00
% 18.47/10.29  Total                : 9.56
% 18.47/10.29  Index Insertion      : 0.00
% 18.47/10.29  Index Deletion       : 0.00
% 18.47/10.29  Index Matching       : 0.00
% 18.47/10.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
