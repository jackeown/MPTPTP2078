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
% DateTime   : Thu Dec  3 09:54:16 EST 2020

% Result     : Theorem 6.01s
% Output     : CNFRefutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 450 expanded)
%              Number of leaves         :   30 ( 158 expanded)
%              Depth                    :   10
%              Number of atoms          :  243 (1028 expanded)
%              Number of equality atoms :   53 ( 393 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_48,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_90,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_319,plain,(
    ! [C_97,A_98,B_99] :
      ( r1_tarski(k2_zfmisc_1(C_97,A_98),k2_zfmisc_1(C_97,B_99))
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_330,plain,(
    ! [B_99] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_7',B_99))
      | ~ r1_tarski('#skF_8',B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_319])).

tff(c_738,plain,(
    ! [B_146,A_147,C_148] :
      ( ~ r1_tarski(k2_zfmisc_1(B_146,A_147),k2_zfmisc_1(C_148,A_147))
      | r1_tarski(B_146,C_148)
      | k1_xboole_0 = A_147 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_784,plain,
    ( r1_tarski('#skF_9','#skF_7')
    | k1_xboole_0 = '#skF_10'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_330,c_738])).

tff(c_801,plain,(
    ~ r1_tarski('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_784])).

tff(c_82,plain,(
    ! [A_35,C_37,B_36] :
      ( r1_tarski(k2_zfmisc_1(A_35,C_37),k2_zfmisc_1(B_36,C_37))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_846,plain,(
    ! [A_152,B_153,C_154] :
      ( ~ r1_tarski(k2_zfmisc_1(A_152,B_153),k2_zfmisc_1(A_152,C_154))
      | r1_tarski(B_153,C_154)
      | k1_xboole_0 = A_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_865,plain,(
    ! [C_154] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_7',C_154))
      | r1_tarski('#skF_8',C_154)
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_846])).

tff(c_1717,plain,(
    ! [C_191] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_7',C_191))
      | r1_tarski('#skF_8',C_191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_865])).

tff(c_1731,plain,
    ( r1_tarski('#skF_8','#skF_10')
    | ~ r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_1717])).

tff(c_1753,plain,(
    ~ r1_tarski('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_801,c_1731])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_143,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_2'(A_57,B_58),A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_72,plain,(
    ! [A_30] : k2_zfmisc_1(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_353,plain,(
    ! [A_100,A_101] :
      ( r1_tarski(k2_zfmisc_1(A_100,A_101),k1_xboole_0)
      | ~ r1_tarski(A_101,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_319])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_248,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_275,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89),B_90)
      | ~ r1_tarski(A_89,B_90)
      | v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_4,c_248])).

tff(c_292,plain,(
    ! [B_90,A_89] :
      ( ~ v1_xboole_0(B_90)
      | ~ r1_tarski(A_89,B_90)
      | v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_275,c_2])).

tff(c_356,plain,(
    ! [A_100,A_101] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k2_zfmisc_1(A_100,A_101))
      | ~ r1_tarski(A_101,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_353,c_292])).

tff(c_376,plain,(
    ! [A_100,A_101] :
      ( v1_xboole_0(k2_zfmisc_1(A_100,A_101))
      | ~ r1_tarski(A_101,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_356])).

tff(c_806,plain,(
    ! [B_149,C_150,A_151] :
      ( r1_tarski(B_149,C_150)
      | k1_xboole_0 = A_151
      | ~ v1_xboole_0(k2_zfmisc_1(B_149,A_151)) ) ),
    inference(resolution,[status(thm)],[c_147,c_738])).

tff(c_814,plain,(
    ! [C_150] :
      ( r1_tarski('#skF_7',C_150)
      | k1_xboole_0 = '#skF_8'
      | ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_806])).

tff(c_823,plain,(
    ! [C_150] :
      ( r1_tarski('#skF_7',C_150)
      | ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_814])).

tff(c_829,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_837,plain,(
    ~ r1_tarski('#skF_10',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_376,c_829])).

tff(c_845,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_147,c_837])).

tff(c_64,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( r2_hidden(k4_tarski(A_26,B_27),k2_zfmisc_1(C_28,D_29))
      | ~ r2_hidden(B_27,D_29)
      | ~ r2_hidden(A_26,C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_438,plain,(
    ! [A_108,C_109,B_110,D_111] :
      ( r2_hidden(A_108,C_109)
      | ~ r2_hidden(k4_tarski(A_108,B_110),k2_zfmisc_1(C_109,D_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2633,plain,(
    ! [A_232,B_233] :
      ( r2_hidden(A_232,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_232,B_233),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_438])).

tff(c_2638,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,'#skF_7')
      | ~ r2_hidden(B_27,'#skF_10')
      | ~ r2_hidden(A_26,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_64,c_2633])).

tff(c_2729,plain,(
    ! [B_246] : ~ r2_hidden(B_246,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2638])).

tff(c_2761,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_2729])).

tff(c_2771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_845,c_2761])).

tff(c_2773,plain,(
    ! [A_247] :
      ( r2_hidden(A_247,'#skF_7')
      | ~ r2_hidden(A_247,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2638])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2786,plain,(
    ! [A_248] :
      ( r1_tarski(A_248,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_248,'#skF_7'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2773,c_8])).

tff(c_2790,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_2786])).

tff(c_2794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1753,c_1753,c_2790])).

tff(c_2795,plain,(
    ! [C_150] : r1_tarski('#skF_7',C_150) ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_74,plain,(
    ! [B_31] : k2_zfmisc_1(k1_xboole_0,B_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_568,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_tarski(k2_zfmisc_1(A_132,C_133),k2_zfmisc_1(B_134,C_133))
      | ~ r1_tarski(A_132,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_630,plain,(
    ! [A_138,B_139] :
      ( r1_tarski(k2_zfmisc_1(A_138,B_139),k1_xboole_0)
      | ~ r1_tarski(A_138,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_568])).

tff(c_649,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k1_xboole_0)
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_630])).

tff(c_700,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_649])).

tff(c_2800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2795,c_700])).

tff(c_2802,plain,(
    r1_tarski('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_784])).

tff(c_84,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_94,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_2801,plain,
    ( k1_xboole_0 = '#skF_10'
    | r1_tarski('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_784])).

tff(c_2816,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2801])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2882,plain,
    ( '#skF_7' = '#skF_9'
    | ~ r1_tarski('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_2816,c_32])).

tff(c_2888,plain,(
    ~ r1_tarski('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2882])).

tff(c_36,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2815,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_2802,c_32])).

tff(c_2893,plain,(
    ~ r1_tarski('#skF_10','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2815])).

tff(c_635,plain,(
    ! [A_138,B_139] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k2_zfmisc_1(A_138,B_139))
      | ~ r1_tarski(A_138,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_630,c_292])).

tff(c_659,plain,(
    ! [A_138,B_139] :
      ( v1_xboole_0(k2_zfmisc_1(A_138,B_139))
      | ~ r1_tarski(A_138,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_635])).

tff(c_2817,plain,(
    ! [A_251,B_252,C_253] :
      ( ~ r1_tarski(k2_zfmisc_1(A_251,B_252),k2_zfmisc_1(A_251,C_253))
      | r1_tarski(B_252,C_253)
      | k1_xboole_0 = A_251 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3057,plain,(
    ! [B_265,C_266,A_267] :
      ( r1_tarski(B_265,C_266)
      | k1_xboole_0 = A_267
      | ~ v1_xboole_0(k2_zfmisc_1(A_267,B_265)) ) ),
    inference(resolution,[status(thm)],[c_147,c_2817])).

tff(c_3065,plain,(
    ! [C_266] :
      ( r1_tarski('#skF_8',C_266)
      | k1_xboole_0 = '#skF_7'
      | ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_3057])).

tff(c_3074,plain,(
    ! [C_266] :
      ( r1_tarski('#skF_8',C_266)
      | ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3065])).

tff(c_3080,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_3074])).

tff(c_3087,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_659,c_3080])).

tff(c_3093,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_147,c_3087])).

tff(c_264,plain,(
    ! [B_82,D_83,A_84,C_85] :
      ( r2_hidden(B_82,D_83)
      | ~ r2_hidden(k4_tarski(A_84,B_82),k2_zfmisc_1(C_85,D_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4484,plain,(
    ! [B_342,A_343] :
      ( r2_hidden(B_342,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_343,B_342),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_264])).

tff(c_4489,plain,(
    ! [B_27,A_26] :
      ( r2_hidden(B_27,'#skF_8')
      | ~ r2_hidden(B_27,'#skF_10')
      | ~ r2_hidden(A_26,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_64,c_4484])).

tff(c_5003,plain,(
    ! [A_369] : ~ r2_hidden(A_369,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4489])).

tff(c_5039,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_5003])).

tff(c_5050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3093,c_5039])).

tff(c_5063,plain,(
    ! [B_374] :
      ( r2_hidden(B_374,'#skF_8')
      | ~ r2_hidden(B_374,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_4489])).

tff(c_5199,plain,(
    ! [B_379] :
      ( r2_hidden('#skF_2'('#skF_10',B_379),'#skF_8')
      | r1_tarski('#skF_10',B_379) ) ),
    inference(resolution,[status(thm)],[c_10,c_5063])).

tff(c_5205,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_5199,c_8])).

tff(c_5213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2893,c_2893,c_5205])).

tff(c_5214,plain,(
    ! [C_266] : r1_tarski('#skF_8',C_266) ),
    inference(splitRight,[status(thm)],[c_3074])).

tff(c_367,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k1_xboole_0)
    | ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_353])).

tff(c_410,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_5221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5214,c_410])).

tff(c_5222,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2815])).

tff(c_333,plain,(
    ! [A_98] :
      ( r1_tarski(k2_zfmisc_1('#skF_7',A_98),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r1_tarski(A_98,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_319])).

tff(c_6548,plain,(
    ! [A_459] :
      ( r1_tarski(k2_zfmisc_1('#skF_7',A_459),k2_zfmisc_1('#skF_9','#skF_8'))
      | ~ r1_tarski(A_459,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5222,c_333])).

tff(c_78,plain,(
    ! [B_33,A_32,C_34] :
      ( ~ r1_tarski(k2_zfmisc_1(B_33,A_32),k2_zfmisc_1(C_34,A_32))
      | r1_tarski(B_33,C_34)
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6556,plain,
    ( r1_tarski('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_6548,c_78])).

tff(c_6585,plain,
    ( r1_tarski('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6556])).

tff(c_6587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2888,c_6585])).

tff(c_6588,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_2801])).

tff(c_6600,plain,(
    ~ r1_tarski('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6588,c_410])).

tff(c_6617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2802,c_6600])).

tff(c_6619,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_649])).

tff(c_160,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_167,plain,(
    ! [B_58,A_57] :
      ( B_58 = A_57
      | ~ r1_tarski(B_58,A_57)
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_147,c_160])).

tff(c_6629,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6619,c_167])).

tff(c_6642,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6629])).

tff(c_6644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6642])).

tff(c_6646,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_6654,plain,
    ( k1_xboole_0 = '#skF_8'
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6646,c_167])).

tff(c_6666,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6654])).

tff(c_6668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6666])).

tff(c_6669,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_6670,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_6671,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6670,c_88])).

tff(c_6699,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6670,c_90])).

tff(c_7145,plain,(
    ! [A_551,C_552,B_553] :
      ( r1_tarski(k2_zfmisc_1(A_551,C_552),k2_zfmisc_1(B_553,C_552))
      | ~ r1_tarski(A_551,B_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7162,plain,(
    ! [B_553] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_8'),k2_zfmisc_1(B_553,'#skF_10'))
      | ~ r1_tarski('#skF_9',B_553) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6699,c_7145])).

tff(c_7771,plain,(
    ! [A_585,B_586,C_587] :
      ( ~ r1_tarski(k2_zfmisc_1(A_585,B_586),k2_zfmisc_1(A_585,C_587))
      | r1_tarski(B_586,C_587)
      | k1_xboole_0 = A_585 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7775,plain,
    ( r1_tarski('#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_7162,c_7771])).

tff(c_7844,plain,
    ( r1_tarski('#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7775])).

tff(c_7845,plain,(
    r1_tarski('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_6671,c_7844])).

tff(c_7165,plain,(
    ! [A_551] :
      ( r1_tarski(k2_zfmisc_1(A_551,'#skF_10'),k2_zfmisc_1('#skF_9','#skF_8'))
      | ~ r1_tarski(A_551,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6699,c_7145])).

tff(c_7800,plain,
    ( r1_tarski('#skF_10','#skF_8')
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_7165,c_7771])).

tff(c_7857,plain,
    ( r1_tarski('#skF_10','#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7800])).

tff(c_7858,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_6671,c_7857])).

tff(c_7902,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_7858,c_32])).

tff(c_7911,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7845,c_7902])).

tff(c_7913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6669,c_7911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:14:04 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.01/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.15  
% 6.01/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.16  %$ r2_hidden > r1_tarski > v1_xboole_0 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_2
% 6.01/2.16  
% 6.01/2.16  %Foreground sorts:
% 6.01/2.16  
% 6.01/2.16  
% 6.01/2.16  %Background operators:
% 6.01/2.16  
% 6.01/2.16  
% 6.01/2.16  %Foreground operators:
% 6.01/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.01/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.01/2.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.01/2.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.01/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.01/2.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.01/2.16  tff('#skF_7', type, '#skF_7': $i).
% 6.01/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.01/2.16  tff('#skF_10', type, '#skF_10': $i).
% 6.01/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.01/2.16  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.01/2.16  tff('#skF_9', type, '#skF_9': $i).
% 6.01/2.16  tff('#skF_8', type, '#skF_8': $i).
% 6.01/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.01/2.16  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.01/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.01/2.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.01/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.01/2.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.01/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.01/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.01/2.16  
% 6.01/2.18  tff(f_111, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 6.01/2.18  tff(f_48, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.01/2.18  tff(f_100, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 6.01/2.18  tff(f_94, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 6.01/2.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.01/2.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.01/2.18  tff(f_83, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.01/2.18  tff(f_77, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.01/2.18  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.01/2.18  tff(c_86, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.01/2.18  tff(c_30, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.01/2.18  tff(c_88, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.01/2.18  tff(c_90, plain, (k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.01/2.18  tff(c_319, plain, (![C_97, A_98, B_99]: (r1_tarski(k2_zfmisc_1(C_97, A_98), k2_zfmisc_1(C_97, B_99)) | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.18  tff(c_330, plain, (![B_99]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_7', B_99)) | ~r1_tarski('#skF_8', B_99))), inference(superposition, [status(thm), theory('equality')], [c_90, c_319])).
% 6.01/2.18  tff(c_738, plain, (![B_146, A_147, C_148]: (~r1_tarski(k2_zfmisc_1(B_146, A_147), k2_zfmisc_1(C_148, A_147)) | r1_tarski(B_146, C_148) | k1_xboole_0=A_147)), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.01/2.18  tff(c_784, plain, (r1_tarski('#skF_9', '#skF_7') | k1_xboole_0='#skF_10' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_330, c_738])).
% 6.01/2.18  tff(c_801, plain, (~r1_tarski('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_784])).
% 6.01/2.18  tff(c_82, plain, (![A_35, C_37, B_36]: (r1_tarski(k2_zfmisc_1(A_35, C_37), k2_zfmisc_1(B_36, C_37)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.18  tff(c_846, plain, (![A_152, B_153, C_154]: (~r1_tarski(k2_zfmisc_1(A_152, B_153), k2_zfmisc_1(A_152, C_154)) | r1_tarski(B_153, C_154) | k1_xboole_0=A_152)), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.01/2.18  tff(c_865, plain, (![C_154]: (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_7', C_154)) | r1_tarski('#skF_8', C_154) | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_90, c_846])).
% 6.01/2.18  tff(c_1717, plain, (![C_191]: (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_7', C_191)) | r1_tarski('#skF_8', C_191))), inference(negUnitSimplification, [status(thm)], [c_88, c_865])).
% 6.01/2.18  tff(c_1731, plain, (r1_tarski('#skF_8', '#skF_10') | ~r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_82, c_1717])).
% 6.01/2.18  tff(c_1753, plain, (~r1_tarski('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_801, c_1731])).
% 6.01/2.18  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.01/2.18  tff(c_143, plain, (![A_57, B_58]: (r2_hidden('#skF_2'(A_57, B_58), A_57) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.01/2.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.01/2.18  tff(c_147, plain, (![A_57, B_58]: (~v1_xboole_0(A_57) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_143, c_2])).
% 6.01/2.18  tff(c_72, plain, (![A_30]: (k2_zfmisc_1(A_30, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.01/2.18  tff(c_353, plain, (![A_100, A_101]: (r1_tarski(k2_zfmisc_1(A_100, A_101), k1_xboole_0) | ~r1_tarski(A_101, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72, c_319])).
% 6.01/2.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.01/2.18  tff(c_248, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.01/2.18  tff(c_275, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89), B_90) | ~r1_tarski(A_89, B_90) | v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_4, c_248])).
% 6.01/2.18  tff(c_292, plain, (![B_90, A_89]: (~v1_xboole_0(B_90) | ~r1_tarski(A_89, B_90) | v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_275, c_2])).
% 6.01/2.18  tff(c_356, plain, (![A_100, A_101]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_zfmisc_1(A_100, A_101)) | ~r1_tarski(A_101, k1_xboole_0))), inference(resolution, [status(thm)], [c_353, c_292])).
% 6.01/2.18  tff(c_376, plain, (![A_100, A_101]: (v1_xboole_0(k2_zfmisc_1(A_100, A_101)) | ~r1_tarski(A_101, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_356])).
% 6.01/2.18  tff(c_806, plain, (![B_149, C_150, A_151]: (r1_tarski(B_149, C_150) | k1_xboole_0=A_151 | ~v1_xboole_0(k2_zfmisc_1(B_149, A_151)))), inference(resolution, [status(thm)], [c_147, c_738])).
% 6.01/2.18  tff(c_814, plain, (![C_150]: (r1_tarski('#skF_7', C_150) | k1_xboole_0='#skF_8' | ~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_806])).
% 6.01/2.18  tff(c_823, plain, (![C_150]: (r1_tarski('#skF_7', C_150) | ~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_86, c_814])).
% 6.01/2.18  tff(c_829, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_823])).
% 6.01/2.18  tff(c_837, plain, (~r1_tarski('#skF_10', k1_xboole_0)), inference(resolution, [status(thm)], [c_376, c_829])).
% 6.01/2.18  tff(c_845, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_147, c_837])).
% 6.01/2.18  tff(c_64, plain, (![A_26, B_27, C_28, D_29]: (r2_hidden(k4_tarski(A_26, B_27), k2_zfmisc_1(C_28, D_29)) | ~r2_hidden(B_27, D_29) | ~r2_hidden(A_26, C_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.01/2.18  tff(c_438, plain, (![A_108, C_109, B_110, D_111]: (r2_hidden(A_108, C_109) | ~r2_hidden(k4_tarski(A_108, B_110), k2_zfmisc_1(C_109, D_111)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.01/2.18  tff(c_2633, plain, (![A_232, B_233]: (r2_hidden(A_232, '#skF_7') | ~r2_hidden(k4_tarski(A_232, B_233), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_438])).
% 6.01/2.18  tff(c_2638, plain, (![A_26, B_27]: (r2_hidden(A_26, '#skF_7') | ~r2_hidden(B_27, '#skF_10') | ~r2_hidden(A_26, '#skF_9'))), inference(resolution, [status(thm)], [c_64, c_2633])).
% 6.01/2.18  tff(c_2729, plain, (![B_246]: (~r2_hidden(B_246, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2638])).
% 6.01/2.18  tff(c_2761, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_2729])).
% 6.01/2.18  tff(c_2771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_845, c_2761])).
% 6.01/2.18  tff(c_2773, plain, (![A_247]: (r2_hidden(A_247, '#skF_7') | ~r2_hidden(A_247, '#skF_9'))), inference(splitRight, [status(thm)], [c_2638])).
% 6.01/2.18  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.01/2.18  tff(c_2786, plain, (![A_248]: (r1_tarski(A_248, '#skF_7') | ~r2_hidden('#skF_2'(A_248, '#skF_7'), '#skF_9'))), inference(resolution, [status(thm)], [c_2773, c_8])).
% 6.01/2.18  tff(c_2790, plain, (r1_tarski('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_2786])).
% 6.01/2.18  tff(c_2794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1753, c_1753, c_2790])).
% 6.01/2.18  tff(c_2795, plain, (![C_150]: (r1_tarski('#skF_7', C_150))), inference(splitRight, [status(thm)], [c_823])).
% 6.01/2.18  tff(c_74, plain, (![B_31]: (k2_zfmisc_1(k1_xboole_0, B_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.01/2.18  tff(c_568, plain, (![A_132, C_133, B_134]: (r1_tarski(k2_zfmisc_1(A_132, C_133), k2_zfmisc_1(B_134, C_133)) | ~r1_tarski(A_132, B_134))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.18  tff(c_630, plain, (![A_138, B_139]: (r1_tarski(k2_zfmisc_1(A_138, B_139), k1_xboole_0) | ~r1_tarski(A_138, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_74, c_568])).
% 6.01/2.18  tff(c_649, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k1_xboole_0) | ~r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_630])).
% 6.01/2.18  tff(c_700, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_649])).
% 6.01/2.18  tff(c_2800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2795, c_700])).
% 6.01/2.18  tff(c_2802, plain, (r1_tarski('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_784])).
% 6.01/2.18  tff(c_84, plain, ('#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.01/2.18  tff(c_94, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_84])).
% 6.01/2.18  tff(c_2801, plain, (k1_xboole_0='#skF_10' | r1_tarski('#skF_9', '#skF_7')), inference(splitRight, [status(thm)], [c_784])).
% 6.01/2.18  tff(c_2816, plain, (r1_tarski('#skF_9', '#skF_7')), inference(splitLeft, [status(thm)], [c_2801])).
% 6.01/2.18  tff(c_32, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.01/2.18  tff(c_2882, plain, ('#skF_7'='#skF_9' | ~r1_tarski('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_2816, c_32])).
% 6.01/2.18  tff(c_2888, plain, (~r1_tarski('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_94, c_2882])).
% 6.01/2.18  tff(c_36, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.01/2.18  tff(c_2815, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_2802, c_32])).
% 6.01/2.18  tff(c_2893, plain, (~r1_tarski('#skF_10', '#skF_8')), inference(splitLeft, [status(thm)], [c_2815])).
% 6.01/2.18  tff(c_635, plain, (![A_138, B_139]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_zfmisc_1(A_138, B_139)) | ~r1_tarski(A_138, k1_xboole_0))), inference(resolution, [status(thm)], [c_630, c_292])).
% 6.01/2.18  tff(c_659, plain, (![A_138, B_139]: (v1_xboole_0(k2_zfmisc_1(A_138, B_139)) | ~r1_tarski(A_138, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_635])).
% 6.01/2.18  tff(c_2817, plain, (![A_251, B_252, C_253]: (~r1_tarski(k2_zfmisc_1(A_251, B_252), k2_zfmisc_1(A_251, C_253)) | r1_tarski(B_252, C_253) | k1_xboole_0=A_251)), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.01/2.18  tff(c_3057, plain, (![B_265, C_266, A_267]: (r1_tarski(B_265, C_266) | k1_xboole_0=A_267 | ~v1_xboole_0(k2_zfmisc_1(A_267, B_265)))), inference(resolution, [status(thm)], [c_147, c_2817])).
% 6.01/2.18  tff(c_3065, plain, (![C_266]: (r1_tarski('#skF_8', C_266) | k1_xboole_0='#skF_7' | ~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_3057])).
% 6.01/2.18  tff(c_3074, plain, (![C_266]: (r1_tarski('#skF_8', C_266) | ~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_88, c_3065])).
% 6.01/2.18  tff(c_3080, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_3074])).
% 6.01/2.18  tff(c_3087, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_659, c_3080])).
% 6.01/2.18  tff(c_3093, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_147, c_3087])).
% 6.01/2.18  tff(c_264, plain, (![B_82, D_83, A_84, C_85]: (r2_hidden(B_82, D_83) | ~r2_hidden(k4_tarski(A_84, B_82), k2_zfmisc_1(C_85, D_83)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.01/2.18  tff(c_4484, plain, (![B_342, A_343]: (r2_hidden(B_342, '#skF_8') | ~r2_hidden(k4_tarski(A_343, B_342), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_264])).
% 6.01/2.18  tff(c_4489, plain, (![B_27, A_26]: (r2_hidden(B_27, '#skF_8') | ~r2_hidden(B_27, '#skF_10') | ~r2_hidden(A_26, '#skF_9'))), inference(resolution, [status(thm)], [c_64, c_4484])).
% 6.01/2.18  tff(c_5003, plain, (![A_369]: (~r2_hidden(A_369, '#skF_9'))), inference(splitLeft, [status(thm)], [c_4489])).
% 6.01/2.18  tff(c_5039, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_5003])).
% 6.01/2.18  tff(c_5050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3093, c_5039])).
% 6.01/2.18  tff(c_5063, plain, (![B_374]: (r2_hidden(B_374, '#skF_8') | ~r2_hidden(B_374, '#skF_10'))), inference(splitRight, [status(thm)], [c_4489])).
% 6.01/2.18  tff(c_5199, plain, (![B_379]: (r2_hidden('#skF_2'('#skF_10', B_379), '#skF_8') | r1_tarski('#skF_10', B_379))), inference(resolution, [status(thm)], [c_10, c_5063])).
% 6.01/2.18  tff(c_5205, plain, (r1_tarski('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_5199, c_8])).
% 6.01/2.18  tff(c_5213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2893, c_2893, c_5205])).
% 6.01/2.18  tff(c_5214, plain, (![C_266]: (r1_tarski('#skF_8', C_266))), inference(splitRight, [status(thm)], [c_3074])).
% 6.01/2.18  tff(c_367, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k1_xboole_0) | ~r1_tarski('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_353])).
% 6.01/2.18  tff(c_410, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_367])).
% 6.01/2.18  tff(c_5221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5214, c_410])).
% 6.01/2.18  tff(c_5222, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_2815])).
% 6.01/2.18  tff(c_333, plain, (![A_98]: (r1_tarski(k2_zfmisc_1('#skF_7', A_98), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r1_tarski(A_98, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_319])).
% 6.01/2.18  tff(c_6548, plain, (![A_459]: (r1_tarski(k2_zfmisc_1('#skF_7', A_459), k2_zfmisc_1('#skF_9', '#skF_8')) | ~r1_tarski(A_459, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5222, c_333])).
% 6.01/2.18  tff(c_78, plain, (![B_33, A_32, C_34]: (~r1_tarski(k2_zfmisc_1(B_33, A_32), k2_zfmisc_1(C_34, A_32)) | r1_tarski(B_33, C_34) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.01/2.18  tff(c_6556, plain, (r1_tarski('#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_6548, c_78])).
% 6.01/2.18  tff(c_6585, plain, (r1_tarski('#skF_7', '#skF_9') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6556])).
% 6.01/2.18  tff(c_6587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_2888, c_6585])).
% 6.01/2.18  tff(c_6588, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_2801])).
% 6.01/2.18  tff(c_6600, plain, (~r1_tarski('#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_6588, c_410])).
% 6.01/2.18  tff(c_6617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2802, c_6600])).
% 6.01/2.18  tff(c_6619, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_649])).
% 6.01/2.18  tff(c_160, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.01/2.18  tff(c_167, plain, (![B_58, A_57]: (B_58=A_57 | ~r1_tarski(B_58, A_57) | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_147, c_160])).
% 6.01/2.18  tff(c_6629, plain, (k1_xboole_0='#skF_7' | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6619, c_167])).
% 6.01/2.18  tff(c_6642, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6629])).
% 6.01/2.18  tff(c_6644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_6642])).
% 6.01/2.18  tff(c_6646, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_367])).
% 6.01/2.18  tff(c_6654, plain, (k1_xboole_0='#skF_8' | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6646, c_167])).
% 6.01/2.18  tff(c_6666, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6654])).
% 6.01/2.18  tff(c_6668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_6666])).
% 6.01/2.18  tff(c_6669, plain, ('#skF_10'!='#skF_8'), inference(splitRight, [status(thm)], [c_84])).
% 6.01/2.18  tff(c_6670, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 6.01/2.18  tff(c_6671, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6670, c_88])).
% 6.01/2.18  tff(c_6699, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6670, c_90])).
% 6.01/2.18  tff(c_7145, plain, (![A_551, C_552, B_553]: (r1_tarski(k2_zfmisc_1(A_551, C_552), k2_zfmisc_1(B_553, C_552)) | ~r1_tarski(A_551, B_553))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.01/2.18  tff(c_7162, plain, (![B_553]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_8'), k2_zfmisc_1(B_553, '#skF_10')) | ~r1_tarski('#skF_9', B_553))), inference(superposition, [status(thm), theory('equality')], [c_6699, c_7145])).
% 6.01/2.18  tff(c_7771, plain, (![A_585, B_586, C_587]: (~r1_tarski(k2_zfmisc_1(A_585, B_586), k2_zfmisc_1(A_585, C_587)) | r1_tarski(B_586, C_587) | k1_xboole_0=A_585)), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.01/2.18  tff(c_7775, plain, (r1_tarski('#skF_8', '#skF_10') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_7162, c_7771])).
% 6.01/2.18  tff(c_7844, plain, (r1_tarski('#skF_8', '#skF_10') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7775])).
% 6.01/2.18  tff(c_7845, plain, (r1_tarski('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_6671, c_7844])).
% 6.01/2.18  tff(c_7165, plain, (![A_551]: (r1_tarski(k2_zfmisc_1(A_551, '#skF_10'), k2_zfmisc_1('#skF_9', '#skF_8')) | ~r1_tarski(A_551, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6699, c_7145])).
% 6.01/2.18  tff(c_7800, plain, (r1_tarski('#skF_10', '#skF_8') | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_7165, c_7771])).
% 6.01/2.18  tff(c_7857, plain, (r1_tarski('#skF_10', '#skF_8') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7800])).
% 6.01/2.18  tff(c_7858, plain, (r1_tarski('#skF_10', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_6671, c_7857])).
% 6.01/2.18  tff(c_7902, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_7858, c_32])).
% 6.01/2.18  tff(c_7911, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7845, c_7902])).
% 6.01/2.18  tff(c_7913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6669, c_7911])).
% 6.01/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.18  
% 6.01/2.18  Inference rules
% 6.01/2.18  ----------------------
% 6.01/2.18  #Ref     : 0
% 6.01/2.18  #Sup     : 1803
% 6.01/2.18  #Fact    : 0
% 6.01/2.18  #Define  : 0
% 6.01/2.18  #Split   : 20
% 6.01/2.18  #Chain   : 0
% 6.01/2.18  #Close   : 0
% 6.01/2.18  
% 6.01/2.18  Ordering : KBO
% 6.01/2.18  
% 6.01/2.18  Simplification rules
% 6.01/2.18  ----------------------
% 6.01/2.18  #Subsume      : 554
% 6.01/2.18  #Demod        : 768
% 6.01/2.18  #Tautology    : 672
% 6.01/2.18  #SimpNegUnit  : 73
% 6.01/2.18  #BackRed      : 34
% 6.01/2.18  
% 6.01/2.18  #Partial instantiations: 0
% 6.01/2.18  #Strategies tried      : 1
% 6.01/2.18  
% 6.01/2.18  Timing (in seconds)
% 6.01/2.18  ----------------------
% 6.01/2.18  Preprocessing        : 0.33
% 6.01/2.18  Parsing              : 0.17
% 6.01/2.18  CNF conversion       : 0.03
% 6.01/2.18  Main loop            : 1.08
% 6.01/2.18  Inferencing          : 0.37
% 6.01/2.18  Reduction            : 0.34
% 6.01/2.18  Demodulation         : 0.23
% 6.01/2.18  BG Simplification    : 0.04
% 6.01/2.18  Subsumption          : 0.25
% 6.01/2.18  Abstraction          : 0.05
% 6.01/2.18  MUC search           : 0.00
% 6.01/2.18  Cooper               : 0.00
% 6.01/2.18  Total                : 1.46
% 6.01/2.18  Index Insertion      : 0.00
% 6.01/2.18  Index Deletion       : 0.00
% 6.01/2.18  Index Matching       : 0.00
% 6.01/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
