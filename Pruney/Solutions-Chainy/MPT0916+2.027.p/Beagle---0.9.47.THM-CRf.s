%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:14 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 657 expanded)
%              Number of leaves         :   32 ( 227 expanded)
%              Depth                    :   11
%              Number of atoms          :  341 (1884 expanded)
%              Number of equality atoms :   91 ( 413 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_40])).

tff(c_30,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k2_zfmisc_1(k2_zfmisc_1(A_13,B_14),C_15) = k3_zfmisc_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1116,plain,(
    ! [A_229,B_230,C_231] :
      ( r2_hidden(k1_mcart_1(A_229),B_230)
      | ~ r2_hidden(A_229,k2_zfmisc_1(B_230,C_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1583,plain,(
    ! [A_312,A_313,B_314,C_315] :
      ( r2_hidden(k1_mcart_1(A_312),k2_zfmisc_1(A_313,B_314))
      | ~ r2_hidden(A_312,k3_zfmisc_1(A_313,B_314,C_315)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1116])).

tff(c_1597,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_1583])).

tff(c_18,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(k2_mcart_1(A_16),C_18)
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1603,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1597,c_18])).

tff(c_1071,plain,(
    ! [A_221,B_222,C_223] : k2_zfmisc_1(k2_zfmisc_1(A_221,B_222),C_223) = k3_zfmisc_1(A_221,B_222,C_223) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1127,plain,(
    ! [A_232,C_233,A_234,B_235] :
      ( r2_hidden(k2_mcart_1(A_232),C_233)
      | ~ r2_hidden(A_232,k3_zfmisc_1(A_234,B_235,C_233)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_18])).

tff(c_1138,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_1127])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_51,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_40])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1229,plain,(
    ! [A_252,B_253,C_254,D_255] :
      ( k7_mcart_1(A_252,B_253,C_254,D_255) = k2_mcart_1(D_255)
      | ~ m1_subset_1(D_255,k3_zfmisc_1(A_252,B_253,C_254))
      | k1_xboole_0 = C_254
      | k1_xboole_0 = B_253
      | k1_xboole_0 = A_252 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1233,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_1229])).

tff(c_1309,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1233])).

tff(c_28,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_53,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_93,plain,(
    ! [A_55,B_56,C_57] : k2_zfmisc_1(k2_zfmisc_1(A_55,B_56),C_57) = k3_zfmisc_1(A_55,B_56,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(k1_mcart_1(A_16),B_17)
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_870,plain,(
    ! [A_195,A_196,B_197,C_198] :
      ( r2_hidden(k1_mcart_1(A_195),k2_zfmisc_1(A_196,B_197))
      | ~ r2_hidden(A_195,k3_zfmisc_1(A_196,B_197,C_198)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_20])).

tff(c_884,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_870])).

tff(c_896,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_884,c_18])).

tff(c_588,plain,(
    ! [A_152,A_153,B_154,C_155] :
      ( r2_hidden(k1_mcart_1(A_152),k2_zfmisc_1(A_153,B_154))
      | ~ r2_hidden(A_152,k3_zfmisc_1(A_153,B_154,C_155)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_20])).

tff(c_602,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_588])).

tff(c_610,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_602,c_20])).

tff(c_230,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k7_mcart_1(A_84,B_85,C_86,D_87) = k2_mcart_1(D_87)
      | ~ m1_subset_1(D_87,k3_zfmisc_1(A_84,B_85,C_86))
      | k1_xboole_0 = C_86
      | k1_xboole_0 = B_85
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_234,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_230])).

tff(c_308,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_141,plain,(
    ! [A_65,C_66,B_67,D_68] :
      ( r1_xboole_0(A_65,C_66)
      | ~ r1_xboole_0(B_67,D_68)
      | ~ r1_tarski(C_66,D_68)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_148,plain,(
    ! [A_69,C_70,A_71] :
      ( r1_xboole_0(A_69,C_70)
      | ~ r1_tarski(C_70,k1_xboole_0)
      | ~ r1_tarski(A_69,A_71) ) ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_172,plain,(
    ! [C_74] :
      ( r1_xboole_0('#skF_5',C_74)
      | ~ r1_tarski(C_74,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_51,c_148])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_207,plain,(
    ! [C_79,C_80] :
      ( ~ r2_hidden(C_79,C_80)
      | ~ r2_hidden(C_79,'#skF_5')
      | ~ r1_tarski(C_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_297,plain,(
    ! [A_102,B_103] :
      ( ~ r2_hidden('#skF_1'(A_102,B_103),'#skF_5')
      | ~ r1_tarski(B_103,k1_xboole_0)
      | r1_xboole_0(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_4,c_207])).

tff(c_307,plain,(
    ! [A_1] :
      ( ~ r1_tarski('#skF_5',k1_xboole_0)
      | r1_xboole_0(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4,c_297])).

tff(c_389,plain,(
    ! [A_115] : r1_xboole_0(A_115,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_308,c_307])).

tff(c_395,plain,(
    ! [C_5,A_115] :
      ( ~ r2_hidden(C_5,'#skF_5')
      | ~ r2_hidden(C_5,A_115) ) ),
    inference(resolution,[status(thm)],[c_389,c_2])).

tff(c_617,plain,(
    ! [A_115] : ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),A_115) ),
    inference(resolution,[status(thm)],[c_610,c_395])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_617,c_610])).

tff(c_630,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_278,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k5_mcart_1(A_95,B_96,C_97,D_98) = k1_mcart_1(k1_mcart_1(D_98))
      | ~ m1_subset_1(D_98,k3_zfmisc_1(A_95,B_96,C_97))
      | k1_xboole_0 = C_97
      | k1_xboole_0 = B_96
      | k1_xboole_0 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_282,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_278])).

tff(c_655,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_282])).

tff(c_656,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_158,plain,(
    ! [C_72] :
      ( r1_xboole_0('#skF_6',C_72)
      | ~ r1_tarski(C_72,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_148])).

tff(c_194,plain,(
    ! [C_77,C_78] :
      ( ~ r2_hidden(C_77,C_78)
      | ~ r2_hidden(C_77,'#skF_6')
      | ~ r1_tarski(C_78,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_158,c_2])).

tff(c_644,plain,(
    ! [A_160,B_161] :
      ( ~ r2_hidden('#skF_1'(A_160,B_161),'#skF_6')
      | ~ r1_tarski(B_161,k1_xboole_0)
      | r1_xboole_0(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_654,plain,(
    ! [A_1] :
      ( ~ r1_tarski('#skF_6',k1_xboole_0)
      | r1_xboole_0(A_1,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_644])).

tff(c_734,plain,(
    ! [A_169] : r1_xboole_0(A_169,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_656,c_654])).

tff(c_740,plain,(
    ! [C_5,A_169] :
      ( ~ r2_hidden(C_5,'#skF_6')
      | ~ r2_hidden(C_5,A_169) ) ),
    inference(resolution,[status(thm)],[c_734,c_2])).

tff(c_917,plain,(
    ! [A_169] : ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),A_169) ),
    inference(resolution,[status(thm)],[c_896,c_740])).

tff(c_919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_917,c_896])).

tff(c_920,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_923,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_920])).

tff(c_999,plain,(
    ! [A_205,A_206,B_207,C_208] :
      ( r2_hidden(k1_mcart_1(A_205),k2_zfmisc_1(A_206,B_207))
      | ~ r2_hidden(A_205,k3_zfmisc_1(A_206,B_207,C_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_20])).

tff(c_1010,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_999])).

tff(c_1012,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1010,c_20])).

tff(c_1016,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_1012])).

tff(c_1018,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1016])).

tff(c_1019,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_129,plain,(
    ! [A_61,C_62,A_63,B_64] :
      ( r2_hidden(k2_mcart_1(A_61),C_62)
      | ~ r2_hidden(A_61,k3_zfmisc_1(A_63,B_64,C_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_18])).

tff(c_140,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_129])).

tff(c_165,plain,(
    ! [C_73] :
      ( r1_xboole_0('#skF_7',C_73)
      | ~ r1_tarski(C_73,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_148])).

tff(c_179,plain,(
    ! [C_75,C_76] :
      ( ~ r2_hidden(C_75,C_76)
      | ~ r2_hidden(C_75,'#skF_7')
      | ~ r1_tarski(C_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_181,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7')
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_140,c_179])).

tff(c_190,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_181])).

tff(c_1038,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_190])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1038])).

tff(c_1050,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1139,plain,(
    ! [A_236,C_237,B_238,D_239] :
      ( r1_xboole_0(A_236,C_237)
      | ~ r1_xboole_0(B_238,D_239)
      | ~ r1_tarski(C_237,D_239)
      | ~ r1_tarski(A_236,B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1146,plain,(
    ! [A_240,C_241,A_242] :
      ( r1_xboole_0(A_240,C_241)
      | ~ r1_tarski(C_241,k1_xboole_0)
      | ~ r1_tarski(A_240,A_242) ) ),
    inference(resolution,[status(thm)],[c_10,c_1139])).

tff(c_1170,plain,(
    ! [C_245] :
      ( r1_xboole_0('#skF_5',C_245)
      | ~ r1_tarski(C_245,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_51,c_1146])).

tff(c_1211,plain,(
    ! [C_250,C_251] :
      ( ~ r2_hidden(C_250,C_251)
      | ~ r2_hidden(C_250,'#skF_5')
      | ~ r1_tarski(C_251,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1170,c_2])).

tff(c_1219,plain,
    ( ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5')
    | ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1050,c_1211])).

tff(c_1227,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1219])).

tff(c_1321,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_1227])).

tff(c_1332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_1321])).

tff(c_1333,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1233])).

tff(c_1347,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1333])).

tff(c_1049,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1114,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1049])).

tff(c_1348,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_1114])).

tff(c_1351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_1348])).

tff(c_1352,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1333])).

tff(c_1354,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1352])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1067,plain,(
    ! [A_218,B_219,C_220] :
      ( ~ r1_xboole_0(A_218,B_219)
      | ~ r2_hidden(C_220,B_219)
      | ~ r2_hidden(C_220,A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1088,plain,(
    ! [C_224,A_225] :
      ( ~ r2_hidden(C_224,k1_xboole_0)
      | ~ r2_hidden(C_224,A_225) ) ),
    inference(resolution,[status(thm)],[c_10,c_1067])).

tff(c_1098,plain,(
    ! [B_226,A_227] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_226),A_227)
      | r1_xboole_0(k1_xboole_0,B_226) ) ),
    inference(resolution,[status(thm)],[c_6,c_1088])).

tff(c_1107,plain,(
    ! [B_2] : r1_xboole_0(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1098])).

tff(c_1235,plain,(
    ! [A_256,C_257,B_258] :
      ( r1_xboole_0(A_256,C_257)
      | ~ r1_tarski(C_257,B_258)
      | ~ r1_tarski(A_256,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1107,c_1139])).

tff(c_1242,plain,(
    ! [A_256] :
      ( r1_xboole_0(A_256,'#skF_6')
      | ~ r1_tarski(A_256,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_1235])).

tff(c_1439,plain,(
    ! [A_286] :
      ( r1_xboole_0(A_286,'#skF_6')
      | ~ r1_tarski(A_286,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_1242])).

tff(c_1445,plain,(
    ! [C_5,A_286] :
      ( ~ r2_hidden(C_5,'#skF_6')
      | ~ r2_hidden(C_5,A_286)
      | ~ r1_tarski(A_286,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1439,c_2])).

tff(c_1615,plain,(
    ! [A_317] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),A_317)
      | ~ r1_tarski(A_317,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1603,c_1445])).

tff(c_1618,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1603,c_1615])).

tff(c_1622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1618])).

tff(c_1623,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1352])).

tff(c_1163,plain,(
    ! [C_244] :
      ( r1_xboole_0('#skF_7',C_244)
      | ~ r1_tarski(C_244,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_1146])).

tff(c_1177,plain,(
    ! [C_246,C_247] :
      ( ~ r2_hidden(C_246,C_247)
      | ~ r2_hidden(C_246,'#skF_7')
      | ~ r1_tarski(C_247,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1163,c_2])).

tff(c_1179,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7')
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1138,c_1177])).

tff(c_1190,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_1179])).

tff(c_1641,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1190])).

tff(c_1651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1641])).

tff(c_1652,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1049])).

tff(c_1655,plain,(
    ! [A_318,B_319,C_320] :
      ( r2_hidden(k1_mcart_1(A_318),B_319)
      | ~ r2_hidden(A_318,k2_zfmisc_1(B_319,C_320)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2142,plain,(
    ! [A_399,A_400,B_401,C_402] :
      ( r2_hidden(k1_mcart_1(A_399),k2_zfmisc_1(A_400,B_401))
      | ~ r2_hidden(A_399,k3_zfmisc_1(A_400,B_401,C_402)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1655])).

tff(c_2153,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_2142])).

tff(c_2167,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2153,c_18])).

tff(c_1735,plain,(
    ! [A_337,B_338,C_339,D_340] :
      ( k7_mcart_1(A_337,B_338,C_339,D_340) = k2_mcart_1(D_340)
      | ~ m1_subset_1(D_340,k3_zfmisc_1(A_337,B_338,C_339))
      | k1_xboole_0 = C_339
      | k1_xboole_0 = B_338
      | k1_xboole_0 = A_337 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1739,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_1735])).

tff(c_1822,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1739])).

tff(c_1678,plain,(
    ! [A_325,C_326,B_327,D_328] :
      ( r1_xboole_0(A_325,C_326)
      | ~ r1_xboole_0(B_327,D_328)
      | ~ r1_tarski(C_326,D_328)
      | ~ r1_tarski(A_325,B_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1685,plain,(
    ! [A_329,C_330,A_331] :
      ( r1_xboole_0(A_329,C_330)
      | ~ r1_tarski(C_330,k1_xboole_0)
      | ~ r1_tarski(A_329,A_331) ) ),
    inference(resolution,[status(thm)],[c_10,c_1678])).

tff(c_1709,plain,(
    ! [C_334] :
      ( r1_xboole_0('#skF_5',C_334)
      | ~ r1_tarski(C_334,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_51,c_1685])).

tff(c_1741,plain,(
    ! [C_341,C_342] :
      ( ~ r2_hidden(C_341,C_342)
      | ~ r2_hidden(C_341,'#skF_5')
      | ~ r1_tarski(C_342,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1709,c_2])).

tff(c_1751,plain,
    ( ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5')
    | ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1050,c_1741])).

tff(c_1760,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1751])).

tff(c_1830,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_1760])).

tff(c_1844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_1830])).

tff(c_1846,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1739])).

tff(c_1803,plain,(
    ! [A_349,B_350,C_351,D_352] :
      ( k5_mcart_1(A_349,B_350,C_351,D_352) = k1_mcart_1(k1_mcart_1(D_352))
      | ~ m1_subset_1(D_352,k3_zfmisc_1(A_349,B_350,C_351))
      | k1_xboole_0 = C_351
      | k1_xboole_0 = B_350
      | k1_xboole_0 = A_349 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1807,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_1803])).

tff(c_1895,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1846,c_1807])).

tff(c_1896,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1895])).

tff(c_1695,plain,(
    ! [C_332] :
      ( r1_xboole_0('#skF_6',C_332)
      | ~ r1_tarski(C_332,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_1685])).

tff(c_1716,plain,(
    ! [C_335,C_336] :
      ( ~ r2_hidden(C_335,C_336)
      | ~ r2_hidden(C_335,'#skF_6')
      | ~ r1_tarski(C_336,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1695,c_2])).

tff(c_1731,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),'#skF_6')
      | ~ r1_tarski(A_1,k1_xboole_0)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1716])).

tff(c_2129,plain,(
    ! [A_397,B_398] :
      ( ~ r2_hidden('#skF_1'(A_397,B_398),'#skF_6')
      | ~ r1_tarski(A_397,'#skF_3')
      | r1_xboole_0(A_397,B_398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_1731])).

tff(c_2133,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_6','#skF_3')
      | r1_xboole_0('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_2129])).

tff(c_2155,plain,(
    ! [B_403] : r1_xboole_0('#skF_6',B_403) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2133])).

tff(c_2174,plain,(
    ! [C_404,B_405] :
      ( ~ r2_hidden(C_404,B_405)
      | ~ r2_hidden(C_404,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2155,c_2])).

tff(c_2176,plain,(
    ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2167,c_2174])).

tff(c_2196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2176])).

tff(c_2198,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1895])).

tff(c_1876,plain,(
    ! [A_360,B_361,C_362,D_363] :
      ( k6_mcart_1(A_360,B_361,C_362,D_363) = k2_mcart_1(k1_mcart_1(D_363))
      | ~ m1_subset_1(D_363,k3_zfmisc_1(A_360,B_361,C_362))
      | k1_xboole_0 = C_362
      | k1_xboole_0 = B_361
      | k1_xboole_0 = A_360 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1879,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_1876])).

tff(c_1882,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1846,c_1879])).

tff(c_2229,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2198,c_1882])).

tff(c_2230,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2229])).

tff(c_1666,plain,(
    ! [A_321,C_322,A_323,B_324] :
      ( r2_hidden(k2_mcart_1(A_321),C_322)
      | ~ r2_hidden(A_321,k3_zfmisc_1(A_323,B_324,C_322)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_18])).

tff(c_1677,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_1666])).

tff(c_1729,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_6')
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1677,c_1716])).

tff(c_1740,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1729])).

tff(c_2247,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_1740])).

tff(c_2258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2247])).

tff(c_2259,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2229])).

tff(c_2287,plain,(
    ! [A_413,A_414,B_415,C_416] :
      ( r2_hidden(k1_mcart_1(A_413),k2_zfmisc_1(A_414,B_415))
      | ~ r2_hidden(A_413,k3_zfmisc_1(A_414,B_415,C_416)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1655])).

tff(c_2298,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_2287])).

tff(c_2302,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2298,c_18])).

tff(c_2306,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2259,c_2302])).

tff(c_2308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1652,c_2306])).

tff(c_2310,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1729])).

tff(c_1702,plain,(
    ! [C_333] :
      ( r1_xboole_0('#skF_7',C_333)
      | ~ r1_tarski(C_333,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_1685])).

tff(c_2345,plain,(
    ! [C_423,C_424] :
      ( ~ r2_hidden(C_423,C_424)
      | ~ r2_hidden(C_423,'#skF_7')
      | ~ r1_tarski(C_424,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1702,c_2])).

tff(c_2347,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7')
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1677,c_2345])).

tff(c_2361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_1677,c_2347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.82  
% 4.67/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.67/1.82  
% 4.67/1.82  %Foreground sorts:
% 4.67/1.82  
% 4.67/1.82  
% 4.67/1.82  %Background operators:
% 4.67/1.82  
% 4.67/1.82  
% 4.67/1.82  %Foreground operators:
% 4.67/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.67/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.67/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.67/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.67/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.67/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.82  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.67/1.82  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.67/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.67/1.82  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.67/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.82  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.67/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.67/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.67/1.82  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.67/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.82  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.67/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.67/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.82  
% 4.77/1.85  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 4.77/1.85  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.77/1.85  tff(f_59, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.77/1.85  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.77/1.85  tff(f_85, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.77/1.85  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.77/1.85  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.77/1.85  tff(f_51, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 4.77/1.85  tff(c_34, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.77/1.85  tff(c_40, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.77/1.85  tff(c_50, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_40])).
% 4.77/1.85  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.77/1.85  tff(c_52, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_40])).
% 4.77/1.85  tff(c_30, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.77/1.85  tff(c_16, plain, (![A_13, B_14, C_15]: (k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), C_15)=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.77/1.85  tff(c_1116, plain, (![A_229, B_230, C_231]: (r2_hidden(k1_mcart_1(A_229), B_230) | ~r2_hidden(A_229, k2_zfmisc_1(B_230, C_231)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.77/1.85  tff(c_1583, plain, (![A_312, A_313, B_314, C_315]: (r2_hidden(k1_mcart_1(A_312), k2_zfmisc_1(A_313, B_314)) | ~r2_hidden(A_312, k3_zfmisc_1(A_313, B_314, C_315)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1116])).
% 4.77/1.85  tff(c_1597, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_1583])).
% 4.77/1.85  tff(c_18, plain, (![A_16, C_18, B_17]: (r2_hidden(k2_mcart_1(A_16), C_18) | ~r2_hidden(A_16, k2_zfmisc_1(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.77/1.85  tff(c_1603, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1597, c_18])).
% 4.77/1.85  tff(c_1071, plain, (![A_221, B_222, C_223]: (k2_zfmisc_1(k2_zfmisc_1(A_221, B_222), C_223)=k3_zfmisc_1(A_221, B_222, C_223))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.77/1.85  tff(c_1127, plain, (![A_232, C_233, A_234, B_235]: (r2_hidden(k2_mcart_1(A_232), C_233) | ~r2_hidden(A_232, k3_zfmisc_1(A_234, B_235, C_233)))), inference(superposition, [status(thm), theory('equality')], [c_1071, c_18])).
% 4.77/1.85  tff(c_1138, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_30, c_1127])).
% 4.77/1.85  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.77/1.85  tff(c_51, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_40])).
% 4.77/1.85  tff(c_32, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.77/1.85  tff(c_1229, plain, (![A_252, B_253, C_254, D_255]: (k7_mcart_1(A_252, B_253, C_254, D_255)=k2_mcart_1(D_255) | ~m1_subset_1(D_255, k3_zfmisc_1(A_252, B_253, C_254)) | k1_xboole_0=C_254 | k1_xboole_0=B_253 | k1_xboole_0=A_252)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.85  tff(c_1233, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_1229])).
% 4.77/1.85  tff(c_1309, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1233])).
% 4.77/1.85  tff(c_28, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.77/1.85  tff(c_53, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_28])).
% 4.77/1.85  tff(c_93, plain, (![A_55, B_56, C_57]: (k2_zfmisc_1(k2_zfmisc_1(A_55, B_56), C_57)=k3_zfmisc_1(A_55, B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.77/1.85  tff(c_20, plain, (![A_16, B_17, C_18]: (r2_hidden(k1_mcart_1(A_16), B_17) | ~r2_hidden(A_16, k2_zfmisc_1(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.77/1.85  tff(c_870, plain, (![A_195, A_196, B_197, C_198]: (r2_hidden(k1_mcart_1(A_195), k2_zfmisc_1(A_196, B_197)) | ~r2_hidden(A_195, k3_zfmisc_1(A_196, B_197, C_198)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_20])).
% 4.77/1.85  tff(c_884, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_870])).
% 4.77/1.85  tff(c_896, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_884, c_18])).
% 4.77/1.85  tff(c_588, plain, (![A_152, A_153, B_154, C_155]: (r2_hidden(k1_mcart_1(A_152), k2_zfmisc_1(A_153, B_154)) | ~r2_hidden(A_152, k3_zfmisc_1(A_153, B_154, C_155)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_20])).
% 4.77/1.85  tff(c_602, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_588])).
% 4.77/1.85  tff(c_610, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_602, c_20])).
% 4.77/1.85  tff(c_230, plain, (![A_84, B_85, C_86, D_87]: (k7_mcart_1(A_84, B_85, C_86, D_87)=k2_mcart_1(D_87) | ~m1_subset_1(D_87, k3_zfmisc_1(A_84, B_85, C_86)) | k1_xboole_0=C_86 | k1_xboole_0=B_85 | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.85  tff(c_234, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_230])).
% 4.77/1.85  tff(c_308, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_234])).
% 4.77/1.85  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.85  tff(c_10, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.77/1.85  tff(c_141, plain, (![A_65, C_66, B_67, D_68]: (r1_xboole_0(A_65, C_66) | ~r1_xboole_0(B_67, D_68) | ~r1_tarski(C_66, D_68) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.77/1.85  tff(c_148, plain, (![A_69, C_70, A_71]: (r1_xboole_0(A_69, C_70) | ~r1_tarski(C_70, k1_xboole_0) | ~r1_tarski(A_69, A_71))), inference(resolution, [status(thm)], [c_10, c_141])).
% 4.77/1.85  tff(c_172, plain, (![C_74]: (r1_xboole_0('#skF_5', C_74) | ~r1_tarski(C_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_51, c_148])).
% 4.77/1.85  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.85  tff(c_207, plain, (![C_79, C_80]: (~r2_hidden(C_79, C_80) | ~r2_hidden(C_79, '#skF_5') | ~r1_tarski(C_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_172, c_2])).
% 4.77/1.85  tff(c_297, plain, (![A_102, B_103]: (~r2_hidden('#skF_1'(A_102, B_103), '#skF_5') | ~r1_tarski(B_103, k1_xboole_0) | r1_xboole_0(A_102, B_103))), inference(resolution, [status(thm)], [c_4, c_207])).
% 4.77/1.85  tff(c_307, plain, (![A_1]: (~r1_tarski('#skF_5', k1_xboole_0) | r1_xboole_0(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_297])).
% 4.77/1.85  tff(c_389, plain, (![A_115]: (r1_xboole_0(A_115, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_308, c_307])).
% 4.77/1.85  tff(c_395, plain, (![C_5, A_115]: (~r2_hidden(C_5, '#skF_5') | ~r2_hidden(C_5, A_115))), inference(resolution, [status(thm)], [c_389, c_2])).
% 4.77/1.85  tff(c_617, plain, (![A_115]: (~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), A_115))), inference(resolution, [status(thm)], [c_610, c_395])).
% 4.77/1.85  tff(c_628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_617, c_610])).
% 4.77/1.85  tff(c_630, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_234])).
% 4.77/1.85  tff(c_278, plain, (![A_95, B_96, C_97, D_98]: (k5_mcart_1(A_95, B_96, C_97, D_98)=k1_mcart_1(k1_mcart_1(D_98)) | ~m1_subset_1(D_98, k3_zfmisc_1(A_95, B_96, C_97)) | k1_xboole_0=C_97 | k1_xboole_0=B_96 | k1_xboole_0=A_95)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.85  tff(c_282, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_278])).
% 4.77/1.85  tff(c_655, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_630, c_282])).
% 4.77/1.85  tff(c_656, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_655])).
% 4.77/1.85  tff(c_158, plain, (![C_72]: (r1_xboole_0('#skF_6', C_72) | ~r1_tarski(C_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_148])).
% 4.77/1.85  tff(c_194, plain, (![C_77, C_78]: (~r2_hidden(C_77, C_78) | ~r2_hidden(C_77, '#skF_6') | ~r1_tarski(C_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_158, c_2])).
% 4.77/1.85  tff(c_644, plain, (![A_160, B_161]: (~r2_hidden('#skF_1'(A_160, B_161), '#skF_6') | ~r1_tarski(B_161, k1_xboole_0) | r1_xboole_0(A_160, B_161))), inference(resolution, [status(thm)], [c_4, c_194])).
% 4.77/1.85  tff(c_654, plain, (![A_1]: (~r1_tarski('#skF_6', k1_xboole_0) | r1_xboole_0(A_1, '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_644])).
% 4.77/1.85  tff(c_734, plain, (![A_169]: (r1_xboole_0(A_169, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_656, c_654])).
% 4.77/1.85  tff(c_740, plain, (![C_5, A_169]: (~r2_hidden(C_5, '#skF_6') | ~r2_hidden(C_5, A_169))), inference(resolution, [status(thm)], [c_734, c_2])).
% 4.77/1.85  tff(c_917, plain, (![A_169]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), A_169))), inference(resolution, [status(thm)], [c_896, c_740])).
% 4.77/1.85  tff(c_919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_917, c_896])).
% 4.77/1.85  tff(c_920, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_655])).
% 4.77/1.85  tff(c_923, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_920])).
% 4.77/1.85  tff(c_999, plain, (![A_205, A_206, B_207, C_208]: (r2_hidden(k1_mcart_1(A_205), k2_zfmisc_1(A_206, B_207)) | ~r2_hidden(A_205, k3_zfmisc_1(A_206, B_207, C_208)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_20])).
% 4.77/1.85  tff(c_1010, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_999])).
% 4.77/1.85  tff(c_1012, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_1010, c_20])).
% 4.77/1.85  tff(c_1016, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_923, c_1012])).
% 4.77/1.85  tff(c_1018, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1016])).
% 4.77/1.85  tff(c_1019, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_920])).
% 4.77/1.85  tff(c_129, plain, (![A_61, C_62, A_63, B_64]: (r2_hidden(k2_mcart_1(A_61), C_62) | ~r2_hidden(A_61, k3_zfmisc_1(A_63, B_64, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_18])).
% 4.77/1.85  tff(c_140, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_30, c_129])).
% 4.77/1.85  tff(c_165, plain, (![C_73]: (r1_xboole_0('#skF_7', C_73) | ~r1_tarski(C_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_148])).
% 4.77/1.85  tff(c_179, plain, (![C_75, C_76]: (~r2_hidden(C_75, C_76) | ~r2_hidden(C_75, '#skF_7') | ~r1_tarski(C_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_165, c_2])).
% 4.77/1.85  tff(c_181, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7') | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_140, c_179])).
% 4.77/1.85  tff(c_190, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_181])).
% 4.77/1.85  tff(c_1038, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_190])).
% 4.77/1.85  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1038])).
% 4.77/1.85  tff(c_1050, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 4.77/1.85  tff(c_1139, plain, (![A_236, C_237, B_238, D_239]: (r1_xboole_0(A_236, C_237) | ~r1_xboole_0(B_238, D_239) | ~r1_tarski(C_237, D_239) | ~r1_tarski(A_236, B_238))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.77/1.85  tff(c_1146, plain, (![A_240, C_241, A_242]: (r1_xboole_0(A_240, C_241) | ~r1_tarski(C_241, k1_xboole_0) | ~r1_tarski(A_240, A_242))), inference(resolution, [status(thm)], [c_10, c_1139])).
% 4.77/1.85  tff(c_1170, plain, (![C_245]: (r1_xboole_0('#skF_5', C_245) | ~r1_tarski(C_245, k1_xboole_0))), inference(resolution, [status(thm)], [c_51, c_1146])).
% 4.77/1.85  tff(c_1211, plain, (![C_250, C_251]: (~r2_hidden(C_250, C_251) | ~r2_hidden(C_250, '#skF_5') | ~r1_tarski(C_251, k1_xboole_0))), inference(resolution, [status(thm)], [c_1170, c_2])).
% 4.77/1.85  tff(c_1219, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5') | ~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_1050, c_1211])).
% 4.77/1.85  tff(c_1227, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1219])).
% 4.77/1.85  tff(c_1321, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1309, c_1227])).
% 4.77/1.85  tff(c_1332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_1321])).
% 4.77/1.85  tff(c_1333, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_1233])).
% 4.77/1.85  tff(c_1347, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1333])).
% 4.77/1.85  tff(c_1049, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_28])).
% 4.77/1.85  tff(c_1114, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1049])).
% 4.77/1.85  tff(c_1348, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_1114])).
% 4.77/1.85  tff(c_1351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1138, c_1348])).
% 4.77/1.85  tff(c_1352, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1333])).
% 4.77/1.85  tff(c_1354, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1352])).
% 4.77/1.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.85  tff(c_1067, plain, (![A_218, B_219, C_220]: (~r1_xboole_0(A_218, B_219) | ~r2_hidden(C_220, B_219) | ~r2_hidden(C_220, A_218))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.85  tff(c_1088, plain, (![C_224, A_225]: (~r2_hidden(C_224, k1_xboole_0) | ~r2_hidden(C_224, A_225))), inference(resolution, [status(thm)], [c_10, c_1067])).
% 4.77/1.85  tff(c_1098, plain, (![B_226, A_227]: (~r2_hidden('#skF_1'(k1_xboole_0, B_226), A_227) | r1_xboole_0(k1_xboole_0, B_226))), inference(resolution, [status(thm)], [c_6, c_1088])).
% 4.77/1.85  tff(c_1107, plain, (![B_2]: (r1_xboole_0(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_1098])).
% 4.77/1.85  tff(c_1235, plain, (![A_256, C_257, B_258]: (r1_xboole_0(A_256, C_257) | ~r1_tarski(C_257, B_258) | ~r1_tarski(A_256, k1_xboole_0))), inference(resolution, [status(thm)], [c_1107, c_1139])).
% 4.77/1.85  tff(c_1242, plain, (![A_256]: (r1_xboole_0(A_256, '#skF_6') | ~r1_tarski(A_256, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_1235])).
% 4.77/1.85  tff(c_1439, plain, (![A_286]: (r1_xboole_0(A_286, '#skF_6') | ~r1_tarski(A_286, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1354, c_1242])).
% 4.77/1.85  tff(c_1445, plain, (![C_5, A_286]: (~r2_hidden(C_5, '#skF_6') | ~r2_hidden(C_5, A_286) | ~r1_tarski(A_286, '#skF_3'))), inference(resolution, [status(thm)], [c_1439, c_2])).
% 4.77/1.85  tff(c_1615, plain, (![A_317]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), A_317) | ~r1_tarski(A_317, '#skF_3'))), inference(resolution, [status(thm)], [c_1603, c_1445])).
% 4.77/1.85  tff(c_1618, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1603, c_1615])).
% 4.77/1.85  tff(c_1622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1618])).
% 4.77/1.85  tff(c_1623, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1352])).
% 4.77/1.85  tff(c_1163, plain, (![C_244]: (r1_xboole_0('#skF_7', C_244) | ~r1_tarski(C_244, k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_1146])).
% 4.77/1.85  tff(c_1177, plain, (![C_246, C_247]: (~r2_hidden(C_246, C_247) | ~r2_hidden(C_246, '#skF_7') | ~r1_tarski(C_247, k1_xboole_0))), inference(resolution, [status(thm)], [c_1163, c_2])).
% 4.77/1.85  tff(c_1179, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7') | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_1138, c_1177])).
% 4.77/1.85  tff(c_1190, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_1179])).
% 4.77/1.85  tff(c_1641, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1190])).
% 4.77/1.85  tff(c_1651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1641])).
% 4.77/1.85  tff(c_1652, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_1049])).
% 4.77/1.85  tff(c_1655, plain, (![A_318, B_319, C_320]: (r2_hidden(k1_mcart_1(A_318), B_319) | ~r2_hidden(A_318, k2_zfmisc_1(B_319, C_320)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.77/1.85  tff(c_2142, plain, (![A_399, A_400, B_401, C_402]: (r2_hidden(k1_mcart_1(A_399), k2_zfmisc_1(A_400, B_401)) | ~r2_hidden(A_399, k3_zfmisc_1(A_400, B_401, C_402)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1655])).
% 4.77/1.85  tff(c_2153, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_2142])).
% 4.77/1.85  tff(c_2167, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2153, c_18])).
% 4.77/1.85  tff(c_1735, plain, (![A_337, B_338, C_339, D_340]: (k7_mcart_1(A_337, B_338, C_339, D_340)=k2_mcart_1(D_340) | ~m1_subset_1(D_340, k3_zfmisc_1(A_337, B_338, C_339)) | k1_xboole_0=C_339 | k1_xboole_0=B_338 | k1_xboole_0=A_337)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.85  tff(c_1739, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_1735])).
% 4.77/1.85  tff(c_1822, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1739])).
% 4.77/1.85  tff(c_1678, plain, (![A_325, C_326, B_327, D_328]: (r1_xboole_0(A_325, C_326) | ~r1_xboole_0(B_327, D_328) | ~r1_tarski(C_326, D_328) | ~r1_tarski(A_325, B_327))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.77/1.85  tff(c_1685, plain, (![A_329, C_330, A_331]: (r1_xboole_0(A_329, C_330) | ~r1_tarski(C_330, k1_xboole_0) | ~r1_tarski(A_329, A_331))), inference(resolution, [status(thm)], [c_10, c_1678])).
% 4.77/1.85  tff(c_1709, plain, (![C_334]: (r1_xboole_0('#skF_5', C_334) | ~r1_tarski(C_334, k1_xboole_0))), inference(resolution, [status(thm)], [c_51, c_1685])).
% 4.77/1.85  tff(c_1741, plain, (![C_341, C_342]: (~r2_hidden(C_341, C_342) | ~r2_hidden(C_341, '#skF_5') | ~r1_tarski(C_342, k1_xboole_0))), inference(resolution, [status(thm)], [c_1709, c_2])).
% 4.77/1.85  tff(c_1751, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5') | ~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_1050, c_1741])).
% 4.77/1.85  tff(c_1760, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1751])).
% 4.77/1.85  tff(c_1830, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1822, c_1760])).
% 4.77/1.85  tff(c_1844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_1830])).
% 4.77/1.85  tff(c_1846, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1739])).
% 4.77/1.85  tff(c_1803, plain, (![A_349, B_350, C_351, D_352]: (k5_mcart_1(A_349, B_350, C_351, D_352)=k1_mcart_1(k1_mcart_1(D_352)) | ~m1_subset_1(D_352, k3_zfmisc_1(A_349, B_350, C_351)) | k1_xboole_0=C_351 | k1_xboole_0=B_350 | k1_xboole_0=A_349)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.85  tff(c_1807, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_1803])).
% 4.77/1.85  tff(c_1895, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1846, c_1807])).
% 4.77/1.85  tff(c_1896, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1895])).
% 4.77/1.85  tff(c_1695, plain, (![C_332]: (r1_xboole_0('#skF_6', C_332) | ~r1_tarski(C_332, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_1685])).
% 4.77/1.85  tff(c_1716, plain, (![C_335, C_336]: (~r2_hidden(C_335, C_336) | ~r2_hidden(C_335, '#skF_6') | ~r1_tarski(C_336, k1_xboole_0))), inference(resolution, [status(thm)], [c_1695, c_2])).
% 4.77/1.85  tff(c_1731, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), '#skF_6') | ~r1_tarski(A_1, k1_xboole_0) | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_1716])).
% 4.77/1.85  tff(c_2129, plain, (![A_397, B_398]: (~r2_hidden('#skF_1'(A_397, B_398), '#skF_6') | ~r1_tarski(A_397, '#skF_3') | r1_xboole_0(A_397, B_398))), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_1731])).
% 4.77/1.85  tff(c_2133, plain, (![B_2]: (~r1_tarski('#skF_6', '#skF_3') | r1_xboole_0('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_2129])).
% 4.77/1.85  tff(c_2155, plain, (![B_403]: (r1_xboole_0('#skF_6', B_403))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2133])).
% 4.77/1.85  tff(c_2174, plain, (![C_404, B_405]: (~r2_hidden(C_404, B_405) | ~r2_hidden(C_404, '#skF_6'))), inference(resolution, [status(thm)], [c_2155, c_2])).
% 4.77/1.85  tff(c_2176, plain, (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2167, c_2174])).
% 4.77/1.85  tff(c_2196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2176])).
% 4.77/1.85  tff(c_2198, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1895])).
% 4.77/1.85  tff(c_1876, plain, (![A_360, B_361, C_362, D_363]: (k6_mcart_1(A_360, B_361, C_362, D_363)=k2_mcart_1(k1_mcart_1(D_363)) | ~m1_subset_1(D_363, k3_zfmisc_1(A_360, B_361, C_362)) | k1_xboole_0=C_362 | k1_xboole_0=B_361 | k1_xboole_0=A_360)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.85  tff(c_1879, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_1876])).
% 4.77/1.85  tff(c_1882, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1846, c_1879])).
% 4.77/1.85  tff(c_2229, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2198, c_1882])).
% 4.77/1.85  tff(c_2230, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2229])).
% 4.77/1.85  tff(c_1666, plain, (![A_321, C_322, A_323, B_324]: (r2_hidden(k2_mcart_1(A_321), C_322) | ~r2_hidden(A_321, k3_zfmisc_1(A_323, B_324, C_322)))), inference(superposition, [status(thm), theory('equality')], [c_1071, c_18])).
% 4.77/1.85  tff(c_1677, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_30, c_1666])).
% 4.77/1.85  tff(c_1729, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_6') | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_1677, c_1716])).
% 4.77/1.85  tff(c_1740, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1729])).
% 4.77/1.85  tff(c_2247, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_1740])).
% 4.77/1.85  tff(c_2258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2247])).
% 4.77/1.85  tff(c_2259, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_2229])).
% 4.77/1.85  tff(c_2287, plain, (![A_413, A_414, B_415, C_416]: (r2_hidden(k1_mcart_1(A_413), k2_zfmisc_1(A_414, B_415)) | ~r2_hidden(A_413, k3_zfmisc_1(A_414, B_415, C_416)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1655])).
% 4.77/1.85  tff(c_2298, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_2287])).
% 4.77/1.85  tff(c_2302, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2298, c_18])).
% 4.77/1.85  tff(c_2306, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2259, c_2302])).
% 4.77/1.85  tff(c_2308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1652, c_2306])).
% 4.77/1.85  tff(c_2310, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1729])).
% 4.77/1.85  tff(c_1702, plain, (![C_333]: (r1_xboole_0('#skF_7', C_333) | ~r1_tarski(C_333, k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_1685])).
% 4.77/1.85  tff(c_2345, plain, (![C_423, C_424]: (~r2_hidden(C_423, C_424) | ~r2_hidden(C_423, '#skF_7') | ~r1_tarski(C_424, k1_xboole_0))), inference(resolution, [status(thm)], [c_1702, c_2])).
% 4.77/1.85  tff(c_2347, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7') | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_1677, c_2345])).
% 4.77/1.85  tff(c_2361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2310, c_1677, c_2347])).
% 4.77/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.85  
% 4.77/1.85  Inference rules
% 4.77/1.85  ----------------------
% 4.77/1.85  #Ref     : 0
% 4.77/1.85  #Sup     : 523
% 4.77/1.85  #Fact    : 0
% 4.77/1.85  #Define  : 0
% 4.77/1.85  #Split   : 28
% 4.77/1.85  #Chain   : 0
% 4.77/1.85  #Close   : 0
% 4.77/1.85  
% 4.77/1.85  Ordering : KBO
% 4.77/1.85  
% 4.77/1.85  Simplification rules
% 4.77/1.85  ----------------------
% 4.77/1.85  #Subsume      : 165
% 4.77/1.85  #Demod        : 388
% 4.77/1.85  #Tautology    : 76
% 4.77/1.85  #SimpNegUnit  : 13
% 4.77/1.85  #BackRed      : 233
% 4.77/1.85  
% 4.77/1.85  #Partial instantiations: 0
% 4.77/1.85  #Strategies tried      : 1
% 4.77/1.85  
% 4.77/1.85  Timing (in seconds)
% 4.77/1.85  ----------------------
% 4.77/1.85  Preprocessing        : 0.32
% 4.77/1.85  Parsing              : 0.17
% 4.77/1.85  CNF conversion       : 0.02
% 4.77/1.85  Main loop            : 0.71
% 4.77/1.85  Inferencing          : 0.25
% 4.77/1.85  Reduction            : 0.22
% 4.77/1.85  Demodulation         : 0.15
% 4.77/1.85  BG Simplification    : 0.03
% 4.77/1.85  Subsumption          : 0.15
% 4.77/1.85  Abstraction          : 0.04
% 4.77/1.85  MUC search           : 0.00
% 4.77/1.85  Cooper               : 0.00
% 4.77/1.85  Total                : 1.11
% 4.77/1.85  Index Insertion      : 0.00
% 4.77/1.85  Index Deletion       : 0.00
% 4.77/1.85  Index Matching       : 0.00
% 4.77/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
