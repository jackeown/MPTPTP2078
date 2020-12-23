%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:12 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 688 expanded)
%              Number of leaves         :   36 ( 236 expanded)
%              Depth                    :    9
%              Number of atoms          :  350 (1790 expanded)
%              Number of equality atoms :   91 ( 393 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_96,axiom,(
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

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1335,plain,(
    ! [A_267,B_268] :
      ( r1_tarski(A_267,B_268)
      | ~ m1_subset_1(A_267,k1_zfmisc_1(B_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1345,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1335])).

tff(c_1362,plain,(
    ! [A_271,B_272] :
      ( r2_hidden('#skF_2'(A_271,B_272),B_272)
      | r1_xboole_0(A_271,B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1370,plain,(
    ! [B_272,A_271] :
      ( ~ v1_xboole_0(B_272)
      | r1_xboole_0(A_271,B_272) ) ),
    inference(resolution,[status(thm)],[c_1362,c_2])).

tff(c_1381,plain,(
    ! [B_277,A_278] :
      ( ~ r1_xboole_0(B_277,A_278)
      | ~ r1_tarski(B_277,A_278)
      | v1_xboole_0(B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1391,plain,(
    ! [A_281,B_282] :
      ( ~ r1_tarski(A_281,B_282)
      | v1_xboole_0(A_281)
      | ~ v1_xboole_0(B_282) ) ),
    inference(resolution,[status(thm)],[c_1370,c_1381])).

tff(c_1408,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1345,c_1391])).

tff(c_1412,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1408])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1346,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1335])).

tff(c_1404,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1346,c_1391])).

tff(c_1411,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_36,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] : k2_zfmisc_1(k2_zfmisc_1(A_17,B_18),C_19) = k3_zfmisc_1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1488,plain,(
    ! [A_298,C_299,B_300] :
      ( r2_hidden(k2_mcart_1(A_298),C_299)
      | ~ r2_hidden(A_298,k2_zfmisc_1(B_300,C_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1518,plain,(
    ! [A_304,C_305,A_306,B_307] :
      ( r2_hidden(k2_mcart_1(A_304),C_305)
      | ~ r2_hidden(A_304,k3_zfmisc_1(A_306,B_307,C_305)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1488])).

tff(c_1532,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_1518])).

tff(c_34,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8')
    | ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_65,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_72,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_100,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55),B_55)
      | r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [B_55,A_54] :
      ( ~ v1_xboole_0(B_55)
      | r1_xboole_0(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_110,plain,(
    ! [B_58,A_59] :
      ( ~ r1_xboole_0(B_58,A_59)
      | ~ r1_tarski(B_58,A_59)
      | v1_xboole_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,(
    ! [A_63,B_64] :
      ( ~ r1_tarski(A_63,B_64)
      | v1_xboole_0(A_63)
      | ~ v1_xboole_0(B_64) ) ),
    inference(resolution,[status(thm)],[c_108,c_110])).

tff(c_147,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_132])).

tff(c_152,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_83,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_72])).

tff(c_145,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_132])).

tff(c_150,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_84,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_146,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_132])).

tff(c_151,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_38,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_269,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k7_mcart_1(A_87,B_88,C_89,D_90) = k2_mcart_1(D_90)
      | ~ m1_subset_1(D_90,k3_zfmisc_1(A_87,B_88,C_89))
      | k1_xboole_0 = C_89
      | k1_xboole_0 = B_88
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_273,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_269])).

tff(c_303,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ! [A_44] :
      ( v1_xboole_0(A_44)
      | r2_hidden('#skF_1'(A_44),A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    ! [A_45] :
      ( ~ r1_tarski(A_45,'#skF_1'(A_45))
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_48,c_20])).

tff(c_71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_309,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_71])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_309])).

tff(c_314,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_355,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k6_mcart_1(A_100,B_101,C_102,D_103) = k2_mcart_1(k1_mcart_1(D_103))
      | ~ m1_subset_1(D_103,k3_zfmisc_1(A_100,B_101,C_102))
      | k1_xboole_0 = C_102
      | k1_xboole_0 = B_101
      | k1_xboole_0 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_358,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_355])).

tff(c_361,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_358])).

tff(c_418,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_430,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_71])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_430])).

tff(c_435,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_395,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k5_mcart_1(A_112,B_113,C_114,D_115) = k1_mcart_1(k1_mcart_1(D_115))
      | ~ m1_subset_1(D_115,k3_zfmisc_1(A_112,B_113,C_114))
      | k1_xboole_0 = C_114
      | k1_xboole_0 = B_113
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_398,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_395])).

tff(c_401,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_398])).

tff(c_538,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_401])).

tff(c_539,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_552,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_71])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_552])).

tff(c_556,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_230,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden(k1_mcart_1(A_80),B_81)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_81,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_480,plain,(
    ! [A_125,A_126,B_127,C_128] :
      ( r2_hidden(k1_mcart_1(A_125),k2_zfmisc_1(A_126,B_127))
      | ~ r2_hidden(A_125,k3_zfmisc_1(A_126,B_127,C_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_230])).

tff(c_505,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_36,c_480])).

tff(c_26,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(k1_mcart_1(A_20),B_21)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_517,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_505,c_26])).

tff(c_559,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_517])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_559])).

tff(c_562,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_624,plain,(
    ! [A_141,B_142,C_143] : k2_zfmisc_1(k2_zfmisc_1(A_141,B_142),C_143) = k3_zfmisc_1(A_141,B_142,C_143) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(k2_mcart_1(A_20),C_22)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_656,plain,(
    ! [A_147,C_148,A_149,B_150] :
      ( r2_hidden(k2_mcart_1(A_147),C_148)
      | ~ r2_hidden(A_147,k3_zfmisc_1(A_149,B_150,C_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_24])).

tff(c_670,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_656])).

tff(c_677,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_670,c_2])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_677])).

tff(c_683,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_699,plain,(
    ! [A_156,B_157,C_158] :
      ( r2_hidden(k1_mcart_1(A_156),B_157)
      | ~ r2_hidden(A_156,k2_zfmisc_1(B_157,C_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_984,plain,(
    ! [B_201,C_202] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_201,C_202))),B_201)
      | v1_xboole_0(k2_zfmisc_1(B_201,C_202)) ) ),
    inference(resolution,[status(thm)],[c_4,c_699])).

tff(c_1013,plain,(
    ! [B_201,C_202] :
      ( ~ v1_xboole_0(B_201)
      | v1_xboole_0(k2_zfmisc_1(B_201,C_202)) ) ),
    inference(resolution,[status(thm)],[c_984,c_2])).

tff(c_1015,plain,(
    ! [B_203,C_204] :
      ( ~ v1_xboole_0(B_203)
      | v1_xboole_0(k2_zfmisc_1(B_203,C_204)) ) ),
    inference(resolution,[status(thm)],[c_984,c_2])).

tff(c_1037,plain,(
    ! [A_210,B_211,C_212] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_210,B_211))
      | v1_xboole_0(k3_zfmisc_1(A_210,B_211,C_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1015])).

tff(c_64,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_1041,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1037,c_64])).

tff(c_1044,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1013,c_1041])).

tff(c_1051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_1044])).

tff(c_1052,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_119,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(k2_mcart_1(A_60),C_61)
      | ~ r2_hidden(A_60,k2_zfmisc_1(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1215,plain,(
    ! [B_248,C_249] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_248,C_249))),C_249)
      | v1_xboole_0(k2_zfmisc_1(B_248,C_249)) ) ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_1242,plain,(
    ! [C_249,B_248] :
      ( ~ v1_xboole_0(C_249)
      | v1_xboole_0(k2_zfmisc_1(B_248,C_249)) ) ),
    inference(resolution,[status(thm)],[c_1215,c_2])).

tff(c_1122,plain,(
    ! [A_227,B_228,C_229] :
      ( r2_hidden(k1_mcart_1(A_227),B_228)
      | ~ r2_hidden(A_227,k2_zfmisc_1(B_228,C_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1269,plain,(
    ! [B_255,C_256] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_255,C_256))),B_255)
      | v1_xboole_0(k2_zfmisc_1(B_255,C_256)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1122])).

tff(c_1300,plain,(
    ! [B_257,C_258] :
      ( ~ v1_xboole_0(B_257)
      | v1_xboole_0(k2_zfmisc_1(B_257,C_258)) ) ),
    inference(resolution,[status(thm)],[c_1269,c_2])).

tff(c_1311,plain,(
    ! [A_263,B_264,C_265] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_263,B_264))
      | v1_xboole_0(k3_zfmisc_1(A_263,B_264,C_265)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1300])).

tff(c_1315,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1311,c_64])).

tff(c_1321,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1242,c_1315])).

tff(c_1326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_1321])).

tff(c_1328,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1360,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1328,c_2])).

tff(c_1347,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1335])).

tff(c_1397,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1347,c_1391])).

tff(c_1407,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1360,c_1397])).

tff(c_1534,plain,(
    ! [A_308,B_309,C_310,D_311] :
      ( k7_mcart_1(A_308,B_309,C_310,D_311) = k2_mcart_1(D_311)
      | ~ m1_subset_1(D_311,k3_zfmisc_1(A_308,B_309,C_310))
      | k1_xboole_0 = C_310
      | k1_xboole_0 = B_309
      | k1_xboole_0 = A_308 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1538,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_1534])).

tff(c_1547,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1538])).

tff(c_1329,plain,(
    ! [A_266] :
      ( ~ r1_tarski(A_266,'#skF_1'(A_266))
      | v1_xboole_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_48,c_20])).

tff(c_1334,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_1329])).

tff(c_1553,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_1334])).

tff(c_1556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1407,c_1553])).

tff(c_1557,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1538])).

tff(c_1652,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1557])).

tff(c_1327,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1361,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1327])).

tff(c_1653,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1652,c_1361])).

tff(c_1656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1653])).

tff(c_1657,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1557])).

tff(c_1659,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1657])).

tff(c_1667,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1659,c_1334])).

tff(c_1670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1411,c_1667])).

tff(c_1671,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1657])).

tff(c_1689,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1334])).

tff(c_1692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1412,c_1689])).

tff(c_1693,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_1752,plain,(
    ! [A_347,B_348,C_349] : k2_zfmisc_1(k2_zfmisc_1(A_347,B_348),C_349) = k3_zfmisc_1(A_347,B_348,C_349) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1805,plain,(
    ! [A_359,C_360,A_361,B_362] :
      ( r2_hidden(k2_mcart_1(A_359),C_360)
      | ~ r2_hidden(A_359,k3_zfmisc_1(A_361,B_362,C_360)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1752,c_24])).

tff(c_1819,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_1805])).

tff(c_1826,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1819,c_2])).

tff(c_1831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1826])).

tff(c_1832,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_1842,plain,(
    ! [A_366,C_367,B_368] :
      ( r2_hidden(k2_mcart_1(A_366),C_367)
      | ~ r2_hidden(A_366,k2_zfmisc_1(B_368,C_367)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2031,plain,(
    ! [B_403,C_404] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_403,C_404))),C_404)
      | v1_xboole_0(k2_zfmisc_1(B_403,C_404)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1842])).

tff(c_2060,plain,(
    ! [C_405,B_406] :
      ( ~ v1_xboole_0(C_405)
      | v1_xboole_0(k2_zfmisc_1(B_406,C_405)) ) ),
    inference(resolution,[status(thm)],[c_2031,c_2])).

tff(c_1925,plain,(
    ! [A_381,B_382,C_383] :
      ( r2_hidden(k1_mcart_1(A_381),B_382)
      | ~ r2_hidden(A_381,k2_zfmisc_1(B_382,C_383)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1969,plain,(
    ! [B_392,C_393] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_392,C_393))),B_392)
      | v1_xboole_0(k2_zfmisc_1(B_392,C_393)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1925])).

tff(c_2005,plain,(
    ! [B_398,C_399] :
      ( ~ v1_xboole_0(B_398)
      | v1_xboole_0(k2_zfmisc_1(B_398,C_399)) ) ),
    inference(resolution,[status(thm)],[c_1969,c_2])).

tff(c_2009,plain,(
    ! [A_400,B_401,C_402] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_400,B_401))
      | v1_xboole_0(k3_zfmisc_1(A_400,B_401,C_402)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2005])).

tff(c_2013,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2009,c_64])).

tff(c_2063,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2060,c_2013])).

tff(c_2070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_2063])).

tff(c_2072,plain,(
    r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1327])).

tff(c_2080,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2072,c_2])).

tff(c_2081,plain,(
    ! [A_407,B_408] :
      ( r2_hidden('#skF_2'(A_407,B_408),B_408)
      | r1_xboole_0(A_407,B_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2089,plain,(
    ! [B_408,A_407] :
      ( ~ v1_xboole_0(B_408)
      | r1_xboole_0(A_407,B_408) ) ),
    inference(resolution,[status(thm)],[c_2081,c_2])).

tff(c_2101,plain,(
    ! [B_415,A_416] :
      ( ~ r1_xboole_0(B_415,A_416)
      | ~ r1_tarski(B_415,A_416)
      | v1_xboole_0(B_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2110,plain,(
    ! [A_417,B_418] :
      ( ~ r1_tarski(A_417,B_418)
      | v1_xboole_0(A_417)
      | ~ v1_xboole_0(B_418) ) ),
    inference(resolution,[status(thm)],[c_2089,c_2101])).

tff(c_2119,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1345,c_2110])).

tff(c_2129,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2080,c_2119])).

tff(c_2071,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1327])).

tff(c_2123,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1346,c_2110])).

tff(c_2139,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2123])).

tff(c_2116,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1347,c_2110])).

tff(c_2126,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1360,c_2116])).

tff(c_2295,plain,(
    ! [A_448,B_449,C_450,D_451] :
      ( k7_mcart_1(A_448,B_449,C_450,D_451) = k2_mcart_1(D_451)
      | ~ m1_subset_1(D_451,k3_zfmisc_1(A_448,B_449,C_450))
      | k1_xboole_0 = C_450
      | k1_xboole_0 = B_449
      | k1_xboole_0 = A_448 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2299,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_2295])).

tff(c_2340,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2299])).

tff(c_2346,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2340,c_1334])).

tff(c_2349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2126,c_2346])).

tff(c_2351,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2299])).

tff(c_2365,plain,(
    ! [A_462,B_463,C_464,D_465] :
      ( k6_mcart_1(A_462,B_463,C_464,D_465) = k2_mcart_1(k1_mcart_1(D_465))
      | ~ m1_subset_1(D_465,k3_zfmisc_1(A_462,B_463,C_464))
      | k1_xboole_0 = C_464
      | k1_xboole_0 = B_463
      | k1_xboole_0 = A_462 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2368,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_2365])).

tff(c_2371,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2351,c_2368])).

tff(c_2390,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2371])).

tff(c_2398,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2390,c_1334])).

tff(c_2401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2139,c_2398])).

tff(c_2402,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2371])).

tff(c_2405,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2402])).

tff(c_2223,plain,(
    ! [A_437,B_438,C_439] :
      ( r2_hidden(k1_mcart_1(A_437),B_438)
      | ~ r2_hidden(A_437,k2_zfmisc_1(B_438,C_439)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2456,plain,(
    ! [A_478,A_479,B_480,C_481] :
      ( r2_hidden(k1_mcart_1(A_478),k2_zfmisc_1(A_479,B_480))
      | ~ r2_hidden(A_478,k3_zfmisc_1(A_479,B_480,C_481)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2223])).

tff(c_2478,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_36,c_2456])).

tff(c_2483,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2478,c_24])).

tff(c_2493,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2405,c_2483])).

tff(c_2495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2071,c_2493])).

tff(c_2496,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2402])).

tff(c_2507,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_1334])).

tff(c_2510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2129,c_2507])).

tff(c_2511,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2123])).

tff(c_2555,plain,(
    ! [A_488,C_489,B_490] :
      ( r2_hidden(k2_mcart_1(A_488),C_489)
      | ~ r2_hidden(A_488,k2_zfmisc_1(B_490,C_489)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2679,plain,(
    ! [B_513,C_514] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_513,C_514))),C_514)
      | v1_xboole_0(k2_zfmisc_1(B_513,C_514)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2555])).

tff(c_2706,plain,(
    ! [C_514,B_513] :
      ( ~ v1_xboole_0(C_514)
      | v1_xboole_0(k2_zfmisc_1(B_513,C_514)) ) ),
    inference(resolution,[status(thm)],[c_2679,c_2])).

tff(c_2635,plain,(
    ! [A_502,B_503,C_504] :
      ( r2_hidden(k1_mcart_1(A_502),B_503)
      | ~ r2_hidden(A_502,k2_zfmisc_1(B_503,C_504)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2717,plain,(
    ! [B_520,C_521] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_520,C_521))),B_520)
      | v1_xboole_0(k2_zfmisc_1(B_520,C_521)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2635])).

tff(c_2748,plain,(
    ! [B_522,C_523] :
      ( ~ v1_xboole_0(B_522)
      | v1_xboole_0(k2_zfmisc_1(B_522,C_523)) ) ),
    inference(resolution,[status(thm)],[c_2717,c_2])).

tff(c_2757,plain,(
    ! [A_528,B_529,C_530] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_528,B_529))
      | v1_xboole_0(k3_zfmisc_1(A_528,B_529,C_530)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2748])).

tff(c_2761,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2757,c_64])).

tff(c_2767,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2706,c_2761])).

tff(c_2772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_2767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/2.00  
% 4.84/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/2.01  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 4.84/2.01  
% 4.84/2.01  %Foreground sorts:
% 4.84/2.01  
% 4.84/2.01  
% 4.84/2.01  %Background operators:
% 4.84/2.01  
% 4.84/2.01  
% 4.84/2.01  %Foreground operators:
% 4.84/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.84/2.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.84/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/2.01  tff('#skF_7', type, '#skF_7': $i).
% 4.84/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.84/2.01  tff('#skF_5', type, '#skF_5': $i).
% 4.84/2.01  tff('#skF_6', type, '#skF_6': $i).
% 4.84/2.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.84/2.01  tff('#skF_3', type, '#skF_3': $i).
% 4.84/2.01  tff('#skF_9', type, '#skF_9': $i).
% 4.84/2.01  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.84/2.01  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.84/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/2.01  tff('#skF_8', type, '#skF_8': $i).
% 4.84/2.01  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.84/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/2.01  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.84/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/2.01  tff('#skF_4', type, '#skF_4': $i).
% 4.84/2.01  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.84/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/2.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.84/2.01  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.84/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.84/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/2.01  
% 4.84/2.03  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 4.84/2.03  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.84/2.03  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.84/2.03  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.84/2.03  tff(f_59, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.84/2.03  tff(f_70, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.84/2.03  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.84/2.03  tff(f_96, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.84/2.03  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.84/2.03  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.84/2.03  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.84/2.03  tff(c_1335, plain, (![A_267, B_268]: (r1_tarski(A_267, B_268) | ~m1_subset_1(A_267, k1_zfmisc_1(B_268)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/2.03  tff(c_1345, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_1335])).
% 4.84/2.03  tff(c_1362, plain, (![A_271, B_272]: (r2_hidden('#skF_2'(A_271, B_272), B_272) | r1_xboole_0(A_271, B_272))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.84/2.03  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/2.03  tff(c_1370, plain, (![B_272, A_271]: (~v1_xboole_0(B_272) | r1_xboole_0(A_271, B_272))), inference(resolution, [status(thm)], [c_1362, c_2])).
% 4.84/2.03  tff(c_1381, plain, (![B_277, A_278]: (~r1_xboole_0(B_277, A_278) | ~r1_tarski(B_277, A_278) | v1_xboole_0(B_277))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.84/2.03  tff(c_1391, plain, (![A_281, B_282]: (~r1_tarski(A_281, B_282) | v1_xboole_0(A_281) | ~v1_xboole_0(B_282))), inference(resolution, [status(thm)], [c_1370, c_1381])).
% 4.84/2.03  tff(c_1408, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1345, c_1391])).
% 4.84/2.03  tff(c_1412, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1408])).
% 4.84/2.03  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.84/2.03  tff(c_1346, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_1335])).
% 4.84/2.03  tff(c_1404, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1346, c_1391])).
% 4.84/2.03  tff(c_1411, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1404])).
% 4.84/2.03  tff(c_36, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.84/2.03  tff(c_22, plain, (![A_17, B_18, C_19]: (k2_zfmisc_1(k2_zfmisc_1(A_17, B_18), C_19)=k3_zfmisc_1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.84/2.03  tff(c_1488, plain, (![A_298, C_299, B_300]: (r2_hidden(k2_mcart_1(A_298), C_299) | ~r2_hidden(A_298, k2_zfmisc_1(B_300, C_299)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_1518, plain, (![A_304, C_305, A_306, B_307]: (r2_hidden(k2_mcart_1(A_304), C_305) | ~r2_hidden(A_304, k3_zfmisc_1(A_306, B_307, C_305)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1488])).
% 4.84/2.03  tff(c_1532, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_36, c_1518])).
% 4.84/2.03  tff(c_34, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8') | ~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.84/2.03  tff(c_65, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 4.84/2.03  tff(c_72, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/2.03  tff(c_82, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_72])).
% 4.84/2.03  tff(c_100, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55), B_55) | r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.84/2.03  tff(c_108, plain, (![B_55, A_54]: (~v1_xboole_0(B_55) | r1_xboole_0(A_54, B_55))), inference(resolution, [status(thm)], [c_100, c_2])).
% 4.84/2.03  tff(c_110, plain, (![B_58, A_59]: (~r1_xboole_0(B_58, A_59) | ~r1_tarski(B_58, A_59) | v1_xboole_0(B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.84/2.03  tff(c_132, plain, (![A_63, B_64]: (~r1_tarski(A_63, B_64) | v1_xboole_0(A_63) | ~v1_xboole_0(B_64))), inference(resolution, [status(thm)], [c_108, c_110])).
% 4.84/2.03  tff(c_147, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_82, c_132])).
% 4.84/2.03  tff(c_152, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_147])).
% 4.84/2.03  tff(c_83, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_72])).
% 4.84/2.03  tff(c_145, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_83, c_132])).
% 4.84/2.03  tff(c_150, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_145])).
% 4.84/2.03  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.84/2.03  tff(c_84, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_72])).
% 4.84/2.03  tff(c_146, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_132])).
% 4.84/2.03  tff(c_151, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 4.84/2.03  tff(c_38, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.84/2.03  tff(c_269, plain, (![A_87, B_88, C_89, D_90]: (k7_mcart_1(A_87, B_88, C_89, D_90)=k2_mcart_1(D_90) | ~m1_subset_1(D_90, k3_zfmisc_1(A_87, B_88, C_89)) | k1_xboole_0=C_89 | k1_xboole_0=B_88 | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.03  tff(c_273, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_269])).
% 4.84/2.03  tff(c_303, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_273])).
% 4.84/2.03  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.84/2.03  tff(c_48, plain, (![A_44]: (v1_xboole_0(A_44) | r2_hidden('#skF_1'(A_44), A_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/2.03  tff(c_20, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.84/2.03  tff(c_66, plain, (![A_45]: (~r1_tarski(A_45, '#skF_1'(A_45)) | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_48, c_20])).
% 4.84/2.03  tff(c_71, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_66])).
% 4.84/2.03  tff(c_309, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_71])).
% 4.84/2.03  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_309])).
% 4.84/2.03  tff(c_314, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_273])).
% 4.84/2.03  tff(c_355, plain, (![A_100, B_101, C_102, D_103]: (k6_mcart_1(A_100, B_101, C_102, D_103)=k2_mcart_1(k1_mcart_1(D_103)) | ~m1_subset_1(D_103, k3_zfmisc_1(A_100, B_101, C_102)) | k1_xboole_0=C_102 | k1_xboole_0=B_101 | k1_xboole_0=A_100)), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.03  tff(c_358, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_355])).
% 4.84/2.03  tff(c_361, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_314, c_358])).
% 4.84/2.03  tff(c_418, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_361])).
% 4.84/2.03  tff(c_430, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_71])).
% 4.84/2.03  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_430])).
% 4.84/2.03  tff(c_435, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_361])).
% 4.84/2.03  tff(c_395, plain, (![A_112, B_113, C_114, D_115]: (k5_mcart_1(A_112, B_113, C_114, D_115)=k1_mcart_1(k1_mcart_1(D_115)) | ~m1_subset_1(D_115, k3_zfmisc_1(A_112, B_113, C_114)) | k1_xboole_0=C_114 | k1_xboole_0=B_113 | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.03  tff(c_398, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_395])).
% 4.84/2.03  tff(c_401, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_314, c_398])).
% 4.84/2.03  tff(c_538, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_435, c_401])).
% 4.84/2.03  tff(c_539, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_538])).
% 4.84/2.03  tff(c_552, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_71])).
% 4.84/2.03  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_552])).
% 4.84/2.03  tff(c_556, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_538])).
% 4.84/2.03  tff(c_230, plain, (![A_80, B_81, C_82]: (r2_hidden(k1_mcart_1(A_80), B_81) | ~r2_hidden(A_80, k2_zfmisc_1(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_480, plain, (![A_125, A_126, B_127, C_128]: (r2_hidden(k1_mcart_1(A_125), k2_zfmisc_1(A_126, B_127)) | ~r2_hidden(A_125, k3_zfmisc_1(A_126, B_127, C_128)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_230])).
% 4.84/2.03  tff(c_505, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_36, c_480])).
% 4.84/2.03  tff(c_26, plain, (![A_20, B_21, C_22]: (r2_hidden(k1_mcart_1(A_20), B_21) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_517, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_505, c_26])).
% 4.84/2.03  tff(c_559, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_556, c_517])).
% 4.84/2.03  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_559])).
% 4.84/2.03  tff(c_562, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_147])).
% 4.84/2.03  tff(c_624, plain, (![A_141, B_142, C_143]: (k2_zfmisc_1(k2_zfmisc_1(A_141, B_142), C_143)=k3_zfmisc_1(A_141, B_142, C_143))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.84/2.03  tff(c_24, plain, (![A_20, C_22, B_21]: (r2_hidden(k2_mcart_1(A_20), C_22) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_656, plain, (![A_147, C_148, A_149, B_150]: (r2_hidden(k2_mcart_1(A_147), C_148) | ~r2_hidden(A_147, k3_zfmisc_1(A_149, B_150, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_624, c_24])).
% 4.84/2.03  tff(c_670, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_36, c_656])).
% 4.84/2.03  tff(c_677, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_670, c_2])).
% 4.84/2.03  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_562, c_677])).
% 4.84/2.03  tff(c_683, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_146])).
% 4.84/2.03  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/2.03  tff(c_699, plain, (![A_156, B_157, C_158]: (r2_hidden(k1_mcart_1(A_156), B_157) | ~r2_hidden(A_156, k2_zfmisc_1(B_157, C_158)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_984, plain, (![B_201, C_202]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_201, C_202))), B_201) | v1_xboole_0(k2_zfmisc_1(B_201, C_202)))), inference(resolution, [status(thm)], [c_4, c_699])).
% 4.84/2.03  tff(c_1013, plain, (![B_201, C_202]: (~v1_xboole_0(B_201) | v1_xboole_0(k2_zfmisc_1(B_201, C_202)))), inference(resolution, [status(thm)], [c_984, c_2])).
% 4.84/2.03  tff(c_1015, plain, (![B_203, C_204]: (~v1_xboole_0(B_203) | v1_xboole_0(k2_zfmisc_1(B_203, C_204)))), inference(resolution, [status(thm)], [c_984, c_2])).
% 4.84/2.03  tff(c_1037, plain, (![A_210, B_211, C_212]: (~v1_xboole_0(k2_zfmisc_1(A_210, B_211)) | v1_xboole_0(k3_zfmisc_1(A_210, B_211, C_212)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1015])).
% 4.84/2.03  tff(c_64, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_2])).
% 4.84/2.03  tff(c_1041, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1037, c_64])).
% 4.84/2.03  tff(c_1044, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1013, c_1041])).
% 4.84/2.03  tff(c_1051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_683, c_1044])).
% 4.84/2.03  tff(c_1052, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_145])).
% 4.84/2.03  tff(c_119, plain, (![A_60, C_61, B_62]: (r2_hidden(k2_mcart_1(A_60), C_61) | ~r2_hidden(A_60, k2_zfmisc_1(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_1215, plain, (![B_248, C_249]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_248, C_249))), C_249) | v1_xboole_0(k2_zfmisc_1(B_248, C_249)))), inference(resolution, [status(thm)], [c_4, c_119])).
% 4.84/2.03  tff(c_1242, plain, (![C_249, B_248]: (~v1_xboole_0(C_249) | v1_xboole_0(k2_zfmisc_1(B_248, C_249)))), inference(resolution, [status(thm)], [c_1215, c_2])).
% 4.84/2.03  tff(c_1122, plain, (![A_227, B_228, C_229]: (r2_hidden(k1_mcart_1(A_227), B_228) | ~r2_hidden(A_227, k2_zfmisc_1(B_228, C_229)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_1269, plain, (![B_255, C_256]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_255, C_256))), B_255) | v1_xboole_0(k2_zfmisc_1(B_255, C_256)))), inference(resolution, [status(thm)], [c_4, c_1122])).
% 4.84/2.03  tff(c_1300, plain, (![B_257, C_258]: (~v1_xboole_0(B_257) | v1_xboole_0(k2_zfmisc_1(B_257, C_258)))), inference(resolution, [status(thm)], [c_1269, c_2])).
% 4.84/2.03  tff(c_1311, plain, (![A_263, B_264, C_265]: (~v1_xboole_0(k2_zfmisc_1(A_263, B_264)) | v1_xboole_0(k3_zfmisc_1(A_263, B_264, C_265)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1300])).
% 4.84/2.03  tff(c_1315, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1311, c_64])).
% 4.84/2.03  tff(c_1321, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1242, c_1315])).
% 4.84/2.03  tff(c_1326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1052, c_1321])).
% 4.84/2.03  tff(c_1328, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 4.84/2.03  tff(c_1360, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1328, c_2])).
% 4.84/2.03  tff(c_1347, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1335])).
% 4.84/2.03  tff(c_1397, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1347, c_1391])).
% 4.84/2.03  tff(c_1407, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1360, c_1397])).
% 4.84/2.03  tff(c_1534, plain, (![A_308, B_309, C_310, D_311]: (k7_mcart_1(A_308, B_309, C_310, D_311)=k2_mcart_1(D_311) | ~m1_subset_1(D_311, k3_zfmisc_1(A_308, B_309, C_310)) | k1_xboole_0=C_310 | k1_xboole_0=B_309 | k1_xboole_0=A_308)), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.03  tff(c_1538, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_1534])).
% 4.84/2.03  tff(c_1547, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1538])).
% 4.84/2.03  tff(c_1329, plain, (![A_266]: (~r1_tarski(A_266, '#skF_1'(A_266)) | v1_xboole_0(A_266))), inference(resolution, [status(thm)], [c_48, c_20])).
% 4.84/2.03  tff(c_1334, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1329])).
% 4.84/2.03  tff(c_1553, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_1334])).
% 4.84/2.03  tff(c_1556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1407, c_1553])).
% 4.84/2.03  tff(c_1557, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_1538])).
% 4.84/2.03  tff(c_1652, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_1557])).
% 4.84/2.03  tff(c_1327, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_34])).
% 4.84/2.03  tff(c_1361, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1327])).
% 4.84/2.03  tff(c_1653, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1652, c_1361])).
% 4.84/2.03  tff(c_1656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1653])).
% 4.84/2.03  tff(c_1657, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1557])).
% 4.84/2.03  tff(c_1659, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1657])).
% 4.84/2.03  tff(c_1667, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1659, c_1334])).
% 4.84/2.03  tff(c_1670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1411, c_1667])).
% 4.84/2.03  tff(c_1671, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1657])).
% 4.84/2.03  tff(c_1689, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1334])).
% 4.84/2.03  tff(c_1692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1412, c_1689])).
% 4.84/2.03  tff(c_1693, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_1408])).
% 4.84/2.03  tff(c_1752, plain, (![A_347, B_348, C_349]: (k2_zfmisc_1(k2_zfmisc_1(A_347, B_348), C_349)=k3_zfmisc_1(A_347, B_348, C_349))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.84/2.03  tff(c_1805, plain, (![A_359, C_360, A_361, B_362]: (r2_hidden(k2_mcart_1(A_359), C_360) | ~r2_hidden(A_359, k3_zfmisc_1(A_361, B_362, C_360)))), inference(superposition, [status(thm), theory('equality')], [c_1752, c_24])).
% 4.84/2.03  tff(c_1819, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_36, c_1805])).
% 4.84/2.03  tff(c_1826, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_1819, c_2])).
% 4.84/2.03  tff(c_1831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1826])).
% 4.84/2.03  tff(c_1832, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1404])).
% 4.84/2.03  tff(c_1842, plain, (![A_366, C_367, B_368]: (r2_hidden(k2_mcart_1(A_366), C_367) | ~r2_hidden(A_366, k2_zfmisc_1(B_368, C_367)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_2031, plain, (![B_403, C_404]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_403, C_404))), C_404) | v1_xboole_0(k2_zfmisc_1(B_403, C_404)))), inference(resolution, [status(thm)], [c_4, c_1842])).
% 4.84/2.03  tff(c_2060, plain, (![C_405, B_406]: (~v1_xboole_0(C_405) | v1_xboole_0(k2_zfmisc_1(B_406, C_405)))), inference(resolution, [status(thm)], [c_2031, c_2])).
% 4.84/2.03  tff(c_1925, plain, (![A_381, B_382, C_383]: (r2_hidden(k1_mcart_1(A_381), B_382) | ~r2_hidden(A_381, k2_zfmisc_1(B_382, C_383)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_1969, plain, (![B_392, C_393]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_392, C_393))), B_392) | v1_xboole_0(k2_zfmisc_1(B_392, C_393)))), inference(resolution, [status(thm)], [c_4, c_1925])).
% 4.84/2.03  tff(c_2005, plain, (![B_398, C_399]: (~v1_xboole_0(B_398) | v1_xboole_0(k2_zfmisc_1(B_398, C_399)))), inference(resolution, [status(thm)], [c_1969, c_2])).
% 4.84/2.03  tff(c_2009, plain, (![A_400, B_401, C_402]: (~v1_xboole_0(k2_zfmisc_1(A_400, B_401)) | v1_xboole_0(k3_zfmisc_1(A_400, B_401, C_402)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2005])).
% 4.84/2.03  tff(c_2013, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2009, c_64])).
% 4.84/2.03  tff(c_2063, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_2060, c_2013])).
% 4.84/2.03  tff(c_2070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1832, c_2063])).
% 4.84/2.03  tff(c_2072, plain, (r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_1327])).
% 4.84/2.03  tff(c_2080, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_2072, c_2])).
% 4.84/2.03  tff(c_2081, plain, (![A_407, B_408]: (r2_hidden('#skF_2'(A_407, B_408), B_408) | r1_xboole_0(A_407, B_408))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.84/2.03  tff(c_2089, plain, (![B_408, A_407]: (~v1_xboole_0(B_408) | r1_xboole_0(A_407, B_408))), inference(resolution, [status(thm)], [c_2081, c_2])).
% 4.84/2.03  tff(c_2101, plain, (![B_415, A_416]: (~r1_xboole_0(B_415, A_416) | ~r1_tarski(B_415, A_416) | v1_xboole_0(B_415))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.84/2.03  tff(c_2110, plain, (![A_417, B_418]: (~r1_tarski(A_417, B_418) | v1_xboole_0(A_417) | ~v1_xboole_0(B_418))), inference(resolution, [status(thm)], [c_2089, c_2101])).
% 4.84/2.03  tff(c_2119, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1345, c_2110])).
% 4.84/2.03  tff(c_2129, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2080, c_2119])).
% 4.84/2.03  tff(c_2071, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_1327])).
% 4.84/2.03  tff(c_2123, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1346, c_2110])).
% 4.84/2.03  tff(c_2139, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2123])).
% 4.84/2.03  tff(c_2116, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1347, c_2110])).
% 4.84/2.03  tff(c_2126, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1360, c_2116])).
% 4.84/2.03  tff(c_2295, plain, (![A_448, B_449, C_450, D_451]: (k7_mcart_1(A_448, B_449, C_450, D_451)=k2_mcart_1(D_451) | ~m1_subset_1(D_451, k3_zfmisc_1(A_448, B_449, C_450)) | k1_xboole_0=C_450 | k1_xboole_0=B_449 | k1_xboole_0=A_448)), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.03  tff(c_2299, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_2295])).
% 4.84/2.03  tff(c_2340, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2299])).
% 4.84/2.03  tff(c_2346, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2340, c_1334])).
% 4.84/2.03  tff(c_2349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2126, c_2346])).
% 4.84/2.03  tff(c_2351, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2299])).
% 4.84/2.03  tff(c_2365, plain, (![A_462, B_463, C_464, D_465]: (k6_mcart_1(A_462, B_463, C_464, D_465)=k2_mcart_1(k1_mcart_1(D_465)) | ~m1_subset_1(D_465, k3_zfmisc_1(A_462, B_463, C_464)) | k1_xboole_0=C_464 | k1_xboole_0=B_463 | k1_xboole_0=A_462)), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.03  tff(c_2368, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_2365])).
% 4.84/2.03  tff(c_2371, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2351, c_2368])).
% 4.84/2.03  tff(c_2390, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2371])).
% 4.84/2.03  tff(c_2398, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2390, c_1334])).
% 4.84/2.03  tff(c_2401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2139, c_2398])).
% 4.84/2.03  tff(c_2402, plain, (k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_2371])).
% 4.84/2.03  tff(c_2405, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitLeft, [status(thm)], [c_2402])).
% 4.84/2.03  tff(c_2223, plain, (![A_437, B_438, C_439]: (r2_hidden(k1_mcart_1(A_437), B_438) | ~r2_hidden(A_437, k2_zfmisc_1(B_438, C_439)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_2456, plain, (![A_478, A_479, B_480, C_481]: (r2_hidden(k1_mcart_1(A_478), k2_zfmisc_1(A_479, B_480)) | ~r2_hidden(A_478, k3_zfmisc_1(A_479, B_480, C_481)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2223])).
% 4.84/2.03  tff(c_2478, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_36, c_2456])).
% 4.84/2.03  tff(c_2483, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_2478, c_24])).
% 4.84/2.03  tff(c_2493, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2405, c_2483])).
% 4.84/2.03  tff(c_2495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2071, c_2493])).
% 4.84/2.03  tff(c_2496, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2402])).
% 4.84/2.03  tff(c_2507, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_1334])).
% 4.84/2.03  tff(c_2510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2129, c_2507])).
% 4.84/2.03  tff(c_2511, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_2123])).
% 4.84/2.03  tff(c_2555, plain, (![A_488, C_489, B_490]: (r2_hidden(k2_mcart_1(A_488), C_489) | ~r2_hidden(A_488, k2_zfmisc_1(B_490, C_489)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_2679, plain, (![B_513, C_514]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_513, C_514))), C_514) | v1_xboole_0(k2_zfmisc_1(B_513, C_514)))), inference(resolution, [status(thm)], [c_4, c_2555])).
% 4.84/2.03  tff(c_2706, plain, (![C_514, B_513]: (~v1_xboole_0(C_514) | v1_xboole_0(k2_zfmisc_1(B_513, C_514)))), inference(resolution, [status(thm)], [c_2679, c_2])).
% 4.84/2.03  tff(c_2635, plain, (![A_502, B_503, C_504]: (r2_hidden(k1_mcart_1(A_502), B_503) | ~r2_hidden(A_502, k2_zfmisc_1(B_503, C_504)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/2.03  tff(c_2717, plain, (![B_520, C_521]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_520, C_521))), B_520) | v1_xboole_0(k2_zfmisc_1(B_520, C_521)))), inference(resolution, [status(thm)], [c_4, c_2635])).
% 4.84/2.03  tff(c_2748, plain, (![B_522, C_523]: (~v1_xboole_0(B_522) | v1_xboole_0(k2_zfmisc_1(B_522, C_523)))), inference(resolution, [status(thm)], [c_2717, c_2])).
% 4.84/2.03  tff(c_2757, plain, (![A_528, B_529, C_530]: (~v1_xboole_0(k2_zfmisc_1(A_528, B_529)) | v1_xboole_0(k3_zfmisc_1(A_528, B_529, C_530)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2748])).
% 4.84/2.03  tff(c_2761, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2757, c_64])).
% 4.84/2.03  tff(c_2767, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_2706, c_2761])).
% 4.84/2.03  tff(c_2772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2511, c_2767])).
% 4.84/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/2.03  
% 4.84/2.03  Inference rules
% 4.84/2.03  ----------------------
% 4.84/2.03  #Ref     : 0
% 4.84/2.03  #Sup     : 563
% 4.84/2.03  #Fact    : 0
% 4.84/2.03  #Define  : 0
% 4.84/2.03  #Split   : 28
% 4.84/2.03  #Chain   : 0
% 4.84/2.03  #Close   : 0
% 4.84/2.03  
% 4.84/2.03  Ordering : KBO
% 4.84/2.03  
% 4.84/2.03  Simplification rules
% 4.84/2.03  ----------------------
% 4.84/2.03  #Subsume      : 51
% 4.84/2.03  #Demod        : 344
% 4.84/2.03  #Tautology    : 120
% 4.84/2.03  #SimpNegUnit  : 25
% 4.84/2.03  #BackRed      : 135
% 4.84/2.03  
% 4.84/2.03  #Partial instantiations: 0
% 4.84/2.03  #Strategies tried      : 1
% 4.84/2.03  
% 4.84/2.03  Timing (in seconds)
% 4.84/2.03  ----------------------
% 4.84/2.04  Preprocessing        : 0.36
% 4.84/2.04  Parsing              : 0.18
% 4.84/2.04  CNF conversion       : 0.03
% 4.84/2.04  Main loop            : 0.80
% 4.84/2.04  Inferencing          : 0.31
% 4.84/2.04  Reduction            : 0.24
% 4.84/2.04  Demodulation         : 0.16
% 4.84/2.04  BG Simplification    : 0.04
% 4.84/2.04  Subsumption          : 0.13
% 4.84/2.04  Abstraction          : 0.04
% 4.84/2.04  MUC search           : 0.00
% 4.84/2.04  Cooper               : 0.00
% 4.84/2.04  Total                : 1.23
% 4.84/2.04  Index Insertion      : 0.00
% 4.84/2.04  Index Deletion       : 0.00
% 4.84/2.04  Index Matching       : 0.00
% 4.84/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
