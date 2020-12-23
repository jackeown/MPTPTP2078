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
% DateTime   : Thu Dec  3 10:10:06 EST 2020

% Result     : Theorem 43.71s
% Output     : CNFRefutation 43.71s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 520 expanded)
%              Number of leaves         :   34 ( 190 expanded)
%              Depth                    :   18
%              Number of atoms          :  210 (1364 expanded)
%              Number of equality atoms :   99 ( 591 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_82,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60212,plain,(
    ! [A_2665,B_2666,C_2667,D_2668] :
      ( k5_mcart_1(A_2665,B_2666,C_2667,D_2668) = k1_mcart_1(k1_mcart_1(D_2668))
      | ~ m1_subset_1(D_2668,k3_zfmisc_1(A_2665,B_2666,C_2667))
      | k1_xboole_0 = C_2667
      | k1_xboole_0 = B_2666
      | k1_xboole_0 = A_2665 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_60248,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_60212])).

tff(c_60260,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_60248])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18) = k3_zfmisc_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_212,plain,(
    ! [A_85,C_86,B_87] :
      ( r2_hidden(k2_mcart_1(A_85),C_86)
      | ~ r2_hidden(A_85,k2_zfmisc_1(B_87,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_62586,plain,(
    ! [A_2875,C_2876,B_2877] :
      ( r2_hidden(k2_mcart_1(A_2875),C_2876)
      | v1_xboole_0(k2_zfmisc_1(B_2877,C_2876))
      | ~ m1_subset_1(A_2875,k2_zfmisc_1(B_2877,C_2876)) ) ),
    inference(resolution,[status(thm)],[c_14,c_212])).

tff(c_62624,plain,(
    ! [A_2875,C_18,A_16,B_17] :
      ( r2_hidden(k2_mcart_1(A_2875),C_18)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18))
      | ~ m1_subset_1(A_2875,k3_zfmisc_1(A_16,B_17,C_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_62586])).

tff(c_65274,plain,(
    ! [A_3035,C_3036,A_3037,B_3038] :
      ( r2_hidden(k2_mcart_1(A_3035),C_3036)
      | v1_xboole_0(k3_zfmisc_1(A_3037,B_3038,C_3036))
      | ~ m1_subset_1(A_3035,k3_zfmisc_1(A_3037,B_3038,C_3036)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_62624])).

tff(c_65409,plain,
    ( r2_hidden(k2_mcart_1('#skF_7'),'#skF_5')
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_65274])).

tff(c_65410,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_65409])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65414,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65410,c_2])).

tff(c_266,plain,(
    ! [A_92,B_93,C_94] : k2_zfmisc_1(k2_zfmisc_1(A_92,B_93),C_94) = k3_zfmisc_1(A_92,B_93,C_94) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_279,plain,(
    ! [C_94,A_92,B_93] :
      ( k1_xboole_0 = C_94
      | k2_zfmisc_1(A_92,B_93) = k1_xboole_0
      | k3_zfmisc_1(A_92,B_93,C_94) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_6])).

tff(c_65432,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_65414,c_279])).

tff(c_65449,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_65432])).

tff(c_65480,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_65449,c_6])).

tff(c_65491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_65480])).

tff(c_65493,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_65409])).

tff(c_133,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k1_mcart_1(A_62),B_63)
      | ~ r2_hidden(A_62,k2_zfmisc_1(B_63,C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_62436,plain,(
    ! [A_2859,B_2860,C_2861] :
      ( r2_hidden(k1_mcart_1(A_2859),B_2860)
      | v1_xboole_0(k2_zfmisc_1(B_2860,C_2861))
      | ~ m1_subset_1(A_2859,k2_zfmisc_1(B_2860,C_2861)) ) ),
    inference(resolution,[status(thm)],[c_14,c_133])).

tff(c_62474,plain,(
    ! [A_2859,A_16,B_17,C_18] :
      ( r2_hidden(k1_mcart_1(A_2859),k2_zfmisc_1(A_16,B_17))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18))
      | ~ m1_subset_1(A_2859,k3_zfmisc_1(A_16,B_17,C_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_62436])).

tff(c_66289,plain,(
    ! [A_3095,A_3096,B_3097,C_3098] :
      ( r2_hidden(k1_mcart_1(A_3095),k2_zfmisc_1(A_3096,B_3097))
      | v1_xboole_0(k3_zfmisc_1(A_3096,B_3097,C_3098))
      | ~ m1_subset_1(A_3095,k3_zfmisc_1(A_3096,B_3097,C_3098)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_62474])).

tff(c_66389,plain,
    ( r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_66289])).

tff(c_66426,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_65493,c_66389])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(k1_mcart_1(A_19),B_20)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66436,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66426,c_22])).

tff(c_66447,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60260,c_66436])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66495,plain,(
    m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66447,c_12])).

tff(c_357,plain,(
    ! [A_103,B_104,C_105] :
      ( k4_tarski('#skF_1'(A_103,B_104,C_105),'#skF_2'(A_103,B_104,C_105)) = A_103
      | ~ r2_hidden(A_103,k2_zfmisc_1(B_104,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [A_27,B_28] : k1_mcart_1(k4_tarski(A_27,B_28)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_370,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_mcart_1(A_103) = '#skF_1'(A_103,B_104,C_105)
      | ~ r2_hidden(A_103,k2_zfmisc_1(B_104,C_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_30])).

tff(c_66429,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = '#skF_1'(k1_mcart_1('#skF_7'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66426,c_370])).

tff(c_66441,plain,(
    '#skF_1'(k1_mcart_1('#skF_7'),'#skF_3','#skF_4') = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60260,c_66429])).

tff(c_494,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k6_mcart_1(A_122,B_123,C_124,D_125) = k2_mcart_1(k1_mcart_1(D_125))
      | ~ m1_subset_1(D_125,k3_zfmisc_1(A_122,B_123,C_124))
      | k1_xboole_0 = C_124
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_518,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_494])).

tff(c_527,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_518])).

tff(c_20,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(k2_mcart_1(A_19),C_21)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66434,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_66426,c_20])).

tff(c_66445,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_66434])).

tff(c_66470,plain,(
    m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_66445,c_12])).

tff(c_32,plain,(
    ! [A_27,B_28] : k2_mcart_1(k4_tarski(A_27,B_28)) = B_28 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_373,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_mcart_1(A_103) = '#skF_2'(A_103,B_104,C_105)
      | ~ r2_hidden(A_103,k2_zfmisc_1(B_104,C_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_32])).

tff(c_66432,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = '#skF_2'(k1_mcart_1('#skF_7'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66426,c_373])).

tff(c_66443,plain,(
    '#skF_2'(k1_mcart_1('#skF_7'),'#skF_3','#skF_4') = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_66432])).

tff(c_427,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k7_mcart_1(A_113,B_114,C_115,D_116) = k2_mcart_1(D_116)
      | ~ m1_subset_1(D_116,k3_zfmisc_1(A_113,B_114,C_115))
      | k1_xboole_0 = C_115
      | k1_xboole_0 = B_114
      | k1_xboole_0 = A_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_451,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_427])).

tff(c_460,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_451])).

tff(c_34,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_461,plain,(
    k2_mcart_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_34])).

tff(c_65492,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_65409])).

tff(c_65497,plain,(
    m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_65492,c_12])).

tff(c_60980,plain,(
    ! [A_2745,B_2746,C_2747] :
      ( k1_mcart_1(A_2745) = '#skF_1'(A_2745,B_2746,C_2747)
      | ~ r2_hidden(A_2745,k2_zfmisc_1(B_2746,C_2747)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_30])).

tff(c_64887,plain,(
    ! [A_3007,B_3008,C_3009] :
      ( k1_mcart_1(A_3007) = '#skF_1'(A_3007,B_3008,C_3009)
      | v1_xboole_0(k2_zfmisc_1(B_3008,C_3009))
      | ~ m1_subset_1(A_3007,k2_zfmisc_1(B_3008,C_3009)) ) ),
    inference(resolution,[status(thm)],[c_14,c_60980])).

tff(c_65002,plain,(
    ! [A_3007,A_16,B_17,C_18] :
      ( '#skF_1'(A_3007,k2_zfmisc_1(A_16,B_17),C_18) = k1_mcart_1(A_3007)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18))
      | ~ m1_subset_1(A_3007,k3_zfmisc_1(A_16,B_17,C_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_64887])).

tff(c_108464,plain,(
    ! [A_5023,A_5024,B_5025,C_5026] :
      ( '#skF_1'(A_5023,k2_zfmisc_1(A_5024,B_5025),C_5026) = k1_mcart_1(A_5023)
      | v1_xboole_0(k3_zfmisc_1(A_5024,B_5025,C_5026))
      | ~ m1_subset_1(A_5023,k3_zfmisc_1(A_5024,B_5025,C_5026)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_65002])).

tff(c_109095,plain,
    ( '#skF_1'('#skF_7',k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') = k1_mcart_1('#skF_7')
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_108464])).

tff(c_109256,plain,(
    '#skF_1'('#skF_7',k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') = k1_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_65493,c_109095])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4] :
      ( k4_tarski('#skF_1'(A_2,B_3,C_4),'#skF_2'(A_2,B_3,C_4)) = A_2
      | ~ r2_hidden(A_2,k2_zfmisc_1(B_3,C_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_109287,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),'#skF_2'('#skF_7',k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k2_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_109256,c_4])).

tff(c_109305,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),'#skF_2'('#skF_7',k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_109287])).

tff(c_109317,plain,(
    ~ r2_hidden('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_109305])).

tff(c_109320,plain,
    ( v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_14,c_109317])).

tff(c_109323,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_109320])).

tff(c_109325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65493,c_109323])).

tff(c_109327,plain,(
    r2_hidden('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_109305])).

tff(c_60646,plain,(
    ! [A_2723,B_2724,C_2725] :
      ( k2_mcart_1(A_2723) = '#skF_2'(A_2723,B_2724,C_2725)
      | ~ r2_hidden(A_2723,k2_zfmisc_1(B_2724,C_2725)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_32])).

tff(c_60693,plain,(
    ! [A_2723,A_16,B_17,C_18] :
      ( '#skF_2'(A_2723,k2_zfmisc_1(A_16,B_17),C_18) = k2_mcart_1(A_2723)
      | ~ r2_hidden(A_2723,k3_zfmisc_1(A_16,B_17,C_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_60646])).

tff(c_109341,plain,(
    '#skF_2'('#skF_7',k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') = k2_mcart_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_109327,c_60693])).

tff(c_109362,plain,
    ( k4_tarski('#skF_1'('#skF_7',k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k2_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_109341,c_4])).

tff(c_109372,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109327,c_18,c_109256,c_109362])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k4_tarski(k4_tarski(A_13,B_14),C_15) = k3_mcart_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62827,plain,(
    ! [A_2893,B_2894,C_2895,C_2896] :
      ( k3_mcart_1('#skF_1'(A_2893,B_2894,C_2895),'#skF_2'(A_2893,B_2894,C_2895),C_2896) = k4_tarski(A_2893,C_2896)
      | ~ r2_hidden(A_2893,k2_zfmisc_1(B_2894,C_2895)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_16])).

tff(c_42,plain,(
    ! [H_42,F_36,G_40] :
      ( H_42 = '#skF_6'
      | k3_mcart_1(F_36,G_40,H_42) != '#skF_7'
      | ~ m1_subset_1(H_42,'#skF_5')
      | ~ m1_subset_1(G_40,'#skF_4')
      | ~ m1_subset_1(F_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62867,plain,(
    ! [C_2896,A_2893,B_2894,C_2895] :
      ( C_2896 = '#skF_6'
      | k4_tarski(A_2893,C_2896) != '#skF_7'
      | ~ m1_subset_1(C_2896,'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_2893,B_2894,C_2895),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_2893,B_2894,C_2895),'#skF_3')
      | ~ r2_hidden(A_2893,k2_zfmisc_1(B_2894,C_2895)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62827,c_42])).

tff(c_109654,plain,(
    ! [B_2894,C_2895] :
      ( k2_mcart_1('#skF_7') = '#skF_6'
      | ~ m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_7'),B_2894,C_2895),'#skF_4')
      | ~ m1_subset_1('#skF_1'(k1_mcart_1('#skF_7'),B_2894,C_2895),'#skF_3')
      | ~ r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1(B_2894,C_2895)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109372,c_62867])).

tff(c_109781,plain,(
    ! [B_2894,C_2895] :
      ( k2_mcart_1('#skF_7') = '#skF_6'
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_7'),B_2894,C_2895),'#skF_4')
      | ~ m1_subset_1('#skF_1'(k1_mcart_1('#skF_7'),B_2894,C_2895),'#skF_3')
      | ~ r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1(B_2894,C_2895)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65497,c_109654])).

tff(c_112716,plain,(
    ! [B_5050,C_5051] :
      ( ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_7'),B_5050,C_5051),'#skF_4')
      | ~ m1_subset_1('#skF_1'(k1_mcart_1('#skF_7'),B_5050,C_5051),'#skF_3')
      | ~ r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1(B_5050,C_5051)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_109781])).

tff(c_112719,plain,
    ( ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_7'),'#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'(k1_mcart_1('#skF_7'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66426,c_112716])).

tff(c_112738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66495,c_66441,c_66470,c_66443,c_112719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.71/32.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.71/32.39  
% 43.71/32.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.71/32.39  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 43.71/32.39  
% 43.71/32.39  %Foreground sorts:
% 43.71/32.39  
% 43.71/32.39  
% 43.71/32.39  %Background operators:
% 43.71/32.39  
% 43.71/32.39  
% 43.71/32.39  %Foreground operators:
% 43.71/32.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 43.71/32.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.71/32.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 43.71/32.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 43.71/32.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 43.71/32.39  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 43.71/32.39  tff('#skF_7', type, '#skF_7': $i).
% 43.71/32.39  tff('#skF_5', type, '#skF_5': $i).
% 43.71/32.39  tff('#skF_6', type, '#skF_6': $i).
% 43.71/32.39  tff('#skF_3', type, '#skF_3': $i).
% 43.71/32.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 43.71/32.39  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 43.71/32.39  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 43.71/32.39  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 43.71/32.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.71/32.39  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 43.71/32.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 43.71/32.39  tff('#skF_4', type, '#skF_4': $i).
% 43.71/32.39  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 43.71/32.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.71/32.39  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 43.71/32.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 43.71/32.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 43.71/32.39  
% 43.71/32.41  tff(f_110, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 43.71/32.41  tff(f_82, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 43.71/32.41  tff(f_56, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 43.71/32.41  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 43.71/32.41  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 43.71/32.41  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 43.71/32.41  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 43.71/32.41  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 43.71/32.41  tff(f_36, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 43.71/32.41  tff(f_86, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 43.71/32.41  tff(f_54, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 43.71/32.41  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.71/32.41  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.71/32.41  tff(c_36, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.71/32.41  tff(c_44, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.71/32.41  tff(c_60212, plain, (![A_2665, B_2666, C_2667, D_2668]: (k5_mcart_1(A_2665, B_2666, C_2667, D_2668)=k1_mcart_1(k1_mcart_1(D_2668)) | ~m1_subset_1(D_2668, k3_zfmisc_1(A_2665, B_2666, C_2667)) | k1_xboole_0=C_2667 | k1_xboole_0=B_2666 | k1_xboole_0=A_2665)), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.71/32.41  tff(c_60248, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_60212])).
% 43.71/32.42  tff(c_60260, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_60248])).
% 43.71/32.42  tff(c_18, plain, (![A_16, B_17, C_18]: (k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)=k3_zfmisc_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 43.71/32.42  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 43.71/32.42  tff(c_212, plain, (![A_85, C_86, B_87]: (r2_hidden(k2_mcart_1(A_85), C_86) | ~r2_hidden(A_85, k2_zfmisc_1(B_87, C_86)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 43.71/32.42  tff(c_62586, plain, (![A_2875, C_2876, B_2877]: (r2_hidden(k2_mcart_1(A_2875), C_2876) | v1_xboole_0(k2_zfmisc_1(B_2877, C_2876)) | ~m1_subset_1(A_2875, k2_zfmisc_1(B_2877, C_2876)))), inference(resolution, [status(thm)], [c_14, c_212])).
% 43.71/32.42  tff(c_62624, plain, (![A_2875, C_18, A_16, B_17]: (r2_hidden(k2_mcart_1(A_2875), C_18) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)) | ~m1_subset_1(A_2875, k3_zfmisc_1(A_16, B_17, C_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_62586])).
% 43.71/32.42  tff(c_65274, plain, (![A_3035, C_3036, A_3037, B_3038]: (r2_hidden(k2_mcart_1(A_3035), C_3036) | v1_xboole_0(k3_zfmisc_1(A_3037, B_3038, C_3036)) | ~m1_subset_1(A_3035, k3_zfmisc_1(A_3037, B_3038, C_3036)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_62624])).
% 43.71/32.42  tff(c_65409, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_5') | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_65274])).
% 43.71/32.42  tff(c_65410, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_65409])).
% 43.71/32.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 43.71/32.42  tff(c_65414, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_65410, c_2])).
% 43.71/32.42  tff(c_266, plain, (![A_92, B_93, C_94]: (k2_zfmisc_1(k2_zfmisc_1(A_92, B_93), C_94)=k3_zfmisc_1(A_92, B_93, C_94))), inference(cnfTransformation, [status(thm)], [f_56])).
% 43.71/32.42  tff(c_6, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 43.71/32.42  tff(c_279, plain, (![C_94, A_92, B_93]: (k1_xboole_0=C_94 | k2_zfmisc_1(A_92, B_93)=k1_xboole_0 | k3_zfmisc_1(A_92, B_93, C_94)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_266, c_6])).
% 43.71/32.42  tff(c_65432, plain, (k1_xboole_0='#skF_5' | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_65414, c_279])).
% 43.71/32.42  tff(c_65449, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36, c_65432])).
% 43.71/32.42  tff(c_65480, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_65449, c_6])).
% 43.71/32.42  tff(c_65491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_65480])).
% 43.71/32.42  tff(c_65493, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_65409])).
% 43.71/32.42  tff(c_133, plain, (![A_62, B_63, C_64]: (r2_hidden(k1_mcart_1(A_62), B_63) | ~r2_hidden(A_62, k2_zfmisc_1(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 43.71/32.42  tff(c_62436, plain, (![A_2859, B_2860, C_2861]: (r2_hidden(k1_mcart_1(A_2859), B_2860) | v1_xboole_0(k2_zfmisc_1(B_2860, C_2861)) | ~m1_subset_1(A_2859, k2_zfmisc_1(B_2860, C_2861)))), inference(resolution, [status(thm)], [c_14, c_133])).
% 43.71/32.42  tff(c_62474, plain, (![A_2859, A_16, B_17, C_18]: (r2_hidden(k1_mcart_1(A_2859), k2_zfmisc_1(A_16, B_17)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)) | ~m1_subset_1(A_2859, k3_zfmisc_1(A_16, B_17, C_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_62436])).
% 43.71/32.42  tff(c_66289, plain, (![A_3095, A_3096, B_3097, C_3098]: (r2_hidden(k1_mcart_1(A_3095), k2_zfmisc_1(A_3096, B_3097)) | v1_xboole_0(k3_zfmisc_1(A_3096, B_3097, C_3098)) | ~m1_subset_1(A_3095, k3_zfmisc_1(A_3096, B_3097, C_3098)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_62474])).
% 43.71/32.42  tff(c_66389, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_66289])).
% 43.71/32.42  tff(c_66426, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_65493, c_66389])).
% 43.71/32.42  tff(c_22, plain, (![A_19, B_20, C_21]: (r2_hidden(k1_mcart_1(A_19), B_20) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 43.71/32.42  tff(c_66436, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), '#skF_3')), inference(resolution, [status(thm)], [c_66426, c_22])).
% 43.71/32.42  tff(c_66447, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60260, c_66436])).
% 43.71/32.42  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 43.71/32.42  tff(c_66495, plain, (m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(resolution, [status(thm)], [c_66447, c_12])).
% 43.71/32.42  tff(c_357, plain, (![A_103, B_104, C_105]: (k4_tarski('#skF_1'(A_103, B_104, C_105), '#skF_2'(A_103, B_104, C_105))=A_103 | ~r2_hidden(A_103, k2_zfmisc_1(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 43.71/32.42  tff(c_30, plain, (![A_27, B_28]: (k1_mcart_1(k4_tarski(A_27, B_28))=A_27)), inference(cnfTransformation, [status(thm)], [f_86])).
% 43.71/32.42  tff(c_370, plain, (![A_103, B_104, C_105]: (k1_mcart_1(A_103)='#skF_1'(A_103, B_104, C_105) | ~r2_hidden(A_103, k2_zfmisc_1(B_104, C_105)))), inference(superposition, [status(thm), theory('equality')], [c_357, c_30])).
% 43.71/32.42  tff(c_66429, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))='#skF_1'(k1_mcart_1('#skF_7'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66426, c_370])).
% 43.71/32.42  tff(c_66441, plain, ('#skF_1'(k1_mcart_1('#skF_7'), '#skF_3', '#skF_4')=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60260, c_66429])).
% 43.71/32.42  tff(c_494, plain, (![A_122, B_123, C_124, D_125]: (k6_mcart_1(A_122, B_123, C_124, D_125)=k2_mcart_1(k1_mcart_1(D_125)) | ~m1_subset_1(D_125, k3_zfmisc_1(A_122, B_123, C_124)) | k1_xboole_0=C_124 | k1_xboole_0=B_123 | k1_xboole_0=A_122)), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.71/32.42  tff(c_518, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_494])).
% 43.71/32.42  tff(c_527, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_518])).
% 43.71/32.42  tff(c_20, plain, (![A_19, C_21, B_20]: (r2_hidden(k2_mcart_1(A_19), C_21) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 43.71/32.42  tff(c_66434, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_4')), inference(resolution, [status(thm)], [c_66426, c_20])).
% 43.71/32.42  tff(c_66445, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_66434])).
% 43.71/32.42  tff(c_66470, plain, (m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_66445, c_12])).
% 43.71/32.42  tff(c_32, plain, (![A_27, B_28]: (k2_mcart_1(k4_tarski(A_27, B_28))=B_28)), inference(cnfTransformation, [status(thm)], [f_86])).
% 43.71/32.42  tff(c_373, plain, (![A_103, B_104, C_105]: (k2_mcart_1(A_103)='#skF_2'(A_103, B_104, C_105) | ~r2_hidden(A_103, k2_zfmisc_1(B_104, C_105)))), inference(superposition, [status(thm), theory('equality')], [c_357, c_32])).
% 43.71/32.42  tff(c_66432, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))='#skF_2'(k1_mcart_1('#skF_7'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66426, c_373])).
% 43.71/32.42  tff(c_66443, plain, ('#skF_2'(k1_mcart_1('#skF_7'), '#skF_3', '#skF_4')=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_66432])).
% 43.71/32.42  tff(c_427, plain, (![A_113, B_114, C_115, D_116]: (k7_mcart_1(A_113, B_114, C_115, D_116)=k2_mcart_1(D_116) | ~m1_subset_1(D_116, k3_zfmisc_1(A_113, B_114, C_115)) | k1_xboole_0=C_115 | k1_xboole_0=B_114 | k1_xboole_0=A_113)), inference(cnfTransformation, [status(thm)], [f_82])).
% 43.71/32.42  tff(c_451, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_427])).
% 43.71/32.42  tff(c_460, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_451])).
% 43.71/32.42  tff(c_34, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.71/32.42  tff(c_461, plain, (k2_mcart_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_34])).
% 43.71/32.42  tff(c_65492, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_65409])).
% 43.71/32.42  tff(c_65497, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_65492, c_12])).
% 43.71/32.42  tff(c_60980, plain, (![A_2745, B_2746, C_2747]: (k1_mcart_1(A_2745)='#skF_1'(A_2745, B_2746, C_2747) | ~r2_hidden(A_2745, k2_zfmisc_1(B_2746, C_2747)))), inference(superposition, [status(thm), theory('equality')], [c_357, c_30])).
% 43.71/32.42  tff(c_64887, plain, (![A_3007, B_3008, C_3009]: (k1_mcart_1(A_3007)='#skF_1'(A_3007, B_3008, C_3009) | v1_xboole_0(k2_zfmisc_1(B_3008, C_3009)) | ~m1_subset_1(A_3007, k2_zfmisc_1(B_3008, C_3009)))), inference(resolution, [status(thm)], [c_14, c_60980])).
% 43.71/32.42  tff(c_65002, plain, (![A_3007, A_16, B_17, C_18]: ('#skF_1'(A_3007, k2_zfmisc_1(A_16, B_17), C_18)=k1_mcart_1(A_3007) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)) | ~m1_subset_1(A_3007, k3_zfmisc_1(A_16, B_17, C_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_64887])).
% 43.71/32.42  tff(c_108464, plain, (![A_5023, A_5024, B_5025, C_5026]: ('#skF_1'(A_5023, k2_zfmisc_1(A_5024, B_5025), C_5026)=k1_mcart_1(A_5023) | v1_xboole_0(k3_zfmisc_1(A_5024, B_5025, C_5026)) | ~m1_subset_1(A_5023, k3_zfmisc_1(A_5024, B_5025, C_5026)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_65002])).
% 43.71/32.42  tff(c_109095, plain, ('#skF_1'('#skF_7', k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')=k1_mcart_1('#skF_7') | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_108464])).
% 43.71/32.42  tff(c_109256, plain, ('#skF_1'('#skF_7', k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')=k1_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_65493, c_109095])).
% 43.71/32.42  tff(c_4, plain, (![A_2, B_3, C_4]: (k4_tarski('#skF_1'(A_2, B_3, C_4), '#skF_2'(A_2, B_3, C_4))=A_2 | ~r2_hidden(A_2, k2_zfmisc_1(B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 43.71/32.42  tff(c_109287, plain, (k4_tarski(k1_mcart_1('#skF_7'), '#skF_2'('#skF_7', k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_7' | ~r2_hidden('#skF_7', k2_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_109256, c_4])).
% 43.71/32.42  tff(c_109305, plain, (k4_tarski(k1_mcart_1('#skF_7'), '#skF_2'('#skF_7', k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_7' | ~r2_hidden('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_109287])).
% 43.71/32.42  tff(c_109317, plain, (~r2_hidden('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_109305])).
% 43.71/32.42  tff(c_109320, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_14, c_109317])).
% 43.71/32.42  tff(c_109323, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_109320])).
% 43.71/32.42  tff(c_109325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65493, c_109323])).
% 43.71/32.42  tff(c_109327, plain, (r2_hidden('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_109305])).
% 43.71/32.42  tff(c_60646, plain, (![A_2723, B_2724, C_2725]: (k2_mcart_1(A_2723)='#skF_2'(A_2723, B_2724, C_2725) | ~r2_hidden(A_2723, k2_zfmisc_1(B_2724, C_2725)))), inference(superposition, [status(thm), theory('equality')], [c_357, c_32])).
% 43.71/32.42  tff(c_60693, plain, (![A_2723, A_16, B_17, C_18]: ('#skF_2'(A_2723, k2_zfmisc_1(A_16, B_17), C_18)=k2_mcart_1(A_2723) | ~r2_hidden(A_2723, k3_zfmisc_1(A_16, B_17, C_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_60646])).
% 43.71/32.42  tff(c_109341, plain, ('#skF_2'('#skF_7', k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')=k2_mcart_1('#skF_7')), inference(resolution, [status(thm)], [c_109327, c_60693])).
% 43.71/32.42  tff(c_109362, plain, (k4_tarski('#skF_1'('#skF_7', k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5'), k2_mcart_1('#skF_7'))='#skF_7' | ~r2_hidden('#skF_7', k2_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_109341, c_4])).
% 43.71/32.42  tff(c_109372, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_109327, c_18, c_109256, c_109362])).
% 43.71/32.42  tff(c_16, plain, (![A_13, B_14, C_15]: (k4_tarski(k4_tarski(A_13, B_14), C_15)=k3_mcart_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 43.71/32.42  tff(c_62827, plain, (![A_2893, B_2894, C_2895, C_2896]: (k3_mcart_1('#skF_1'(A_2893, B_2894, C_2895), '#skF_2'(A_2893, B_2894, C_2895), C_2896)=k4_tarski(A_2893, C_2896) | ~r2_hidden(A_2893, k2_zfmisc_1(B_2894, C_2895)))), inference(superposition, [status(thm), theory('equality')], [c_357, c_16])).
% 43.71/32.42  tff(c_42, plain, (![H_42, F_36, G_40]: (H_42='#skF_6' | k3_mcart_1(F_36, G_40, H_42)!='#skF_7' | ~m1_subset_1(H_42, '#skF_5') | ~m1_subset_1(G_40, '#skF_4') | ~m1_subset_1(F_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.71/32.42  tff(c_62867, plain, (![C_2896, A_2893, B_2894, C_2895]: (C_2896='#skF_6' | k4_tarski(A_2893, C_2896)!='#skF_7' | ~m1_subset_1(C_2896, '#skF_5') | ~m1_subset_1('#skF_2'(A_2893, B_2894, C_2895), '#skF_4') | ~m1_subset_1('#skF_1'(A_2893, B_2894, C_2895), '#skF_3') | ~r2_hidden(A_2893, k2_zfmisc_1(B_2894, C_2895)))), inference(superposition, [status(thm), theory('equality')], [c_62827, c_42])).
% 43.71/32.42  tff(c_109654, plain, (![B_2894, C_2895]: (k2_mcart_1('#skF_7')='#skF_6' | ~m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_7'), B_2894, C_2895), '#skF_4') | ~m1_subset_1('#skF_1'(k1_mcart_1('#skF_7'), B_2894, C_2895), '#skF_3') | ~r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1(B_2894, C_2895)))), inference(superposition, [status(thm), theory('equality')], [c_109372, c_62867])).
% 43.71/32.42  tff(c_109781, plain, (![B_2894, C_2895]: (k2_mcart_1('#skF_7')='#skF_6' | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_7'), B_2894, C_2895), '#skF_4') | ~m1_subset_1('#skF_1'(k1_mcart_1('#skF_7'), B_2894, C_2895), '#skF_3') | ~r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1(B_2894, C_2895)))), inference(demodulation, [status(thm), theory('equality')], [c_65497, c_109654])).
% 43.71/32.42  tff(c_112716, plain, (![B_5050, C_5051]: (~m1_subset_1('#skF_2'(k1_mcart_1('#skF_7'), B_5050, C_5051), '#skF_4') | ~m1_subset_1('#skF_1'(k1_mcart_1('#skF_7'), B_5050, C_5051), '#skF_3') | ~r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1(B_5050, C_5051)))), inference(negUnitSimplification, [status(thm)], [c_461, c_109781])).
% 43.71/32.42  tff(c_112719, plain, (~m1_subset_1('#skF_2'(k1_mcart_1('#skF_7'), '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'(k1_mcart_1('#skF_7'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_66426, c_112716])).
% 43.71/32.42  tff(c_112738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66495, c_66441, c_66470, c_66443, c_112719])).
% 43.71/32.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.71/32.42  
% 43.71/32.42  Inference rules
% 43.71/32.42  ----------------------
% 43.71/32.42  #Ref     : 0
% 43.71/32.42  #Sup     : 33007
% 43.71/32.42  #Fact    : 0
% 43.71/32.42  #Define  : 0
% 43.71/32.42  #Split   : 16
% 43.71/32.42  #Chain   : 0
% 43.71/32.42  #Close   : 0
% 43.71/32.42  
% 43.71/32.42  Ordering : KBO
% 43.71/32.42  
% 43.71/32.42  Simplification rules
% 43.71/32.42  ----------------------
% 43.71/32.42  #Subsume      : 5381
% 43.71/32.42  #Demod        : 5411
% 43.71/32.42  #Tautology    : 994
% 43.71/32.42  #SimpNegUnit  : 25
% 43.71/32.42  #BackRed      : 5
% 43.71/32.42  
% 43.71/32.42  #Partial instantiations: 0
% 43.71/32.42  #Strategies tried      : 1
% 43.71/32.42  
% 43.71/32.42  Timing (in seconds)
% 43.71/32.42  ----------------------
% 43.71/32.42  Preprocessing        : 0.33
% 43.71/32.42  Parsing              : 0.18
% 43.89/32.42  CNF conversion       : 0.02
% 43.89/32.42  Main loop            : 31.30
% 43.89/32.42  Inferencing          : 4.59
% 43.89/32.42  Reduction            : 6.03
% 43.89/32.42  Demodulation         : 4.19
% 43.89/32.42  BG Simplification    : 0.66
% 43.89/32.42  Subsumption          : 18.09
% 43.89/32.42  Abstraction          : 0.85
% 43.89/32.42  MUC search           : 0.00
% 43.89/32.42  Cooper               : 0.00
% 43.89/32.42  Total                : 31.68
% 43.89/32.42  Index Insertion      : 0.00
% 43.89/32.42  Index Deletion       : 0.00
% 43.89/32.42  Index Matching       : 0.00
% 43.89/32.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
