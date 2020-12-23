%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0890+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:01 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 124 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 318 expanded)
%              Number of equality atoms :   99 ( 279 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                  & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                  & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k2_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') != k2_mcart_1('#skF_8')
    | k2_mcart_1(k1_mcart_1('#skF_8')) != k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')
    | k1_mcart_1(k1_mcart_1('#skF_8')) != k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) != k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_406,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k3_mcart_1(k5_mcart_1(A_120,B_121,C_122,D_123),k6_mcart_1(A_120,B_121,C_122,D_123),k7_mcart_1(A_120,B_121,C_122,D_123)) = D_123
      | ~ m1_subset_1(D_123,k3_zfmisc_1(A_120,B_121,C_122))
      | k1_xboole_0 = C_122
      | k1_xboole_0 = B_121
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_43,B_44,C_45] : k4_tarski(k4_tarski(A_43,B_44),C_45) = k3_mcart_1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [C_41,D_42,B_34,C_35] :
      ( k2_mcart_1(k4_tarski(C_41,D_42)) = D_42
      | k4_tarski(C_41,D_42) != k4_tarski(B_34,C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    ! [B_71,C_72] : k2_mcart_1(k4_tarski(B_71,C_72)) = C_72 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_96,plain,(
    ! [A_43,B_44,C_45] : k2_mcart_1(k3_mcart_1(A_43,B_44,C_45)) = C_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_511,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( k7_mcart_1(A_144,B_145,C_146,D_147) = k2_mcart_1(D_147)
      | ~ m1_subset_1(D_147,k3_zfmisc_1(A_144,B_145,C_146))
      | k1_xboole_0 = C_146
      | k1_xboole_0 = B_145
      | k1_xboole_0 = A_144 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_96])).

tff(c_514,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_511])).

tff(c_517,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_514])).

tff(c_16,plain,(
    ! [A_46,B_47,C_48,D_50] :
      ( k3_mcart_1(k5_mcart_1(A_46,B_47,C_48,D_50),k6_mcart_1(A_46,B_47,C_48,D_50),k7_mcart_1(A_46,B_47,C_48,D_50)) = D_50
      | ~ m1_subset_1(D_50,k3_zfmisc_1(A_46,B_47,C_48))
      | k1_xboole_0 = C_48
      | k1_xboole_0 = B_47
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_521,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_16])).

tff(c_525,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_521])).

tff(c_526,plain,(
    k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_525])).

tff(c_2,plain,(
    ! [C_20,D_21,B_13,C_14] :
      ( k1_mcart_1(k4_tarski(C_20,D_21)) = C_20
      | k4_tarski(C_20,D_21) != k4_tarski(B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [B_59,C_60] : k1_mcart_1(k4_tarski(B_59,C_60)) = B_59 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_60,plain,(
    ! [A_43,B_44,C_45] : k1_mcart_1(k3_mcart_1(A_43,B_44,C_45)) = k4_tarski(A_43,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_51])).

tff(c_1046,plain,(
    k4_tarski(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = k1_mcart_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_60])).

tff(c_44,plain,(
    ! [B_13,C_14] : k1_mcart_1(k4_tarski(B_13,C_14)) = B_13 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_1775,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_44])).

tff(c_1802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1775])).

tff(c_1803,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) != k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')
    | k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') != k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_1849,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') != k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1803])).

tff(c_2154,plain,(
    ! [A_2850,B_2851,C_2852,D_2853] :
      ( k3_mcart_1(k5_mcart_1(A_2850,B_2851,C_2852,D_2853),k6_mcart_1(A_2850,B_2851,C_2852,D_2853),k7_mcart_1(A_2850,B_2851,C_2852,D_2853)) = D_2853
      | ~ m1_subset_1(D_2853,k3_zfmisc_1(A_2850,B_2851,C_2852))
      | k1_xboole_0 = C_2852
      | k1_xboole_0 = B_2851
      | k1_xboole_0 = A_2850 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1824,plain,(
    ! [B_2800,C_2801] : k2_mcart_1(k4_tarski(B_2800,C_2801)) = C_2801 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_1833,plain,(
    ! [A_43,B_44,C_45] : k2_mcart_1(k3_mcart_1(A_43,B_44,C_45)) = C_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1824])).

tff(c_2652,plain,(
    ! [A_2886,B_2887,C_2888,D_2889] :
      ( k7_mcart_1(A_2886,B_2887,C_2888,D_2889) = k2_mcart_1(D_2889)
      | ~ m1_subset_1(D_2889,k3_zfmisc_1(A_2886,B_2887,C_2888))
      | k1_xboole_0 = C_2888
      | k1_xboole_0 = B_2887
      | k1_xboole_0 = A_2886 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2154,c_1833])).

tff(c_2655,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_2652])).

tff(c_2659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_1849,c_2655])).

tff(c_2660,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) != k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1803])).

tff(c_2661,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1803])).

tff(c_2969,plain,(
    ! [A_2932,B_2933,C_2934,D_2935] :
      ( k3_mcart_1(k5_mcart_1(A_2932,B_2933,C_2934,D_2935),k6_mcart_1(A_2932,B_2933,C_2934,D_2935),k7_mcart_1(A_2932,B_2933,C_2934,D_2935)) = D_2935
      | ~ m1_subset_1(D_2935,k3_zfmisc_1(A_2932,B_2933,C_2934))
      | k1_xboole_0 = C_2934
      | k1_xboole_0 = B_2933
      | k1_xboole_0 = A_2932 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2999,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_2969])).

tff(c_3003,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2999])).

tff(c_3004,plain,(
    k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_3003])).

tff(c_3029,plain,(
    k4_tarski(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = k1_mcart_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3004,c_60])).

tff(c_1816,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) = C_35 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_3679,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3029,c_1816])).

tff(c_3702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2660,c_3679])).

%------------------------------------------------------------------------------
