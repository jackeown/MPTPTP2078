%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:52 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 177 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 538 expanded)
%              Number of equality atoms :  133 ( 483 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ~ ! [E] :
                ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
               => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                  & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                  & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                  & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k2_mcart_1('#skF_5')
    | k2_mcart_1(k1_mcart_1('#skF_5')) != k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) != k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) != k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_73,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) != k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_16,plain,(
    m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_127,plain,(
    ! [A_48,E_47,D_49,C_50,B_46] :
      ( k4_mcart_1(k8_mcart_1(A_48,B_46,C_50,D_49,E_47),k9_mcart_1(A_48,B_46,C_50,D_49,E_47),k10_mcart_1(A_48,B_46,C_50,D_49,E_47),k11_mcart_1(A_48,B_46,C_50,D_49,E_47)) = E_47
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_48,B_46,C_50,D_49))
      | k1_xboole_0 = D_49
      | k1_xboole_0 = C_50
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ! [A_38,B_39,C_40,D_41] : k4_tarski(k3_mcart_1(A_38,B_39,C_40),D_41) = k4_mcart_1(A_38,B_39,C_40,D_41) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_18,B_19] : k2_mcart_1(k4_tarski(A_18,B_19)) = B_19 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    ! [A_38,B_39,C_40,D_41] : k2_mcart_1(k4_mcart_1(A_38,B_39,C_40,D_41)) = D_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_12])).

tff(c_268,plain,(
    ! [A_76,C_78,D_77,B_75,E_79] :
      ( k11_mcart_1(A_76,B_75,C_78,D_77,E_79) = k2_mcart_1(E_79)
      | ~ m1_subset_1(E_79,k4_zfmisc_1(A_76,B_75,C_78,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_78
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_76 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_101])).

tff(c_271,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_268])).

tff(c_274,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_271])).

tff(c_8,plain,(
    ! [D_15,E_17,C_14,A_12,B_13] :
      ( k4_mcart_1(k8_mcart_1(A_12,B_13,C_14,D_15,E_17),k9_mcart_1(A_12,B_13,C_14,D_15,E_17),k10_mcart_1(A_12,B_13,C_14,D_15,E_17),k11_mcart_1(A_12,B_13,C_14,D_15,E_17)) = E_17
      | ~ m1_subset_1(E_17,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_278,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_8])).

tff(c_282,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_278])).

tff(c_283,plain,(
    k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_282])).

tff(c_10,plain,(
    ! [A_18,B_19] : k1_mcart_1(k4_tarski(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    ! [A_38,B_39,C_40,D_41] : k1_mcart_1(k4_mcart_1(A_38,B_39,C_40,D_41)) = k3_mcart_1(A_38,B_39,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_10])).

tff(c_288,plain,(
    k3_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_104])).

tff(c_43,plain,(
    ! [A_25,B_26,C_27] : k4_tarski(k4_tarski(A_25,B_26),C_27) = k3_mcart_1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [A_25,B_26,C_27] : k1_mcart_1(k3_mcart_1(A_25,B_26,C_27)) = k4_tarski(A_25,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_10])).

tff(c_308,plain,(
    k4_tarski(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) = k1_mcart_1(k1_mcart_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_55])).

tff(c_334,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_10])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_334])).

tff(c_339,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) != k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k2_mcart_1(k1_mcart_1('#skF_5')) != k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k2_mcart_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_381,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k2_mcart_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_436,plain,(
    ! [E_104,B_103,A_105,C_107,D_106] :
      ( k4_mcart_1(k8_mcart_1(A_105,B_103,C_107,D_106,E_104),k9_mcart_1(A_105,B_103,C_107,D_106,E_104),k10_mcart_1(A_105,B_103,C_107,D_106,E_104),k11_mcart_1(A_105,B_103,C_107,D_106,E_104)) = E_104
      | ~ m1_subset_1(E_104,k4_zfmisc_1(A_105,B_103,C_107,D_106))
      | k1_xboole_0 = D_106
      | k1_xboole_0 = C_107
      | k1_xboole_0 = B_103
      | k1_xboole_0 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_363,plain,(
    ! [A_87,B_88,C_89,D_90] : k4_tarski(k3_mcart_1(A_87,B_88,C_89),D_90) = k4_mcart_1(A_87,B_88,C_89,D_90) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_372,plain,(
    ! [A_87,B_88,C_89,D_90] : k2_mcart_1(k4_mcart_1(A_87,B_88,C_89,D_90)) = D_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_12])).

tff(c_538,plain,(
    ! [B_126,D_124,C_127,A_125,E_128] :
      ( k11_mcart_1(A_125,B_126,C_127,D_124,E_128) = k2_mcart_1(E_128)
      | ~ m1_subset_1(E_128,k4_zfmisc_1(A_125,B_126,C_127,D_124))
      | k1_xboole_0 = D_124
      | k1_xboole_0 = C_127
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_125 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_372])).

tff(c_541,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_538])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_381,c_541])).

tff(c_546,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) != k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) != k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_570,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) != k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_547,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_663,plain,(
    ! [E_152,C_155,A_153,B_151,D_154] :
      ( k4_mcart_1(k8_mcart_1(A_153,B_151,C_155,D_154,E_152),k9_mcart_1(A_153,B_151,C_155,D_154,E_152),k10_mcart_1(A_153,B_151,C_155,D_154,E_152),k11_mcart_1(A_153,B_151,C_155,D_154,E_152)) = E_152
      | ~ m1_subset_1(E_152,k4_zfmisc_1(A_153,B_151,C_155,D_154))
      | k1_xboole_0 = D_154
      | k1_xboole_0 = C_155
      | k1_xboole_0 = B_151
      | k1_xboole_0 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_678,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_663])).

tff(c_682,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_678])).

tff(c_683,plain,(
    k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_682])).

tff(c_375,plain,(
    ! [A_87,B_88,C_89,D_90] : k1_mcart_1(k4_mcart_1(A_87,B_88,C_89,D_90)) = k3_mcart_1(A_87,B_88,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_10])).

tff(c_714,plain,(
    k3_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_375])).

tff(c_739,plain,(
    k4_tarski(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) = k1_mcart_1(k1_mcart_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_55])).

tff(c_762,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_12])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_762])).

tff(c_770,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) != k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_869,plain,(
    ! [E_177,A_178,D_179,C_180,B_176] :
      ( k4_mcart_1(k8_mcart_1(A_178,B_176,C_180,D_179,E_177),k9_mcart_1(A_178,B_176,C_180,D_179,E_177),k10_mcart_1(A_178,B_176,C_180,D_179,E_177),k11_mcart_1(A_178,B_176,C_180,D_179,E_177)) = E_177
      | ~ m1_subset_1(E_177,k4_zfmisc_1(A_178,B_176,C_180,D_179))
      | k1_xboole_0 = D_179
      | k1_xboole_0 = C_180
      | k1_xboole_0 = B_176
      | k1_xboole_0 = A_178 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_884,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_869])).

tff(c_888,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_884])).

tff(c_889,plain,(
    k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_888])).

tff(c_920,plain,(
    k3_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_375])).

tff(c_52,plain,(
    ! [A_25,B_26,C_27] : k2_mcart_1(k3_mcart_1(A_25,B_26,C_27)) = C_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_12])).

tff(c_947,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_52])).

tff(c_951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_770,c_947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:34:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  
% 2.86/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.86/1.41  
% 2.86/1.41  %Foreground sorts:
% 2.86/1.41  
% 2.86/1.41  
% 2.86/1.41  %Background operators:
% 2.86/1.41  
% 2.86/1.41  
% 2.86/1.41  %Foreground operators:
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.86/1.41  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.41  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.86/1.41  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.86/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.41  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.41  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.86/1.41  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.86/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.86/1.41  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.86/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.41  
% 2.86/1.43  tff(f_80, negated_conjecture, ~(![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 2.86/1.43  tff(f_50, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (E = k4_mcart_1(k8_mcart_1(A, B, C, D, E), k9_mcart_1(A, B, C, D, E), k10_mcart_1(A, B, C, D, E), k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_mcart_1)).
% 2.86/1.43  tff(f_29, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.86/1.43  tff(f_54, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.86/1.43  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.86/1.43  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.43  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.43  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.43  tff(c_18, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.43  tff(c_14, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_mcart_1('#skF_5') | k2_mcart_1(k1_mcart_1('#skF_5'))!=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))!=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))!=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.43  tff(c_73, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))!=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_14])).
% 2.86/1.43  tff(c_16, plain, (m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.43  tff(c_127, plain, (![A_48, E_47, D_49, C_50, B_46]: (k4_mcart_1(k8_mcart_1(A_48, B_46, C_50, D_49, E_47), k9_mcart_1(A_48, B_46, C_50, D_49, E_47), k10_mcart_1(A_48, B_46, C_50, D_49, E_47), k11_mcart_1(A_48, B_46, C_50, D_49, E_47))=E_47 | ~m1_subset_1(E_47, k4_zfmisc_1(A_48, B_46, C_50, D_49)) | k1_xboole_0=D_49 | k1_xboole_0=C_50 | k1_xboole_0=B_46 | k1_xboole_0=A_48)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.43  tff(c_92, plain, (![A_38, B_39, C_40, D_41]: (k4_tarski(k3_mcart_1(A_38, B_39, C_40), D_41)=k4_mcart_1(A_38, B_39, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.43  tff(c_12, plain, (![A_18, B_19]: (k2_mcart_1(k4_tarski(A_18, B_19))=B_19)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.86/1.43  tff(c_101, plain, (![A_38, B_39, C_40, D_41]: (k2_mcart_1(k4_mcart_1(A_38, B_39, C_40, D_41))=D_41)), inference(superposition, [status(thm), theory('equality')], [c_92, c_12])).
% 2.86/1.43  tff(c_268, plain, (![A_76, C_78, D_77, B_75, E_79]: (k11_mcart_1(A_76, B_75, C_78, D_77, E_79)=k2_mcart_1(E_79) | ~m1_subset_1(E_79, k4_zfmisc_1(A_76, B_75, C_78, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_78 | k1_xboole_0=B_75 | k1_xboole_0=A_76)), inference(superposition, [status(thm), theory('equality')], [c_127, c_101])).
% 2.86/1.43  tff(c_271, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_268])).
% 2.86/1.43  tff(c_274, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_271])).
% 2.86/1.43  tff(c_8, plain, (![D_15, E_17, C_14, A_12, B_13]: (k4_mcart_1(k8_mcart_1(A_12, B_13, C_14, D_15, E_17), k9_mcart_1(A_12, B_13, C_14, D_15, E_17), k10_mcart_1(A_12, B_13, C_14, D_15, E_17), k11_mcart_1(A_12, B_13, C_14, D_15, E_17))=E_17 | ~m1_subset_1(E_17, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.43  tff(c_278, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_274, c_8])).
% 2.86/1.43  tff(c_282, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_278])).
% 2.86/1.43  tff(c_283, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_282])).
% 2.86/1.43  tff(c_10, plain, (![A_18, B_19]: (k1_mcart_1(k4_tarski(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.86/1.43  tff(c_104, plain, (![A_38, B_39, C_40, D_41]: (k1_mcart_1(k4_mcart_1(A_38, B_39, C_40, D_41))=k3_mcart_1(A_38, B_39, C_40))), inference(superposition, [status(thm), theory('equality')], [c_92, c_10])).
% 2.86/1.43  tff(c_288, plain, (k3_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k1_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_283, c_104])).
% 2.86/1.43  tff(c_43, plain, (![A_25, B_26, C_27]: (k4_tarski(k4_tarski(A_25, B_26), C_27)=k3_mcart_1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.43  tff(c_55, plain, (![A_25, B_26, C_27]: (k1_mcart_1(k3_mcart_1(A_25, B_26, C_27))=k4_tarski(A_25, B_26))), inference(superposition, [status(thm), theory('equality')], [c_43, c_10])).
% 2.86/1.43  tff(c_308, plain, (k4_tarski(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k1_mcart_1(k1_mcart_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_288, c_55])).
% 2.86/1.43  tff(c_334, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_308, c_10])).
% 2.86/1.43  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_334])).
% 2.86/1.43  tff(c_339, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))!=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k2_mcart_1(k1_mcart_1('#skF_5'))!=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_mcart_1('#skF_5')), inference(splitRight, [status(thm)], [c_14])).
% 2.86/1.43  tff(c_381, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k2_mcart_1('#skF_5')), inference(splitLeft, [status(thm)], [c_339])).
% 2.86/1.43  tff(c_436, plain, (![E_104, B_103, A_105, C_107, D_106]: (k4_mcart_1(k8_mcart_1(A_105, B_103, C_107, D_106, E_104), k9_mcart_1(A_105, B_103, C_107, D_106, E_104), k10_mcart_1(A_105, B_103, C_107, D_106, E_104), k11_mcart_1(A_105, B_103, C_107, D_106, E_104))=E_104 | ~m1_subset_1(E_104, k4_zfmisc_1(A_105, B_103, C_107, D_106)) | k1_xboole_0=D_106 | k1_xboole_0=C_107 | k1_xboole_0=B_103 | k1_xboole_0=A_105)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.43  tff(c_363, plain, (![A_87, B_88, C_89, D_90]: (k4_tarski(k3_mcart_1(A_87, B_88, C_89), D_90)=k4_mcart_1(A_87, B_88, C_89, D_90))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.43  tff(c_372, plain, (![A_87, B_88, C_89, D_90]: (k2_mcart_1(k4_mcart_1(A_87, B_88, C_89, D_90))=D_90)), inference(superposition, [status(thm), theory('equality')], [c_363, c_12])).
% 2.86/1.43  tff(c_538, plain, (![B_126, D_124, C_127, A_125, E_128]: (k11_mcart_1(A_125, B_126, C_127, D_124, E_128)=k2_mcart_1(E_128) | ~m1_subset_1(E_128, k4_zfmisc_1(A_125, B_126, C_127, D_124)) | k1_xboole_0=D_124 | k1_xboole_0=C_127 | k1_xboole_0=B_126 | k1_xboole_0=A_125)), inference(superposition, [status(thm), theory('equality')], [c_436, c_372])).
% 2.86/1.43  tff(c_541, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_538])).
% 2.86/1.43  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_381, c_541])).
% 2.86/1.43  tff(c_546, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))!=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))!=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_339])).
% 2.86/1.43  tff(c_570, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))!=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_546])).
% 2.86/1.43  tff(c_547, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5')), inference(splitRight, [status(thm)], [c_339])).
% 2.86/1.43  tff(c_663, plain, (![E_152, C_155, A_153, B_151, D_154]: (k4_mcart_1(k8_mcart_1(A_153, B_151, C_155, D_154, E_152), k9_mcart_1(A_153, B_151, C_155, D_154, E_152), k10_mcart_1(A_153, B_151, C_155, D_154, E_152), k11_mcart_1(A_153, B_151, C_155, D_154, E_152))=E_152 | ~m1_subset_1(E_152, k4_zfmisc_1(A_153, B_151, C_155, D_154)) | k1_xboole_0=D_154 | k1_xboole_0=C_155 | k1_xboole_0=B_151 | k1_xboole_0=A_153)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.43  tff(c_678, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_547, c_663])).
% 2.86/1.43  tff(c_682, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_678])).
% 2.86/1.43  tff(c_683, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_682])).
% 2.86/1.43  tff(c_375, plain, (![A_87, B_88, C_89, D_90]: (k1_mcart_1(k4_mcart_1(A_87, B_88, C_89, D_90))=k3_mcart_1(A_87, B_88, C_89))), inference(superposition, [status(thm), theory('equality')], [c_363, c_10])).
% 2.86/1.43  tff(c_714, plain, (k3_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k1_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_683, c_375])).
% 2.86/1.43  tff(c_739, plain, (k4_tarski(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k1_mcart_1(k1_mcart_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_714, c_55])).
% 2.86/1.43  tff(c_762, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_739, c_12])).
% 2.86/1.43  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_570, c_762])).
% 2.86/1.43  tff(c_770, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))!=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_546])).
% 2.86/1.43  tff(c_869, plain, (![E_177, A_178, D_179, C_180, B_176]: (k4_mcart_1(k8_mcart_1(A_178, B_176, C_180, D_179, E_177), k9_mcart_1(A_178, B_176, C_180, D_179, E_177), k10_mcart_1(A_178, B_176, C_180, D_179, E_177), k11_mcart_1(A_178, B_176, C_180, D_179, E_177))=E_177 | ~m1_subset_1(E_177, k4_zfmisc_1(A_178, B_176, C_180, D_179)) | k1_xboole_0=D_179 | k1_xboole_0=C_180 | k1_xboole_0=B_176 | k1_xboole_0=A_178)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.43  tff(c_884, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_547, c_869])).
% 2.86/1.43  tff(c_888, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_884])).
% 2.86/1.43  tff(c_889, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_888])).
% 2.86/1.43  tff(c_920, plain, (k3_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k1_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_889, c_375])).
% 2.86/1.43  tff(c_52, plain, (![A_25, B_26, C_27]: (k2_mcart_1(k3_mcart_1(A_25, B_26, C_27))=C_27)), inference(superposition, [status(thm), theory('equality')], [c_43, c_12])).
% 2.86/1.43  tff(c_947, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_920, c_52])).
% 2.86/1.43  tff(c_951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_770, c_947])).
% 2.86/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.43  
% 2.86/1.43  Inference rules
% 2.86/1.43  ----------------------
% 2.86/1.43  #Ref     : 0
% 2.86/1.43  #Sup     : 230
% 2.86/1.43  #Fact    : 0
% 2.86/1.43  #Define  : 0
% 2.86/1.43  #Split   : 3
% 2.86/1.43  #Chain   : 0
% 2.86/1.43  #Close   : 0
% 2.86/1.43  
% 2.86/1.43  Ordering : KBO
% 2.86/1.43  
% 2.86/1.43  Simplification rules
% 2.86/1.43  ----------------------
% 2.86/1.43  #Subsume      : 0
% 2.86/1.43  #Demod        : 149
% 2.86/1.43  #Tautology    : 171
% 2.86/1.43  #SimpNegUnit  : 8
% 2.86/1.43  #BackRed      : 0
% 2.86/1.43  
% 2.86/1.43  #Partial instantiations: 0
% 2.86/1.43  #Strategies tried      : 1
% 2.86/1.43  
% 2.86/1.43  Timing (in seconds)
% 2.86/1.43  ----------------------
% 2.86/1.43  Preprocessing        : 0.29
% 2.86/1.43  Parsing              : 0.15
% 2.86/1.43  CNF conversion       : 0.02
% 2.86/1.43  Main loop            : 0.37
% 2.86/1.43  Inferencing          : 0.17
% 2.86/1.43  Reduction            : 0.12
% 2.86/1.43  Demodulation         : 0.09
% 2.86/1.43  BG Simplification    : 0.02
% 2.86/1.43  Subsumption          : 0.03
% 2.86/1.43  Abstraction          : 0.03
% 2.86/1.43  MUC search           : 0.00
% 2.86/1.43  Cooper               : 0.00
% 2.86/1.43  Total                : 0.68
% 2.86/1.43  Index Insertion      : 0.00
% 2.86/1.43  Index Deletion       : 0.00
% 2.86/1.43  Index Matching       : 0.00
% 2.86/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
