%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:09 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 332 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :   10
%              Number of atoms          :  176 ( 698 expanded)
%              Number of equality atoms :   13 ( 102 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( r2_hidden(k3_mcart_1(A,B,C),k3_zfmisc_1(D,E,F))
      <=> ( r2_hidden(A,D)
          & r2_hidden(B,E)
          & r2_hidden(C,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

tff(c_22,plain,
    ( r2_hidden('#skF_1','#skF_4')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_111,plain,(
    ~ r2_hidden('#skF_7','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_12,plain,(
    ! [A_17,B_18] : k1_mcart_1(k4_tarski(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [A_23,B_24,C_25] : k4_tarski(k4_tarski(A_23,B_24),C_25) = k3_mcart_1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_23,B_24,C_25] : k1_mcart_1(k3_mcart_1(A_23,B_24,C_25)) = k4_tarski(A_23,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_26,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] : k2_zfmisc_1(k2_zfmisc_1(A_4,B_5),C_6) = k3_zfmisc_1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden(k1_mcart_1(A_38),B_39)
      | ~ r2_hidden(A_38,k2_zfmisc_1(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [A_49,A_50,B_51,C_52] :
      ( r2_hidden(k1_mcart_1(A_49),k2_zfmisc_1(A_50,B_51))
      | ~ r2_hidden(A_49,k3_zfmisc_1(A_50,B_51,C_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_143,plain,(
    r2_hidden(k1_mcart_1(k3_mcart_1('#skF_7','#skF_8','#skF_9')),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_112,c_141])).

tff(c_145,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_143])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden(k1_mcart_1(A_7),B_8)
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    r2_hidden(k1_mcart_1(k4_tarski('#skF_7','#skF_8')),'#skF_10') ),
    inference(resolution,[status(thm)],[c_145,c_8])).

tff(c_151,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_151])).

tff(c_155,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_30,plain,
    ( r2_hidden('#skF_1','#skF_4')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,(
    r2_hidden('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_30])).

tff(c_28,plain,
    ( r2_hidden('#skF_2','#skF_5')
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_157,plain,(
    r2_hidden('#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_28])).

tff(c_14,plain,(
    ! [A_17,B_18] : k2_mcart_1(k4_tarski(A_17,B_18)) = B_18 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [D_15,E_16,B_11,C_12] :
      ( r2_hidden(k4_tarski(D_15,E_16),k2_zfmisc_1(B_11,C_12))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_15,E_16)),C_12)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_15,E_16)),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31,plain,(
    ! [D_15,E_16,B_11,C_12] :
      ( r2_hidden(k4_tarski(D_15,E_16),k2_zfmisc_1(B_11,C_12))
      | ~ r2_hidden(E_16,C_12)
      | ~ r2_hidden(D_15,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_10])).

tff(c_154,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_200,plain,(
    ! [D_65,E_66,B_67,C_68] :
      ( r2_hidden(k4_tarski(D_65,E_66),k2_zfmisc_1(B_67,C_68))
      | ~ r2_hidden(E_66,C_68)
      | ~ r2_hidden(D_65,B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_10])).

tff(c_215,plain,(
    ! [B_70,D_72,E_69,C_71,A_73] :
      ( r2_hidden(k4_tarski(D_72,E_69),k3_zfmisc_1(A_73,B_70,C_71))
      | ~ r2_hidden(E_69,C_71)
      | ~ r2_hidden(D_72,k2_zfmisc_1(A_73,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_200])).

tff(c_248,plain,(
    ! [C_81,B_79,A_83,B_80,A_84,C_82] :
      ( r2_hidden(k3_mcart_1(A_83,B_80,C_82),k3_zfmisc_1(A_84,B_79,C_81))
      | ~ r2_hidden(C_82,C_81)
      | ~ r2_hidden(k4_tarski(A_83,B_80),k2_zfmisc_1(A_84,B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_215])).

tff(c_24,plain,
    ( ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_247,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_24])).

tff(c_251,plain,
    ( ~ r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_248,c_247])).

tff(c_267,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_251])).

tff(c_277,plain,
    ( ~ r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_31,c_267])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_157,c_277])).

tff(c_283,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_20,plain,
    ( r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_285,plain,
    ( r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_20])).

tff(c_286,plain,(
    ~ r2_hidden('#skF_8','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_287,plain,(
    r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_335,plain,(
    ! [A_93,A_94,B_95,C_96] :
      ( r2_hidden(k1_mcart_1(A_93),k2_zfmisc_1(A_94,B_95))
      | ~ r2_hidden(A_93,k3_zfmisc_1(A_94,B_95,C_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_339,plain,(
    r2_hidden(k1_mcart_1(k3_mcart_1('#skF_7','#skF_8','#skF_9')),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_287,c_335])).

tff(c_342,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_339])).

tff(c_6,plain,(
    ! [A_7,C_9,B_8] :
      ( r2_hidden(k2_mcart_1(A_7),C_9)
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_346,plain,(
    r2_hidden(k2_mcart_1(k4_tarski('#skF_7','#skF_8')),'#skF_11') ),
    inference(resolution,[status(thm)],[c_342,c_6])).

tff(c_350,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_346])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_350])).

tff(c_353,plain,(
    r2_hidden('#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_354,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_355,plain,(
    r2_hidden('#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_28])).

tff(c_358,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_26])).

tff(c_401,plain,(
    ! [D_109,E_110,B_111,C_112] :
      ( r2_hidden(k4_tarski(D_109,E_110),k2_zfmisc_1(B_111,C_112))
      | ~ r2_hidden(E_110,C_112)
      | ~ r2_hidden(D_109,B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_10])).

tff(c_416,plain,(
    ! [C_114,D_115,A_117,E_116,B_113] :
      ( r2_hidden(k4_tarski(D_115,E_116),k3_zfmisc_1(A_117,B_113,C_114))
      | ~ r2_hidden(E_116,C_114)
      | ~ r2_hidden(D_115,k2_zfmisc_1(A_117,B_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_401])).

tff(c_451,plain,(
    ! [C_126,A_127,A_125,B_123,C_124,B_128] :
      ( r2_hidden(k3_mcart_1(A_127,B_123,C_126),k3_zfmisc_1(A_125,B_128,C_124))
      | ~ r2_hidden(C_126,C_124)
      | ~ r2_hidden(k4_tarski(A_127,B_123),k2_zfmisc_1(A_125,B_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_416])).

tff(c_450,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_24])).

tff(c_454,plain,
    ( ~ r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_451,c_450])).

tff(c_470,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_454])).

tff(c_480,plain,
    ( ~ r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_31,c_470])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_355,c_480])).

tff(c_485,plain,
    ( ~ r2_hidden('#skF_9','#skF_12')
    | r2_hidden('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_487,plain,(
    ~ r2_hidden('#skF_9','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_62,plain,(
    ! [A_23,B_24,C_25] : k2_mcart_1(k3_mcart_1(A_23,B_24,C_25)) = C_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_492,plain,(
    r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_90,plain,(
    ! [A_35,B_36,C_37] : k2_zfmisc_1(k2_zfmisc_1(A_35,B_36),C_37) = k3_zfmisc_1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_7,C_37,A_35,B_36] :
      ( r2_hidden(k2_mcart_1(A_7),C_37)
      | ~ r2_hidden(A_7,k3_zfmisc_1(A_35,B_36,C_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_6])).

tff(c_494,plain,(
    r2_hidden(k2_mcart_1(k3_mcart_1('#skF_7','#skF_8','#skF_9')),'#skF_12') ),
    inference(resolution,[status(thm)],[c_492,c_98])).

tff(c_496,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_494])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_496])).

tff(c_500,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_505,plain,(
    r2_hidden('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_30])).

tff(c_501,plain,(
    r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_501])).

tff(c_503,plain,(
    r2_hidden('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_499,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_549,plain,(
    ! [D_141,E_142,B_143,C_144] :
      ( r2_hidden(k4_tarski(D_141,E_142),k2_zfmisc_1(B_143,C_144))
      | ~ r2_hidden(E_142,C_144)
      | ~ r2_hidden(D_141,B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_10])).

tff(c_566,plain,(
    ! [C_148,A_149,D_145,E_147,B_146] :
      ( r2_hidden(k4_tarski(D_145,E_147),k3_zfmisc_1(A_149,B_146,C_148))
      | ~ r2_hidden(E_147,C_148)
      | ~ r2_hidden(D_145,k2_zfmisc_1(A_149,B_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_549])).

tff(c_598,plain,(
    ! [C_159,C_155,A_160,B_156,A_157,B_158] :
      ( r2_hidden(k3_mcart_1(A_160,B_158,C_159),k3_zfmisc_1(A_157,B_156,C_155))
      | ~ r2_hidden(C_159,C_155)
      | ~ r2_hidden(k4_tarski(A_160,B_158),k2_zfmisc_1(A_157,B_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_566])).

tff(c_521,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_24])).

tff(c_603,plain,
    ( ~ r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_598,c_521])).

tff(c_619,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_603])).

tff(c_627,plain,
    ( ~ r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_31,c_619])).

tff(c_631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_503,c_627])).

tff(c_633,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_486,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_282,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_12')
    | r2_hidden('#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_635,plain,(
    r2_hidden('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_486,c_282])).

tff(c_632,plain,(
    r2_hidden('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_18,plain,
    ( r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_644,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_486,c_633,c_18])).

tff(c_700,plain,(
    ! [D_173,E_174,B_175,C_176] :
      ( r2_hidden(k4_tarski(D_173,E_174),k2_zfmisc_1(B_175,C_176))
      | ~ r2_hidden(E_174,C_176)
      | ~ r2_hidden(D_173,B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_10])).

tff(c_731,plain,(
    ! [C_182,B_183,A_185,C_184,B_186] :
      ( r2_hidden(k3_mcart_1(A_185,B_183,C_184),k2_zfmisc_1(B_186,C_182))
      | ~ r2_hidden(C_184,C_182)
      | ~ r2_hidden(k4_tarski(A_185,B_183),B_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_700])).

tff(c_749,plain,(
    ! [B_188,A_187,B_190,A_192,C_191,C_189] :
      ( r2_hidden(k3_mcart_1(A_187,B_190,C_191),k3_zfmisc_1(A_192,B_188,C_189))
      | ~ r2_hidden(C_191,C_189)
      | ~ r2_hidden(k4_tarski(A_187,B_190),k2_zfmisc_1(A_192,B_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_731])).

tff(c_16,plain,
    ( ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_748,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_486,c_633,c_16])).

tff(c_752,plain,
    ( ~ r2_hidden('#skF_3','#skF_6')
    | ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_749,c_748])).

tff(c_765,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_752])).

tff(c_774,plain,
    ( ~ r2_hidden('#skF_2','#skF_5')
    | ~ r2_hidden('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_31,c_765])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_632,c_774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:03:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.42  
% 2.51/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.42  %$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12
% 2.51/1.42  
% 2.51/1.42  %Foreground sorts:
% 2.51/1.42  
% 2.51/1.42  
% 2.51/1.42  %Background operators:
% 2.51/1.42  
% 2.51/1.42  
% 2.51/1.42  %Foreground operators:
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.42  tff('#skF_11', type, '#skF_11': $i).
% 2.51/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.42  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.51/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.42  tff('#skF_10', type, '#skF_10': $i).
% 2.51/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.51/1.42  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.51/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.42  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.51/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.42  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.51/1.42  tff('#skF_12', type, '#skF_12': $i).
% 2.51/1.42  
% 2.51/1.44  tff(f_58, negated_conjecture, ~(![A, B, C, D, E, F]: (r2_hidden(k3_mcart_1(A, B, C), k3_zfmisc_1(D, E, F)) <=> ((r2_hidden(A, D) & r2_hidden(B, E)) & r2_hidden(C, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_mcart_1)).
% 2.51/1.44  tff(f_49, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.51/1.44  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.51/1.44  tff(f_29, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.51/1.44  tff(f_35, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.51/1.44  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_mcart_1)).
% 2.51/1.44  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_4') | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.44  tff(c_111, plain, (~r2_hidden('#skF_7', '#skF_10')), inference(splitLeft, [status(thm)], [c_22])).
% 2.51/1.44  tff(c_12, plain, (![A_17, B_18]: (k1_mcart_1(k4_tarski(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.51/1.44  tff(c_50, plain, (![A_23, B_24, C_25]: (k4_tarski(k4_tarski(A_23, B_24), C_25)=k3_mcart_1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.44  tff(c_59, plain, (![A_23, B_24, C_25]: (k1_mcart_1(k3_mcart_1(A_23, B_24, C_25))=k4_tarski(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_50, c_12])).
% 2.51/1.44  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_6') | r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.44  tff(c_112, plain, (r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.51/1.44  tff(c_4, plain, (![A_4, B_5, C_6]: (k2_zfmisc_1(k2_zfmisc_1(A_4, B_5), C_6)=k3_zfmisc_1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.44  tff(c_107, plain, (![A_38, B_39, C_40]: (r2_hidden(k1_mcart_1(A_38), B_39) | ~r2_hidden(A_38, k2_zfmisc_1(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.44  tff(c_141, plain, (![A_49, A_50, B_51, C_52]: (r2_hidden(k1_mcart_1(A_49), k2_zfmisc_1(A_50, B_51)) | ~r2_hidden(A_49, k3_zfmisc_1(A_50, B_51, C_52)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_107])).
% 2.51/1.44  tff(c_143, plain, (r2_hidden(k1_mcart_1(k3_mcart_1('#skF_7', '#skF_8', '#skF_9')), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_112, c_141])).
% 2.51/1.44  tff(c_145, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_143])).
% 2.51/1.44  tff(c_8, plain, (![A_7, B_8, C_9]: (r2_hidden(k1_mcart_1(A_7), B_8) | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.44  tff(c_147, plain, (r2_hidden(k1_mcart_1(k4_tarski('#skF_7', '#skF_8')), '#skF_10')), inference(resolution, [status(thm)], [c_145, c_8])).
% 2.51/1.44  tff(c_151, plain, (r2_hidden('#skF_7', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_147])).
% 2.51/1.44  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_151])).
% 2.51/1.44  tff(c_155, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitRight, [status(thm)], [c_26])).
% 2.51/1.44  tff(c_30, plain, (r2_hidden('#skF_1', '#skF_4') | r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.44  tff(c_156, plain, (r2_hidden('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_155, c_30])).
% 2.51/1.44  tff(c_28, plain, (r2_hidden('#skF_2', '#skF_5') | r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.44  tff(c_157, plain, (r2_hidden('#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_155, c_28])).
% 2.51/1.44  tff(c_14, plain, (![A_17, B_18]: (k2_mcart_1(k4_tarski(A_17, B_18))=B_18)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.51/1.44  tff(c_10, plain, (![D_15, E_16, B_11, C_12]: (r2_hidden(k4_tarski(D_15, E_16), k2_zfmisc_1(B_11, C_12)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_15, E_16)), C_12) | ~r2_hidden(k1_mcart_1(k4_tarski(D_15, E_16)), B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.44  tff(c_31, plain, (![D_15, E_16, B_11, C_12]: (r2_hidden(k4_tarski(D_15, E_16), k2_zfmisc_1(B_11, C_12)) | ~r2_hidden(E_16, C_12) | ~r2_hidden(D_15, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_10])).
% 2.51/1.44  tff(c_154, plain, (r2_hidden('#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_26])).
% 2.51/1.44  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski(k4_tarski(A_1, B_2), C_3)=k3_mcart_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.44  tff(c_200, plain, (![D_65, E_66, B_67, C_68]: (r2_hidden(k4_tarski(D_65, E_66), k2_zfmisc_1(B_67, C_68)) | ~r2_hidden(E_66, C_68) | ~r2_hidden(D_65, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_10])).
% 2.51/1.44  tff(c_215, plain, (![B_70, D_72, E_69, C_71, A_73]: (r2_hidden(k4_tarski(D_72, E_69), k3_zfmisc_1(A_73, B_70, C_71)) | ~r2_hidden(E_69, C_71) | ~r2_hidden(D_72, k2_zfmisc_1(A_73, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_200])).
% 2.51/1.44  tff(c_248, plain, (![C_81, B_79, A_83, B_80, A_84, C_82]: (r2_hidden(k3_mcart_1(A_83, B_80, C_82), k3_zfmisc_1(A_84, B_79, C_81)) | ~r2_hidden(C_82, C_81) | ~r2_hidden(k4_tarski(A_83, B_80), k2_zfmisc_1(A_84, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_215])).
% 2.51/1.44  tff(c_24, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.44  tff(c_247, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_155, c_24])).
% 2.51/1.44  tff(c_251, plain, (~r2_hidden('#skF_3', '#skF_6') | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_248, c_247])).
% 2.51/1.44  tff(c_267, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_251])).
% 2.51/1.44  tff(c_277, plain, (~r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_31, c_267])).
% 2.51/1.44  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_157, c_277])).
% 2.51/1.44  tff(c_283, plain, (r2_hidden('#skF_7', '#skF_10')), inference(splitRight, [status(thm)], [c_22])).
% 2.51/1.44  tff(c_20, plain, (r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.44  tff(c_285, plain, (r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_20])).
% 2.51/1.44  tff(c_286, plain, (~r2_hidden('#skF_8', '#skF_11')), inference(splitLeft, [status(thm)], [c_285])).
% 2.51/1.44  tff(c_287, plain, (r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.51/1.44  tff(c_335, plain, (![A_93, A_94, B_95, C_96]: (r2_hidden(k1_mcart_1(A_93), k2_zfmisc_1(A_94, B_95)) | ~r2_hidden(A_93, k3_zfmisc_1(A_94, B_95, C_96)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_107])).
% 2.51/1.44  tff(c_339, plain, (r2_hidden(k1_mcart_1(k3_mcart_1('#skF_7', '#skF_8', '#skF_9')), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_287, c_335])).
% 2.51/1.44  tff(c_342, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_339])).
% 2.51/1.44  tff(c_6, plain, (![A_7, C_9, B_8]: (r2_hidden(k2_mcart_1(A_7), C_9) | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.44  tff(c_346, plain, (r2_hidden(k2_mcart_1(k4_tarski('#skF_7', '#skF_8')), '#skF_11')), inference(resolution, [status(thm)], [c_342, c_6])).
% 2.51/1.44  tff(c_350, plain, (r2_hidden('#skF_8', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_346])).
% 2.51/1.44  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_350])).
% 2.51/1.44  tff(c_353, plain, (r2_hidden('#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.51/1.44  tff(c_354, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitRight, [status(thm)], [c_30])).
% 2.51/1.44  tff(c_355, plain, (r2_hidden('#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_354, c_28])).
% 2.51/1.44  tff(c_358, plain, (r2_hidden('#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_354, c_26])).
% 2.51/1.44  tff(c_401, plain, (![D_109, E_110, B_111, C_112]: (r2_hidden(k4_tarski(D_109, E_110), k2_zfmisc_1(B_111, C_112)) | ~r2_hidden(E_110, C_112) | ~r2_hidden(D_109, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_10])).
% 2.51/1.44  tff(c_416, plain, (![C_114, D_115, A_117, E_116, B_113]: (r2_hidden(k4_tarski(D_115, E_116), k3_zfmisc_1(A_117, B_113, C_114)) | ~r2_hidden(E_116, C_114) | ~r2_hidden(D_115, k2_zfmisc_1(A_117, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_401])).
% 2.51/1.44  tff(c_451, plain, (![C_126, A_127, A_125, B_123, C_124, B_128]: (r2_hidden(k3_mcart_1(A_127, B_123, C_126), k3_zfmisc_1(A_125, B_128, C_124)) | ~r2_hidden(C_126, C_124) | ~r2_hidden(k4_tarski(A_127, B_123), k2_zfmisc_1(A_125, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_416])).
% 2.51/1.44  tff(c_450, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_354, c_24])).
% 2.51/1.44  tff(c_454, plain, (~r2_hidden('#skF_3', '#skF_6') | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_451, c_450])).
% 2.51/1.44  tff(c_470, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_454])).
% 2.51/1.44  tff(c_480, plain, (~r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_31, c_470])).
% 2.51/1.44  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_355, c_480])).
% 2.51/1.44  tff(c_485, plain, (~r2_hidden('#skF_9', '#skF_12') | r2_hidden('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_285])).
% 2.51/1.44  tff(c_487, plain, (~r2_hidden('#skF_9', '#skF_12')), inference(splitLeft, [status(thm)], [c_485])).
% 2.51/1.44  tff(c_62, plain, (![A_23, B_24, C_25]: (k2_mcart_1(k3_mcart_1(A_23, B_24, C_25))=C_25)), inference(superposition, [status(thm), theory('equality')], [c_50, c_14])).
% 2.51/1.44  tff(c_492, plain, (r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.51/1.44  tff(c_90, plain, (![A_35, B_36, C_37]: (k2_zfmisc_1(k2_zfmisc_1(A_35, B_36), C_37)=k3_zfmisc_1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.44  tff(c_98, plain, (![A_7, C_37, A_35, B_36]: (r2_hidden(k2_mcart_1(A_7), C_37) | ~r2_hidden(A_7, k3_zfmisc_1(A_35, B_36, C_37)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_6])).
% 2.51/1.44  tff(c_494, plain, (r2_hidden(k2_mcart_1(k3_mcart_1('#skF_7', '#skF_8', '#skF_9')), '#skF_12')), inference(resolution, [status(thm)], [c_492, c_98])).
% 2.51/1.44  tff(c_496, plain, (r2_hidden('#skF_9', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_494])).
% 2.51/1.44  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_487, c_496])).
% 2.51/1.44  tff(c_500, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitRight, [status(thm)], [c_26])).
% 2.51/1.44  tff(c_505, plain, (r2_hidden('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_500, c_30])).
% 2.51/1.44  tff(c_501, plain, (r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.51/1.44  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_500, c_501])).
% 2.51/1.44  tff(c_503, plain, (r2_hidden('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 2.51/1.44  tff(c_499, plain, (r2_hidden('#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_26])).
% 2.51/1.44  tff(c_549, plain, (![D_141, E_142, B_143, C_144]: (r2_hidden(k4_tarski(D_141, E_142), k2_zfmisc_1(B_143, C_144)) | ~r2_hidden(E_142, C_144) | ~r2_hidden(D_141, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_10])).
% 2.51/1.44  tff(c_566, plain, (![C_148, A_149, D_145, E_147, B_146]: (r2_hidden(k4_tarski(D_145, E_147), k3_zfmisc_1(A_149, B_146, C_148)) | ~r2_hidden(E_147, C_148) | ~r2_hidden(D_145, k2_zfmisc_1(A_149, B_146)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_549])).
% 2.51/1.44  tff(c_598, plain, (![C_159, C_155, A_160, B_156, A_157, B_158]: (r2_hidden(k3_mcart_1(A_160, B_158, C_159), k3_zfmisc_1(A_157, B_156, C_155)) | ~r2_hidden(C_159, C_155) | ~r2_hidden(k4_tarski(A_160, B_158), k2_zfmisc_1(A_157, B_156)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_566])).
% 2.51/1.44  tff(c_521, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_500, c_24])).
% 2.51/1.44  tff(c_603, plain, (~r2_hidden('#skF_3', '#skF_6') | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_598, c_521])).
% 2.51/1.44  tff(c_619, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_603])).
% 2.51/1.44  tff(c_627, plain, (~r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_31, c_619])).
% 2.51/1.44  tff(c_631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_505, c_503, c_627])).
% 2.51/1.44  tff(c_633, plain, (r2_hidden('#skF_9', '#skF_12')), inference(splitRight, [status(thm)], [c_485])).
% 2.51/1.44  tff(c_486, plain, (r2_hidden('#skF_8', '#skF_11')), inference(splitRight, [status(thm)], [c_285])).
% 2.51/1.44  tff(c_282, plain, (~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_9', '#skF_12') | r2_hidden('#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 2.51/1.44  tff(c_635, plain, (r2_hidden('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_633, c_486, c_282])).
% 2.51/1.44  tff(c_632, plain, (r2_hidden('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_485])).
% 2.51/1.44  tff(c_18, plain, (r2_hidden('#skF_3', '#skF_6') | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.44  tff(c_644, plain, (r2_hidden('#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_486, c_633, c_18])).
% 2.51/1.44  tff(c_700, plain, (![D_173, E_174, B_175, C_176]: (r2_hidden(k4_tarski(D_173, E_174), k2_zfmisc_1(B_175, C_176)) | ~r2_hidden(E_174, C_176) | ~r2_hidden(D_173, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_10])).
% 2.51/1.44  tff(c_731, plain, (![C_182, B_183, A_185, C_184, B_186]: (r2_hidden(k3_mcart_1(A_185, B_183, C_184), k2_zfmisc_1(B_186, C_182)) | ~r2_hidden(C_184, C_182) | ~r2_hidden(k4_tarski(A_185, B_183), B_186))), inference(superposition, [status(thm), theory('equality')], [c_2, c_700])).
% 2.51/1.44  tff(c_749, plain, (![B_188, A_187, B_190, A_192, C_191, C_189]: (r2_hidden(k3_mcart_1(A_187, B_190, C_191), k3_zfmisc_1(A_192, B_188, C_189)) | ~r2_hidden(C_191, C_189) | ~r2_hidden(k4_tarski(A_187, B_190), k2_zfmisc_1(A_192, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_731])).
% 2.51/1.44  tff(c_16, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | ~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.44  tff(c_748, plain, (~r2_hidden(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_486, c_633, c_16])).
% 2.51/1.44  tff(c_752, plain, (~r2_hidden('#skF_3', '#skF_6') | ~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_749, c_748])).
% 2.51/1.44  tff(c_765, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_644, c_752])).
% 2.51/1.44  tff(c_774, plain, (~r2_hidden('#skF_2', '#skF_5') | ~r2_hidden('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_31, c_765])).
% 2.51/1.44  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_635, c_632, c_774])).
% 2.51/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.44  
% 2.51/1.44  Inference rules
% 2.51/1.44  ----------------------
% 2.51/1.44  #Ref     : 0
% 2.51/1.44  #Sup     : 163
% 2.51/1.44  #Fact    : 0
% 2.51/1.44  #Define  : 0
% 2.51/1.44  #Split   : 8
% 2.51/1.44  #Chain   : 0
% 2.51/1.44  #Close   : 0
% 2.51/1.44  
% 2.51/1.44  Ordering : KBO
% 2.51/1.44  
% 2.51/1.44  Simplification rules
% 2.51/1.44  ----------------------
% 2.51/1.44  #Subsume      : 38
% 2.51/1.44  #Demod        : 160
% 2.51/1.44  #Tautology    : 112
% 2.51/1.44  #SimpNegUnit  : 12
% 2.51/1.44  #BackRed      : 0
% 2.51/1.44  
% 2.51/1.44  #Partial instantiations: 0
% 2.51/1.44  #Strategies tried      : 1
% 2.51/1.44  
% 2.51/1.44  Timing (in seconds)
% 2.51/1.44  ----------------------
% 2.51/1.44  Preprocessing        : 0.28
% 2.51/1.44  Parsing              : 0.15
% 2.51/1.44  CNF conversion       : 0.02
% 2.51/1.44  Main loop            : 0.37
% 2.51/1.44  Inferencing          : 0.16
% 2.51/1.44  Reduction            : 0.12
% 2.51/1.44  Demodulation         : 0.09
% 2.51/1.44  BG Simplification    : 0.02
% 2.51/1.44  Subsumption          : 0.06
% 2.51/1.44  Abstraction          : 0.02
% 2.51/1.44  MUC search           : 0.00
% 2.51/1.44  Cooper               : 0.00
% 2.51/1.45  Total                : 0.70
% 2.51/1.45  Index Insertion      : 0.00
% 2.51/1.45  Index Deletion       : 0.00
% 2.51/1.45  Index Matching       : 0.00
% 2.51/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
