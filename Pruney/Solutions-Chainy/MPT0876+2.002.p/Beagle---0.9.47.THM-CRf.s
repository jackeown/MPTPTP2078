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
% DateTime   : Thu Dec  3 10:09:28 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  209 (4053 expanded)
%              Number of leaves         :   19 (1339 expanded)
%              Depth                    :   25
%              Number of atoms          :  390 (11495 expanded)
%              Number of equality atoms :  240 (9409 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_165,plain,(
    ! [A_31,B_32,C_33] :
      ( k3_zfmisc_1(A_31,B_32,C_33) != k1_xboole_0
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_168,plain,
    ( k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_178,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_168])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k3_zfmisc_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_309,plain,(
    ! [B_50,D_51,A_52,C_53] :
      ( r1_tarski(B_50,D_51)
      | k2_zfmisc_1(A_52,B_50) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_52,B_50),k2_zfmisc_1(C_53,D_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_312,plain,(
    ! [C_11,B_10,D_51,C_53,A_9] :
      ( r1_tarski(C_11,D_51)
      | k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_9,B_10,C_11),k2_zfmisc_1(C_53,D_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_309])).

tff(c_533,plain,(
    ! [C_78,D_77,C_80,A_81,B_79] :
      ( r1_tarski(C_80,D_77)
      | k3_zfmisc_1(A_81,B_79,C_80) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_81,B_79,C_80),k2_zfmisc_1(C_78,D_77)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_312])).

tff(c_542,plain,(
    ! [D_77,C_78] :
      ( r1_tarski('#skF_3',D_77)
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k2_zfmisc_1(C_78,D_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_533])).

tff(c_559,plain,(
    ! [D_77,C_78] :
      ( r1_tarski('#skF_3',D_77)
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k2_zfmisc_1(C_78,D_77)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_542])).

tff(c_571,plain,(
    ! [D_83,C_84] :
      ( r1_tarski('#skF_3',D_83)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k2_zfmisc_1(C_84,D_83)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_559])).

tff(c_581,plain,(
    ! [C_85,A_86,B_87] :
      ( r1_tarski('#skF_3',C_85)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),k3_zfmisc_1(A_86,B_87,C_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_571])).

tff(c_603,plain,(
    r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_581])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_606,plain,
    ( '#skF_6' = '#skF_3'
    | ~ r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_603,c_2])).

tff(c_607,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_684,plain,(
    ! [C_103,B_102,C_101,A_104,B_105,A_100] :
      ( r1_tarski(C_101,C_103)
      | k3_zfmisc_1(A_100,B_105,C_101) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_100,B_105,C_101),k3_zfmisc_1(A_104,B_102,C_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_533])).

tff(c_740,plain,(
    ! [C_108,A_109,B_110] :
      ( r1_tarski(C_108,'#skF_3')
      | k3_zfmisc_1(A_109,B_110,C_108) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_109,B_110,C_108),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_684])).

tff(c_759,plain,
    ( r1_tarski('#skF_6','#skF_3')
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_740])).

tff(c_770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_607,c_759])).

tff(c_771,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_779,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_178])).

tff(c_780,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_36])).

tff(c_253,plain,(
    ! [A_41,C_42,B_43,D_44] :
      ( r1_tarski(A_41,C_42)
      | k2_zfmisc_1(A_41,B_43) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_41,B_43),k2_zfmisc_1(C_42,D_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_256,plain,(
    ! [C_42,D_44,C_11,B_10,A_9] :
      ( r1_tarski(k2_zfmisc_1(A_9,B_10),C_42)
      | k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_9,B_10,C_11),k2_zfmisc_1(C_42,D_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_253])).

tff(c_945,plain,(
    ! [B_133,C_132,D_131,C_134,A_135] :
      ( r1_tarski(k2_zfmisc_1(A_135,B_133),C_132)
      | k3_zfmisc_1(A_135,B_133,C_134) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_135,B_133,C_134),k2_zfmisc_1(C_132,D_131)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_256])).

tff(c_948,plain,(
    ! [C_132,D_131] :
      ( r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),C_132)
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_3'),k2_zfmisc_1(C_132,D_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_945])).

tff(c_970,plain,(
    ! [C_132,D_131] :
      ( r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),C_132)
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_3'),k2_zfmisc_1(C_132,D_131)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_948])).

tff(c_976,plain,(
    ! [C_136,D_137] :
      ( r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),C_136)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_3'),k2_zfmisc_1(C_136,D_137)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_779,c_970])).

tff(c_986,plain,(
    ! [A_138,B_139,C_140] :
      ( r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(A_138,B_139))
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_5','#skF_3'),k3_zfmisc_1(A_138,B_139,C_140)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_976])).

tff(c_1011,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_986])).

tff(c_1026,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5')
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1011,c_2])).

tff(c_1036,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1026])).

tff(c_815,plain,(
    ! [C_114,A_111,A_115,B_113,B_112] :
      ( r1_tarski(A_111,k2_zfmisc_1(A_115,B_113))
      | k2_zfmisc_1(A_111,B_112) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_111,B_112),k3_zfmisc_1(A_115,B_113,C_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_253])).

tff(c_863,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(A_119,k2_zfmisc_1('#skF_1','#skF_2'))
      | k2_zfmisc_1(A_119,B_120) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_119,B_120),k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_815])).

tff(c_866,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(k2_zfmisc_1(A_9,B_10),k2_zfmisc_1('#skF_1','#skF_2'))
      | k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_9,B_10,C_11),k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_863])).

tff(c_1081,plain,(
    ! [A_147,B_148,C_149] :
      ( r1_tarski(k2_zfmisc_1(A_147,B_148),k2_zfmisc_1('#skF_1','#skF_2'))
      | k3_zfmisc_1(A_147,B_148,C_149) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_147,B_148,C_149),k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_866])).

tff(c_1100,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1081])).

tff(c_1111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_779,c_1036,c_1100])).

tff(c_1112,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1026])).

tff(c_129,plain,(
    ! [A_28,B_29,C_30] : k2_zfmisc_1(k2_zfmisc_1(A_28,B_29),C_30) = k3_zfmisc_1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_205,plain,(
    ! [A_37,B_38,C_39,C_40] : k3_zfmisc_1(k2_zfmisc_1(A_37,B_38),C_39,C_40) = k2_zfmisc_1(k3_zfmisc_1(A_37,B_38,C_39),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_18])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] :
      ( k3_zfmisc_1(A_12,B_13,C_14) != k1_xboole_0
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_451,plain,(
    ! [A_73,B_74,C_75,C_76] :
      ( k2_zfmisc_1(k3_zfmisc_1(A_73,B_74,C_75),C_76) != k1_xboole_0
      | k1_xboole_0 = C_76
      | k1_xboole_0 = C_75
      | k2_zfmisc_1(A_73,B_74) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_20])).

tff(c_457,plain,(
    ! [C_76] :
      ( k2_zfmisc_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),C_76) != k1_xboole_0
      | k1_xboole_0 = C_76
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_451])).

tff(c_472,plain,(
    ! [C_76] :
      ( k2_zfmisc_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),C_76) != k1_xboole_0
      | k1_xboole_0 = C_76
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_457])).

tff(c_482,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_514,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_8])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_514])).

tff(c_532,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_1118,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_532])).

tff(c_14,plain,(
    ! [B_6,D_8,A_5,C_7] :
      ( r1_tarski(B_6,D_8)
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_5,B_6),k2_zfmisc_1(C_7,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1014,plain,
    ( r1_tarski('#skF_2','#skF_5')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1011,c_14])).

tff(c_1022,plain,(
    r1_tarski('#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_1014])).

tff(c_1029,plain,
    ( '#skF_5' = '#skF_2'
    | ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1022,c_2])).

tff(c_1035,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1029])).

tff(c_1315,plain,(
    ! [B_162,A_163] :
      ( r1_tarski(B_162,'#skF_2')
      | k2_zfmisc_1(A_163,B_162) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_163,B_162),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_14])).

tff(c_1331,plain,
    ( r1_tarski('#skF_5','#skF_2')
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1315])).

tff(c_1341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1118,c_1035,c_1331])).

tff(c_1342,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1029])).

tff(c_1386,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_779])).

tff(c_1545,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_2')
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_1342,c_1026])).

tff(c_1546,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1545])).

tff(c_873,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(k2_zfmisc_1(A_9,B_10),k2_zfmisc_1('#skF_1','#skF_2'))
      | k3_zfmisc_1(A_9,B_10,C_11) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_9,B_10,C_11),k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_866])).

tff(c_1631,plain,(
    ! [A_192,B_193,C_194] :
      ( r1_tarski(k2_zfmisc_1(A_192,B_193),k2_zfmisc_1('#skF_1','#skF_2'))
      | k3_zfmisc_1(A_192,B_193,C_194) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_192,B_193,C_194),k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_873])).

tff(c_1650,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1631])).

tff(c_1661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1386,c_1546,c_1650])).

tff(c_1662,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1545])).

tff(c_1708,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1662,c_8])).

tff(c_1719,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_1708])).

tff(c_28,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_106,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_16,plain,(
    ! [A_5,C_7,B_6,D_8] :
      ( r1_tarski(A_5,C_7)
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_5,B_6),k2_zfmisc_1(C_7,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1017,plain,
    ( r1_tarski('#skF_1','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1011,c_16])).

tff(c_1025,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_1017])).

tff(c_1031,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1025,c_2])).

tff(c_1034,plain,(
    ~ r1_tarski('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_1031])).

tff(c_1920,plain,(
    ! [A_212,B_213] :
      ( r1_tarski(A_212,'#skF_1')
      | k2_zfmisc_1(A_212,B_213) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_212,B_213),k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1662,c_16])).

tff(c_1936,plain,
    ( r1_tarski('#skF_4','#skF_1')
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1920])).

tff(c_1946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1719,c_1034,c_1936])).

tff(c_1948,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1949,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_34])).

tff(c_1973,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_36])).

tff(c_2014,plain,(
    ! [A_221,B_222,C_223] :
      ( k3_zfmisc_1(A_221,B_222,C_223) != k1_xboole_0
      | k1_xboole_0 = C_223
      | k1_xboole_0 = B_222
      | k1_xboole_0 = A_221 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2017,plain,
    ( k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1973,c_2014])).

tff(c_2027,plain,
    ( k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1949,c_2017])).

tff(c_2034,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2027])).

tff(c_1947,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1954,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1947])).

tff(c_2103,plain,(
    ! [B_231,D_232,A_233,C_234] :
      ( r1_tarski(B_231,D_232)
      | k2_zfmisc_1(A_233,B_231) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_233,B_231),k2_zfmisc_1(C_234,D_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2106,plain,(
    ! [C_11,B_10,C_234,D_232,A_9] :
      ( r1_tarski(C_11,D_232)
      | k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_9,B_10,C_11),k2_zfmisc_1(C_234,D_232)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2103])).

tff(c_2556,plain,(
    ! [A_282,D_278,B_279,C_281,C_280] :
      ( r1_tarski(C_281,D_278)
      | k3_zfmisc_1(A_282,B_279,C_281) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_282,B_279,C_281),k2_zfmisc_1(C_280,D_278)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2106])).

tff(c_2565,plain,(
    ! [D_278,C_280] :
      ( r1_tarski('#skF_6',D_278)
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_280,D_278)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1973,c_2556])).

tff(c_2582,plain,(
    ! [D_278,C_280] :
      ( r1_tarski('#skF_6',D_278)
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_280,D_278)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_2565])).

tff(c_2587,plain,(
    ! [D_283,C_284] :
      ( r1_tarski('#skF_6',D_283)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_284,D_283)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2034,c_2582])).

tff(c_2805,plain,(
    ! [C_301,A_302,B_303] :
      ( r1_tarski('#skF_6',C_301)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k3_zfmisc_1(A_302,B_303,C_301)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2587])).

tff(c_2827,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2805])).

tff(c_2829,plain,
    ( '#skF_6' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_2827,c_2])).

tff(c_2832,plain,(
    ~ r1_tarski('#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1954,c_2829])).

tff(c_2244,plain,(
    ! [A_258,A_257,C_256,B_255,B_254] :
      ( r1_tarski(B_254,C_256)
      | k2_zfmisc_1(A_257,B_254) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_257,B_254),k3_zfmisc_1(A_258,B_255,C_256)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2103])).

tff(c_2302,plain,(
    ! [B_263,A_264] :
      ( r1_tarski(B_263,'#skF_6')
      | k2_zfmisc_1(A_264,B_263) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_264,B_263),k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1973,c_2244])).

tff(c_2305,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(C_11,'#skF_6')
      | k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_9,B_10,C_11),k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2302])).

tff(c_2940,plain,(
    ! [C_321,A_322,B_323] :
      ( r1_tarski(C_321,'#skF_6')
      | k3_zfmisc_1(A_322,B_323,C_321) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_322,B_323,C_321),k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2305])).

tff(c_2959,plain,
    ( r1_tarski('#skF_3','#skF_6')
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2940])).

tff(c_2970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2034,c_2832,c_2959])).

tff(c_2971,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2027])).

tff(c_2973,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2971])).

tff(c_2976,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2973,c_1949])).

tff(c_2982,plain,(
    '#skF_6' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2973,c_32])).

tff(c_2972,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2027])).

tff(c_3054,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2973,c_2972])).

tff(c_1978,plain,(
    ! [A_218,B_219,C_220] : k2_zfmisc_1(k2_zfmisc_1(A_218,B_219),C_220) = k3_zfmisc_1(A_218,B_219,C_220) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1987,plain,(
    ! [C_220,A_218,B_219] :
      ( k1_xboole_0 = C_220
      | k2_zfmisc_1(A_218,B_219) = k1_xboole_0
      | k3_zfmisc_1(A_218,B_219,C_220) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1978,c_8])).

tff(c_3154,plain,(
    ! [C_342,A_343,B_344] :
      ( C_342 = '#skF_6'
      | k2_zfmisc_1(A_343,B_344) = '#skF_6'
      | k3_zfmisc_1(A_343,B_344,C_342) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2973,c_2973,c_2973,c_1987])).

tff(c_3166,plain,
    ( '#skF_6' = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3054,c_3154])).

tff(c_3175,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1954,c_3166])).

tff(c_2975,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_6'
      | A_3 = '#skF_6'
      | k2_zfmisc_1(A_3,B_4) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2973,c_2973,c_2973,c_8])).

tff(c_3179,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3175,c_2975])).

tff(c_3200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2976,c_2982,c_3179])).

tff(c_3201,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2971])).

tff(c_3205,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_1949])).

tff(c_3211,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_32])).

tff(c_3212,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_30])).

tff(c_3258,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_2972])).

tff(c_3388,plain,(
    ! [C_363,A_364,B_365] :
      ( C_363 = '#skF_5'
      | k2_zfmisc_1(A_364,B_365) = '#skF_5'
      | k3_zfmisc_1(A_364,B_365,C_363) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_3201,c_3201,c_1987])).

tff(c_3400,plain,
    ( '#skF_5' = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3258,c_3388])).

tff(c_3409,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3212,c_3400])).

tff(c_3204,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_5'
      | A_3 = '#skF_5'
      | k2_zfmisc_1(A_3,B_4) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_3201,c_3201,c_8])).

tff(c_3413,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3409,c_3204])).

tff(c_3434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3205,c_3211,c_3413])).

tff(c_3436,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1947])).

tff(c_3459,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3436,c_1948,c_36])).

tff(c_3464,plain,(
    ! [A_370,B_371,C_372] : k2_zfmisc_1(k2_zfmisc_1(A_370,B_371),C_372) = k3_zfmisc_1(A_370,B_371,C_372) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3541,plain,(
    ! [A_379,B_380,C_381,C_382] : k3_zfmisc_1(k2_zfmisc_1(A_379,B_380),C_381,C_382) = k2_zfmisc_1(k3_zfmisc_1(A_379,B_380,C_381),C_382) ),
    inference(superposition,[status(thm),theory(equality)],[c_3464,c_18])).

tff(c_3759,plain,(
    ! [A_411,B_412,C_413,C_414] :
      ( k2_zfmisc_1(k3_zfmisc_1(A_411,B_412,C_413),C_414) != k1_xboole_0
      | k1_xboole_0 = C_414
      | k1_xboole_0 = C_413
      | k2_zfmisc_1(A_411,B_412) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3541,c_20])).

tff(c_3765,plain,(
    ! [C_414] :
      ( k2_zfmisc_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),C_414) != k1_xboole_0
      | k1_xboole_0 = C_414
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3459,c_3759])).

tff(c_3780,plain,(
    ! [C_414] :
      ( k2_zfmisc_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),C_414) != k1_xboole_0
      | k1_xboole_0 = C_414
      | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3765])).

tff(c_3790,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3780])).

tff(c_3819,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3790,c_8])).

tff(c_3833,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1949,c_3819])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3816,plain,(
    ! [C_11] : k3_zfmisc_1('#skF_4','#skF_5',C_11) = k2_zfmisc_1(k1_xboole_0,C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_3790,c_18])).

tff(c_3830,plain,(
    ! [C_11] : k3_zfmisc_1('#skF_4','#skF_5',C_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3816])).

tff(c_3933,plain,(
    ! [C_11] : k3_zfmisc_1('#skF_4','#skF_5',C_11) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3833,c_3830])).

tff(c_3934,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_3459])).

tff(c_3500,plain,(
    ! [A_373,B_374,C_375] :
      ( k3_zfmisc_1(A_373,B_374,C_375) != k1_xboole_0
      | k1_xboole_0 = C_375
      | k1_xboole_0 = B_374
      | k1_xboole_0 = A_373 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3503,plain,
    ( k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3459,c_3500])).

tff(c_3513,plain,
    ( k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1949,c_30,c_3503])).

tff(c_3520,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3513])).

tff(c_3845,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3833,c_3520])).

tff(c_3975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3934,c_3845])).

tff(c_3977,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3780])).

tff(c_3435,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1947])).

tff(c_3645,plain,(
    ! [A_392,C_393,B_394,D_395] :
      ( r1_tarski(A_392,C_393)
      | k2_zfmisc_1(A_392,B_394) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_392,B_394),k2_zfmisc_1(C_393,D_395)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4050,plain,(
    ! [A_440,B_439,A_436,B_437,C_438] :
      ( r1_tarski(A_436,k2_zfmisc_1(A_440,B_437))
      | k2_zfmisc_1(A_436,B_439) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_436,B_439),k3_zfmisc_1(A_440,B_437,C_438)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3645])).

tff(c_4101,plain,(
    ! [A_445,B_446] :
      ( r1_tarski(A_445,k2_zfmisc_1('#skF_4','#skF_5'))
      | k2_zfmisc_1(A_445,B_446) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_445,B_446),k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3459,c_4050])).

tff(c_4104,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(k2_zfmisc_1(A_9,B_10),k2_zfmisc_1('#skF_4','#skF_5'))
      | k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_9,B_10,C_11),k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4101])).

tff(c_4157,plain,(
    ! [A_453,B_454,C_455] :
      ( r1_tarski(k2_zfmisc_1(A_453,B_454),k2_zfmisc_1('#skF_4','#skF_5'))
      | k3_zfmisc_1(A_453,B_454,C_455) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_453,B_454,C_455),k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4104])).

tff(c_4176,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5'))
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_4157])).

tff(c_4186,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3520,c_4176])).

tff(c_4197,plain,
    ( r1_tarski('#skF_2','#skF_5')
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4186,c_14])).

tff(c_4199,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4197])).

tff(c_4241,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4199,c_8])).

tff(c_4258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1949,c_32,c_4241])).

tff(c_4259,plain,(
    r1_tarski('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_4197])).

tff(c_4262,plain,
    ( '#skF_5' = '#skF_2'
    | ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_4259,c_2])).

tff(c_4265,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3435,c_4262])).

tff(c_3648,plain,(
    ! [C_11,B_10,C_393,D_395,A_9] :
      ( r1_tarski(k2_zfmisc_1(A_9,B_10),C_393)
      | k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_9,B_10,C_11),k2_zfmisc_1(C_393,D_395)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3645])).

tff(c_4266,plain,(
    ! [A_460,C_456,B_457,C_458,D_459] :
      ( r1_tarski(k2_zfmisc_1(A_460,B_457),C_456)
      | k3_zfmisc_1(A_460,B_457,C_458) = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1(A_460,B_457,C_458),k2_zfmisc_1(C_456,D_459)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3648])).

tff(c_4275,plain,(
    ! [C_456,D_459] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),C_456)
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_456,D_459)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3459,c_4266])).

tff(c_4292,plain,(
    ! [C_456,D_459] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),C_456)
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_456,D_459)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3459,c_4275])).

tff(c_4297,plain,(
    ! [C_461,D_462] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),C_461)
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k2_zfmisc_1(C_461,D_462)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3520,c_4292])).

tff(c_4308,plain,(
    ! [A_463,B_464,C_465] :
      ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(A_463,B_464))
      | ~ r1_tarski(k3_zfmisc_1('#skF_4','#skF_2','#skF_3'),k3_zfmisc_1(A_463,B_464,C_465)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4297])).

tff(c_4333,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_4308])).

tff(c_4339,plain,
    ( r1_tarski('#skF_5','#skF_2')
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4333,c_14])).

tff(c_4348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3977,c_4265,c_4339])).

tff(c_4349,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3513])).

tff(c_4353,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4349,c_1949])).

tff(c_4360,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4349,c_30])).

tff(c_24,plain,(
    ! [A_12,C_14] : k3_zfmisc_1(A_12,k1_xboole_0,C_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4356,plain,(
    ! [A_12,C_14] : k3_zfmisc_1(A_12,'#skF_5',C_14) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4349,c_4349,c_24])).

tff(c_4432,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4356,c_3459])).

tff(c_4530,plain,(
    ! [A_484,B_485,C_486] :
      ( k3_zfmisc_1(A_484,B_485,C_486) != '#skF_5'
      | C_486 = '#skF_5'
      | B_485 = '#skF_5'
      | A_484 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4349,c_4349,c_4349,c_4349,c_20])).

tff(c_4536,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4432,c_4530])).

tff(c_4548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4353,c_3435,c_4360,c_4536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.99  
% 4.90/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.99  %$ r1_tarski > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.90/1.99  
% 4.90/1.99  %Foreground sorts:
% 4.90/1.99  
% 4.90/1.99  
% 4.90/1.99  %Background operators:
% 4.90/1.99  
% 4.90/1.99  
% 4.90/1.99  %Foreground operators:
% 4.90/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.90/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.90/1.99  tff('#skF_5', type, '#skF_5': $i).
% 4.90/1.99  tff('#skF_6', type, '#skF_6': $i).
% 4.90/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.90/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.90/1.99  tff('#skF_1', type, '#skF_1': $i).
% 4.90/1.99  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.90/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.90/1.99  tff('#skF_4', type, '#skF_4': $i).
% 4.90/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.99  
% 4.90/2.02  tff(f_74, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 4.90/2.02  tff(f_59, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 4.90/2.02  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.90/2.02  tff(f_47, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.90/2.02  tff(f_45, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 4.90/2.02  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.90/2.02  tff(c_34, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.90/2.02  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.90/2.02  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.90/2.02  tff(c_36, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.90/2.02  tff(c_165, plain, (![A_31, B_32, C_33]: (k3_zfmisc_1(A_31, B_32, C_33)!=k1_xboole_0 | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.90/2.02  tff(c_168, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_36, c_165])).
% 4.90/2.02  tff(c_178, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_168])).
% 4.90/2.02  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.90/2.02  tff(c_18, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k3_zfmisc_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.90/2.02  tff(c_309, plain, (![B_50, D_51, A_52, C_53]: (r1_tarski(B_50, D_51) | k2_zfmisc_1(A_52, B_50)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_52, B_50), k2_zfmisc_1(C_53, D_51)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.90/2.02  tff(c_312, plain, (![C_11, B_10, D_51, C_53, A_9]: (r1_tarski(C_11, D_51) | k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_9, B_10, C_11), k2_zfmisc_1(C_53, D_51)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_309])).
% 4.90/2.02  tff(c_533, plain, (![C_78, D_77, C_80, A_81, B_79]: (r1_tarski(C_80, D_77) | k3_zfmisc_1(A_81, B_79, C_80)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_81, B_79, C_80), k2_zfmisc_1(C_78, D_77)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_312])).
% 4.90/2.02  tff(c_542, plain, (![D_77, C_78]: (r1_tarski('#skF_3', D_77) | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k2_zfmisc_1(C_78, D_77)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_533])).
% 4.90/2.02  tff(c_559, plain, (![D_77, C_78]: (r1_tarski('#skF_3', D_77) | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k2_zfmisc_1(C_78, D_77)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_542])).
% 4.90/2.02  tff(c_571, plain, (![D_83, C_84]: (r1_tarski('#skF_3', D_83) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k2_zfmisc_1(C_84, D_83)))), inference(negUnitSimplification, [status(thm)], [c_178, c_559])).
% 4.90/2.02  tff(c_581, plain, (![C_85, A_86, B_87]: (r1_tarski('#skF_3', C_85) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), k3_zfmisc_1(A_86, B_87, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_571])).
% 4.90/2.02  tff(c_603, plain, (r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_581])).
% 4.90/2.02  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.90/2.02  tff(c_606, plain, ('#skF_6'='#skF_3' | ~r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_603, c_2])).
% 4.90/2.02  tff(c_607, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_606])).
% 4.90/2.02  tff(c_684, plain, (![C_103, B_102, C_101, A_104, B_105, A_100]: (r1_tarski(C_101, C_103) | k3_zfmisc_1(A_100, B_105, C_101)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_100, B_105, C_101), k3_zfmisc_1(A_104, B_102, C_103)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_533])).
% 4.90/2.02  tff(c_740, plain, (![C_108, A_109, B_110]: (r1_tarski(C_108, '#skF_3') | k3_zfmisc_1(A_109, B_110, C_108)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_109, B_110, C_108), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_684])).
% 4.90/2.02  tff(c_759, plain, (r1_tarski('#skF_6', '#skF_3') | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_740])).
% 4.90/2.02  tff(c_770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_607, c_759])).
% 4.90/2.02  tff(c_771, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_606])).
% 4.90/2.02  tff(c_779, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_771, c_178])).
% 4.90/2.02  tff(c_780, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_36])).
% 4.90/2.02  tff(c_253, plain, (![A_41, C_42, B_43, D_44]: (r1_tarski(A_41, C_42) | k2_zfmisc_1(A_41, B_43)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_41, B_43), k2_zfmisc_1(C_42, D_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.90/2.02  tff(c_256, plain, (![C_42, D_44, C_11, B_10, A_9]: (r1_tarski(k2_zfmisc_1(A_9, B_10), C_42) | k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_9, B_10, C_11), k2_zfmisc_1(C_42, D_44)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_253])).
% 4.90/2.02  tff(c_945, plain, (![B_133, C_132, D_131, C_134, A_135]: (r1_tarski(k2_zfmisc_1(A_135, B_133), C_132) | k3_zfmisc_1(A_135, B_133, C_134)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_135, B_133, C_134), k2_zfmisc_1(C_132, D_131)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_256])).
% 4.90/2.02  tff(c_948, plain, (![C_132, D_131]: (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), C_132) | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'), k2_zfmisc_1(C_132, D_131)))), inference(superposition, [status(thm), theory('equality')], [c_780, c_945])).
% 4.90/2.02  tff(c_970, plain, (![C_132, D_131]: (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), C_132) | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'), k2_zfmisc_1(C_132, D_131)))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_948])).
% 4.90/2.02  tff(c_976, plain, (![C_136, D_137]: (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), C_136) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'), k2_zfmisc_1(C_136, D_137)))), inference(negUnitSimplification, [status(thm)], [c_779, c_970])).
% 4.90/2.02  tff(c_986, plain, (![A_138, B_139, C_140]: (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(A_138, B_139)) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'), k3_zfmisc_1(A_138, B_139, C_140)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_976])).
% 4.90/2.02  tff(c_1011, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_986])).
% 4.90/2.02  tff(c_1026, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5') | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1011, c_2])).
% 4.90/2.02  tff(c_1036, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1026])).
% 4.90/2.02  tff(c_815, plain, (![C_114, A_111, A_115, B_113, B_112]: (r1_tarski(A_111, k2_zfmisc_1(A_115, B_113)) | k2_zfmisc_1(A_111, B_112)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_111, B_112), k3_zfmisc_1(A_115, B_113, C_114)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_253])).
% 4.90/2.02  tff(c_863, plain, (![A_119, B_120]: (r1_tarski(A_119, k2_zfmisc_1('#skF_1', '#skF_2')) | k2_zfmisc_1(A_119, B_120)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_119, B_120), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_780, c_815])).
% 4.90/2.02  tff(c_866, plain, (![A_9, B_10, C_11]: (r1_tarski(k2_zfmisc_1(A_9, B_10), k2_zfmisc_1('#skF_1', '#skF_2')) | k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_9, B_10, C_11), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_863])).
% 4.90/2.02  tff(c_1081, plain, (![A_147, B_148, C_149]: (r1_tarski(k2_zfmisc_1(A_147, B_148), k2_zfmisc_1('#skF_1', '#skF_2')) | k3_zfmisc_1(A_147, B_148, C_149)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_147, B_148, C_149), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_866])).
% 4.90/2.02  tff(c_1100, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1081])).
% 4.90/2.02  tff(c_1111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_779, c_1036, c_1100])).
% 4.90/2.02  tff(c_1112, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1026])).
% 4.90/2.02  tff(c_129, plain, (![A_28, B_29, C_30]: (k2_zfmisc_1(k2_zfmisc_1(A_28, B_29), C_30)=k3_zfmisc_1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.90/2.02  tff(c_205, plain, (![A_37, B_38, C_39, C_40]: (k3_zfmisc_1(k2_zfmisc_1(A_37, B_38), C_39, C_40)=k2_zfmisc_1(k3_zfmisc_1(A_37, B_38, C_39), C_40))), inference(superposition, [status(thm), theory('equality')], [c_129, c_18])).
% 4.90/2.02  tff(c_20, plain, (![A_12, B_13, C_14]: (k3_zfmisc_1(A_12, B_13, C_14)!=k1_xboole_0 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.90/2.02  tff(c_451, plain, (![A_73, B_74, C_75, C_76]: (k2_zfmisc_1(k3_zfmisc_1(A_73, B_74, C_75), C_76)!=k1_xboole_0 | k1_xboole_0=C_76 | k1_xboole_0=C_75 | k2_zfmisc_1(A_73, B_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_205, c_20])).
% 4.90/2.02  tff(c_457, plain, (![C_76]: (k2_zfmisc_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), C_76)!=k1_xboole_0 | k1_xboole_0=C_76 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_451])).
% 4.90/2.02  tff(c_472, plain, (![C_76]: (k2_zfmisc_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), C_76)!=k1_xboole_0 | k1_xboole_0=C_76 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_30, c_457])).
% 4.90/2.02  tff(c_482, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_472])).
% 4.90/2.02  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.90/2.02  tff(c_514, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_482, c_8])).
% 4.90/2.02  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_514])).
% 4.90/2.02  tff(c_532, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_472])).
% 4.90/2.02  tff(c_1118, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1112, c_532])).
% 4.90/2.02  tff(c_14, plain, (![B_6, D_8, A_5, C_7]: (r1_tarski(B_6, D_8) | k2_zfmisc_1(A_5, B_6)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_5, B_6), k2_zfmisc_1(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.90/2.02  tff(c_1014, plain, (r1_tarski('#skF_2', '#skF_5') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1011, c_14])).
% 4.90/2.02  tff(c_1022, plain, (r1_tarski('#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_532, c_1014])).
% 4.90/2.02  tff(c_1029, plain, ('#skF_5'='#skF_2' | ~r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1022, c_2])).
% 4.90/2.02  tff(c_1035, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_1029])).
% 4.90/2.02  tff(c_1315, plain, (![B_162, A_163]: (r1_tarski(B_162, '#skF_2') | k2_zfmisc_1(A_163, B_162)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_163, B_162), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1112, c_14])).
% 4.90/2.02  tff(c_1331, plain, (r1_tarski('#skF_5', '#skF_2') | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1315])).
% 4.90/2.02  tff(c_1341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1118, c_1035, c_1331])).
% 4.90/2.02  tff(c_1342, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_1029])).
% 4.90/2.02  tff(c_1386, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_779])).
% 4.90/2.02  tff(c_1545, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_2') | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_1342, c_1026])).
% 4.90/2.02  tff(c_1546, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1545])).
% 4.90/2.02  tff(c_873, plain, (![A_9, B_10, C_11]: (r1_tarski(k2_zfmisc_1(A_9, B_10), k2_zfmisc_1('#skF_1', '#skF_2')) | k3_zfmisc_1(A_9, B_10, C_11)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_9, B_10, C_11), k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_866])).
% 4.90/2.02  tff(c_1631, plain, (![A_192, B_193, C_194]: (r1_tarski(k2_zfmisc_1(A_192, B_193), k2_zfmisc_1('#skF_1', '#skF_2')) | k3_zfmisc_1(A_192, B_193, C_194)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_192, B_193, C_194), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_873])).
% 4.90/2.02  tff(c_1650, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1631])).
% 4.90/2.02  tff(c_1661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1386, c_1546, c_1650])).
% 4.90/2.02  tff(c_1662, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_1545])).
% 4.90/2.02  tff(c_1708, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1662, c_8])).
% 4.90/2.02  tff(c_1719, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_1708])).
% 4.90/2.02  tff(c_28, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.90/2.02  tff(c_106, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 4.90/2.02  tff(c_16, plain, (![A_5, C_7, B_6, D_8]: (r1_tarski(A_5, C_7) | k2_zfmisc_1(A_5, B_6)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_5, B_6), k2_zfmisc_1(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.90/2.02  tff(c_1017, plain, (r1_tarski('#skF_1', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1011, c_16])).
% 4.90/2.02  tff(c_1025, plain, (r1_tarski('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_532, c_1017])).
% 4.90/2.02  tff(c_1031, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1025, c_2])).
% 4.90/2.02  tff(c_1034, plain, (~r1_tarski('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_106, c_1031])).
% 4.90/2.02  tff(c_1920, plain, (![A_212, B_213]: (r1_tarski(A_212, '#skF_1') | k2_zfmisc_1(A_212, B_213)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_212, B_213), k2_zfmisc_1('#skF_4', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1662, c_16])).
% 4.90/2.02  tff(c_1936, plain, (r1_tarski('#skF_4', '#skF_1') | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1920])).
% 4.90/2.02  tff(c_1946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1719, c_1034, c_1936])).
% 4.90/2.02  tff(c_1948, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 4.90/2.02  tff(c_1949, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_34])).
% 4.90/2.02  tff(c_1973, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_36])).
% 4.90/2.02  tff(c_2014, plain, (![A_221, B_222, C_223]: (k3_zfmisc_1(A_221, B_222, C_223)!=k1_xboole_0 | k1_xboole_0=C_223 | k1_xboole_0=B_222 | k1_xboole_0=A_221)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.90/2.02  tff(c_2017, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1973, c_2014])).
% 4.90/2.02  tff(c_2027, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1949, c_2017])).
% 4.90/2.02  tff(c_2034, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2027])).
% 4.90/2.02  tff(c_1947, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 4.90/2.02  tff(c_1954, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_1947])).
% 4.90/2.02  tff(c_2103, plain, (![B_231, D_232, A_233, C_234]: (r1_tarski(B_231, D_232) | k2_zfmisc_1(A_233, B_231)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_233, B_231), k2_zfmisc_1(C_234, D_232)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.90/2.02  tff(c_2106, plain, (![C_11, B_10, C_234, D_232, A_9]: (r1_tarski(C_11, D_232) | k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_9, B_10, C_11), k2_zfmisc_1(C_234, D_232)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2103])).
% 4.90/2.02  tff(c_2556, plain, (![A_282, D_278, B_279, C_281, C_280]: (r1_tarski(C_281, D_278) | k3_zfmisc_1(A_282, B_279, C_281)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_282, B_279, C_281), k2_zfmisc_1(C_280, D_278)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2106])).
% 4.90/2.02  tff(c_2565, plain, (![D_278, C_280]: (r1_tarski('#skF_6', D_278) | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_280, D_278)))), inference(superposition, [status(thm), theory('equality')], [c_1973, c_2556])).
% 4.90/2.02  tff(c_2582, plain, (![D_278, C_280]: (r1_tarski('#skF_6', D_278) | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_280, D_278)))), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_2565])).
% 4.90/2.02  tff(c_2587, plain, (![D_283, C_284]: (r1_tarski('#skF_6', D_283) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_284, D_283)))), inference(negUnitSimplification, [status(thm)], [c_2034, c_2582])).
% 4.90/2.02  tff(c_2805, plain, (![C_301, A_302, B_303]: (r1_tarski('#skF_6', C_301) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k3_zfmisc_1(A_302, B_303, C_301)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2587])).
% 4.90/2.02  tff(c_2827, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_2805])).
% 4.90/2.02  tff(c_2829, plain, ('#skF_6'='#skF_3' | ~r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_2827, c_2])).
% 4.90/2.02  tff(c_2832, plain, (~r1_tarski('#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1954, c_2829])).
% 4.90/2.02  tff(c_2244, plain, (![A_258, A_257, C_256, B_255, B_254]: (r1_tarski(B_254, C_256) | k2_zfmisc_1(A_257, B_254)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_257, B_254), k3_zfmisc_1(A_258, B_255, C_256)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2103])).
% 4.90/2.02  tff(c_2302, plain, (![B_263, A_264]: (r1_tarski(B_263, '#skF_6') | k2_zfmisc_1(A_264, B_263)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_264, B_263), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1973, c_2244])).
% 4.90/2.02  tff(c_2305, plain, (![C_11, A_9, B_10]: (r1_tarski(C_11, '#skF_6') | k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_9, B_10, C_11), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2302])).
% 4.90/2.02  tff(c_2940, plain, (![C_321, A_322, B_323]: (r1_tarski(C_321, '#skF_6') | k3_zfmisc_1(A_322, B_323, C_321)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_322, B_323, C_321), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2305])).
% 4.90/2.02  tff(c_2959, plain, (r1_tarski('#skF_3', '#skF_6') | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2940])).
% 4.90/2.02  tff(c_2970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2034, c_2832, c_2959])).
% 4.90/2.02  tff(c_2971, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2027])).
% 4.90/2.02  tff(c_2973, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2971])).
% 4.90/2.02  tff(c_2976, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2973, c_1949])).
% 4.90/2.02  tff(c_2982, plain, ('#skF_6'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2973, c_32])).
% 4.90/2.02  tff(c_2972, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2027])).
% 4.90/2.02  tff(c_3054, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2973, c_2972])).
% 4.90/2.02  tff(c_1978, plain, (![A_218, B_219, C_220]: (k2_zfmisc_1(k2_zfmisc_1(A_218, B_219), C_220)=k3_zfmisc_1(A_218, B_219, C_220))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.90/2.02  tff(c_1987, plain, (![C_220, A_218, B_219]: (k1_xboole_0=C_220 | k2_zfmisc_1(A_218, B_219)=k1_xboole_0 | k3_zfmisc_1(A_218, B_219, C_220)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1978, c_8])).
% 4.90/2.02  tff(c_3154, plain, (![C_342, A_343, B_344]: (C_342='#skF_6' | k2_zfmisc_1(A_343, B_344)='#skF_6' | k3_zfmisc_1(A_343, B_344, C_342)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2973, c_2973, c_2973, c_1987])).
% 4.90/2.02  tff(c_3166, plain, ('#skF_6'='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3054, c_3154])).
% 4.90/2.02  tff(c_3175, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1954, c_3166])).
% 4.90/2.02  tff(c_2975, plain, (![B_4, A_3]: (B_4='#skF_6' | A_3='#skF_6' | k2_zfmisc_1(A_3, B_4)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2973, c_2973, c_2973, c_8])).
% 4.90/2.02  tff(c_3179, plain, ('#skF_6'='#skF_2' | '#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3175, c_2975])).
% 4.90/2.02  tff(c_3200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2976, c_2982, c_3179])).
% 4.90/2.02  tff(c_3201, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2971])).
% 4.90/2.02  tff(c_3205, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_1949])).
% 4.90/2.02  tff(c_3211, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_32])).
% 4.90/2.02  tff(c_3212, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_30])).
% 4.90/2.02  tff(c_3258, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_2972])).
% 4.90/2.02  tff(c_3388, plain, (![C_363, A_364, B_365]: (C_363='#skF_5' | k2_zfmisc_1(A_364, B_365)='#skF_5' | k3_zfmisc_1(A_364, B_365, C_363)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_3201, c_3201, c_1987])).
% 4.90/2.02  tff(c_3400, plain, ('#skF_5'='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3258, c_3388])).
% 4.90/2.02  tff(c_3409, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3212, c_3400])).
% 4.90/2.02  tff(c_3204, plain, (![B_4, A_3]: (B_4='#skF_5' | A_3='#skF_5' | k2_zfmisc_1(A_3, B_4)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_3201, c_3201, c_8])).
% 4.90/2.02  tff(c_3413, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3409, c_3204])).
% 4.90/2.02  tff(c_3434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3205, c_3211, c_3413])).
% 4.90/2.02  tff(c_3436, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1947])).
% 4.90/2.02  tff(c_3459, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3436, c_1948, c_36])).
% 4.90/2.02  tff(c_3464, plain, (![A_370, B_371, C_372]: (k2_zfmisc_1(k2_zfmisc_1(A_370, B_371), C_372)=k3_zfmisc_1(A_370, B_371, C_372))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.90/2.02  tff(c_3541, plain, (![A_379, B_380, C_381, C_382]: (k3_zfmisc_1(k2_zfmisc_1(A_379, B_380), C_381, C_382)=k2_zfmisc_1(k3_zfmisc_1(A_379, B_380, C_381), C_382))), inference(superposition, [status(thm), theory('equality')], [c_3464, c_18])).
% 4.90/2.02  tff(c_3759, plain, (![A_411, B_412, C_413, C_414]: (k2_zfmisc_1(k3_zfmisc_1(A_411, B_412, C_413), C_414)!=k1_xboole_0 | k1_xboole_0=C_414 | k1_xboole_0=C_413 | k2_zfmisc_1(A_411, B_412)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3541, c_20])).
% 4.90/2.02  tff(c_3765, plain, (![C_414]: (k2_zfmisc_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), C_414)!=k1_xboole_0 | k1_xboole_0=C_414 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3459, c_3759])).
% 4.90/2.02  tff(c_3780, plain, (![C_414]: (k2_zfmisc_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), C_414)!=k1_xboole_0 | k1_xboole_0=C_414 | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_30, c_3765])).
% 4.90/2.02  tff(c_3790, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3780])).
% 4.90/2.02  tff(c_3819, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3790, c_8])).
% 4.90/2.02  tff(c_3833, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1949, c_3819])).
% 4.90/2.02  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.90/2.02  tff(c_3816, plain, (![C_11]: (k3_zfmisc_1('#skF_4', '#skF_5', C_11)=k2_zfmisc_1(k1_xboole_0, C_11))), inference(superposition, [status(thm), theory('equality')], [c_3790, c_18])).
% 4.90/2.02  tff(c_3830, plain, (![C_11]: (k3_zfmisc_1('#skF_4', '#skF_5', C_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3816])).
% 4.90/2.02  tff(c_3933, plain, (![C_11]: (k3_zfmisc_1('#skF_4', '#skF_5', C_11)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3833, c_3830])).
% 4.90/2.02  tff(c_3934, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3933, c_3459])).
% 4.90/2.02  tff(c_3500, plain, (![A_373, B_374, C_375]: (k3_zfmisc_1(A_373, B_374, C_375)!=k1_xboole_0 | k1_xboole_0=C_375 | k1_xboole_0=B_374 | k1_xboole_0=A_373)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.90/2.02  tff(c_3503, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3459, c_3500])).
% 4.90/2.02  tff(c_3513, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1949, c_30, c_3503])).
% 4.90/2.02  tff(c_3520, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3513])).
% 4.90/2.02  tff(c_3845, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3833, c_3520])).
% 4.90/2.02  tff(c_3975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3934, c_3845])).
% 4.90/2.02  tff(c_3977, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3780])).
% 4.90/2.02  tff(c_3435, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_1947])).
% 4.90/2.02  tff(c_3645, plain, (![A_392, C_393, B_394, D_395]: (r1_tarski(A_392, C_393) | k2_zfmisc_1(A_392, B_394)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_392, B_394), k2_zfmisc_1(C_393, D_395)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.90/2.02  tff(c_4050, plain, (![A_440, B_439, A_436, B_437, C_438]: (r1_tarski(A_436, k2_zfmisc_1(A_440, B_437)) | k2_zfmisc_1(A_436, B_439)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_436, B_439), k3_zfmisc_1(A_440, B_437, C_438)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3645])).
% 4.90/2.02  tff(c_4101, plain, (![A_445, B_446]: (r1_tarski(A_445, k2_zfmisc_1('#skF_4', '#skF_5')) | k2_zfmisc_1(A_445, B_446)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_445, B_446), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3459, c_4050])).
% 4.90/2.02  tff(c_4104, plain, (![A_9, B_10, C_11]: (r1_tarski(k2_zfmisc_1(A_9, B_10), k2_zfmisc_1('#skF_4', '#skF_5')) | k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_9, B_10, C_11), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4101])).
% 4.90/2.02  tff(c_4157, plain, (![A_453, B_454, C_455]: (r1_tarski(k2_zfmisc_1(A_453, B_454), k2_zfmisc_1('#skF_4', '#skF_5')) | k3_zfmisc_1(A_453, B_454, C_455)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_453, B_454, C_455), k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4104])).
% 4.90/2.02  tff(c_4176, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5')) | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_4157])).
% 4.90/2.02  tff(c_4186, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3520, c_4176])).
% 4.90/2.02  tff(c_4197, plain, (r1_tarski('#skF_2', '#skF_5') | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_4186, c_14])).
% 4.90/2.02  tff(c_4199, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4197])).
% 4.90/2.02  tff(c_4241, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4199, c_8])).
% 4.90/2.02  tff(c_4258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1949, c_32, c_4241])).
% 4.90/2.02  tff(c_4259, plain, (r1_tarski('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_4197])).
% 4.90/2.02  tff(c_4262, plain, ('#skF_5'='#skF_2' | ~r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_4259, c_2])).
% 4.90/2.02  tff(c_4265, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3435, c_4262])).
% 4.90/2.02  tff(c_3648, plain, (![C_11, B_10, C_393, D_395, A_9]: (r1_tarski(k2_zfmisc_1(A_9, B_10), C_393) | k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_9, B_10, C_11), k2_zfmisc_1(C_393, D_395)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3645])).
% 4.90/2.02  tff(c_4266, plain, (![A_460, C_456, B_457, C_458, D_459]: (r1_tarski(k2_zfmisc_1(A_460, B_457), C_456) | k3_zfmisc_1(A_460, B_457, C_458)=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1(A_460, B_457, C_458), k2_zfmisc_1(C_456, D_459)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3648])).
% 4.90/2.02  tff(c_4275, plain, (![C_456, D_459]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), C_456) | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_456, D_459)))), inference(superposition, [status(thm), theory('equality')], [c_3459, c_4266])).
% 4.90/2.02  tff(c_4292, plain, (![C_456, D_459]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), C_456) | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_456, D_459)))), inference(demodulation, [status(thm), theory('equality')], [c_3459, c_4275])).
% 4.90/2.02  tff(c_4297, plain, (![C_461, D_462]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), C_461) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k2_zfmisc_1(C_461, D_462)))), inference(negUnitSimplification, [status(thm)], [c_3520, c_4292])).
% 4.90/2.02  tff(c_4308, plain, (![A_463, B_464, C_465]: (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(A_463, B_464)) | ~r1_tarski(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'), k3_zfmisc_1(A_463, B_464, C_465)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4297])).
% 4.90/2.02  tff(c_4333, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_4308])).
% 4.90/2.02  tff(c_4339, plain, (r1_tarski('#skF_5', '#skF_2') | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_4333, c_14])).
% 4.90/2.02  tff(c_4348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3977, c_4265, c_4339])).
% 4.90/2.02  tff(c_4349, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3513])).
% 4.90/2.02  tff(c_4353, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4349, c_1949])).
% 4.90/2.02  tff(c_4360, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4349, c_30])).
% 4.90/2.02  tff(c_24, plain, (![A_12, C_14]: (k3_zfmisc_1(A_12, k1_xboole_0, C_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.90/2.02  tff(c_4356, plain, (![A_12, C_14]: (k3_zfmisc_1(A_12, '#skF_5', C_14)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4349, c_4349, c_24])).
% 4.90/2.02  tff(c_4432, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4356, c_3459])).
% 4.90/2.02  tff(c_4530, plain, (![A_484, B_485, C_486]: (k3_zfmisc_1(A_484, B_485, C_486)!='#skF_5' | C_486='#skF_5' | B_485='#skF_5' | A_484='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4349, c_4349, c_4349, c_4349, c_20])).
% 4.90/2.02  tff(c_4536, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4432, c_4530])).
% 4.90/2.02  tff(c_4548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4353, c_3435, c_4360, c_4536])).
% 4.90/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/2.02  
% 4.90/2.02  Inference rules
% 4.90/2.02  ----------------------
% 4.90/2.02  #Ref     : 0
% 4.90/2.02  #Sup     : 1063
% 4.90/2.02  #Fact    : 0
% 4.90/2.02  #Define  : 0
% 4.90/2.02  #Split   : 22
% 4.90/2.02  #Chain   : 0
% 4.90/2.02  #Close   : 0
% 4.90/2.02  
% 4.90/2.02  Ordering : KBO
% 4.90/2.02  
% 4.90/2.02  Simplification rules
% 4.90/2.02  ----------------------
% 4.90/2.02  #Subsume      : 281
% 4.90/2.02  #Demod        : 997
% 4.90/2.02  #Tautology    : 588
% 4.90/2.02  #SimpNegUnit  : 90
% 4.90/2.02  #BackRed      : 133
% 4.90/2.02  
% 4.90/2.02  #Partial instantiations: 0
% 4.90/2.02  #Strategies tried      : 1
% 4.90/2.02  
% 4.90/2.02  Timing (in seconds)
% 4.90/2.02  ----------------------
% 4.90/2.02  Preprocessing        : 0.38
% 4.90/2.02  Parsing              : 0.21
% 4.90/2.02  CNF conversion       : 0.02
% 4.90/2.02  Main loop            : 0.82
% 4.90/2.02  Inferencing          : 0.27
% 4.90/2.03  Reduction            : 0.30
% 4.90/2.03  Demodulation         : 0.22
% 4.90/2.03  BG Simplification    : 0.03
% 4.90/2.03  Subsumption          : 0.17
% 4.90/2.03  Abstraction          : 0.04
% 4.90/2.03  MUC search           : 0.00
% 4.90/2.03  Cooper               : 0.00
% 4.90/2.03  Total                : 1.28
% 4.90/2.03  Index Insertion      : 0.00
% 4.90/2.03  Index Deletion       : 0.00
% 4.90/2.03  Index Matching       : 0.00
% 4.90/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
