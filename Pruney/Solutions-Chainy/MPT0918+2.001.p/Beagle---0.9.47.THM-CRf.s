%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:14 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 158 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :    6
%              Number of atoms          :  129 ( 493 expanded)
%              Number of equality atoms :  118 ( 449 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
       => ~ ( A != k1_xboole_0
            & B != k1_xboole_0
            & C != k1_xboole_0
            & D != k1_xboole_0
            & ? [F,G,H,I] :
                ( E = k4_mcart_1(F,G,H,I)
                & ~ ( k8_mcart_1(A,B,C,D,E) = F
                    & k9_mcart_1(A,B,C,D,E) = G
                    & k10_mcart_1(A,B,C,D,E) = H
                    & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_72,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_18,plain,(
    ! [A_21,B_22] : k1_mcart_1(k4_tarski(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_124,plain,(
    ! [A_47,B_48,C_49,D_50] : k4_tarski(k3_mcart_1(A_47,B_48,C_49),D_50) = k4_mcart_1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_55,B_56,C_57,D_58] : k1_mcart_1(k4_mcart_1(A_55,B_56,C_57,D_58)) = k3_mcart_1(A_55,B_56,C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_18])).

tff(c_167,plain,(
    k3_mcart_1('#skF_6','#skF_7','#skF_8') = k1_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_158])).

tff(c_73,plain,(
    ! [A_34,B_35,C_36] : k4_tarski(k4_tarski(A_34,B_35),C_36) = k3_mcart_1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_34,B_35,C_36] : k1_mcart_1(k3_mcart_1(A_34,B_35,C_36)) = k4_tarski(A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_18])).

tff(c_176,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k4_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_82])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_537,plain,(
    ! [C_121,D_122,E_124,A_125,B_123] :
      ( k8_mcart_1(A_125,B_123,C_121,D_122,E_124) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_124)))
      | ~ m1_subset_1(E_124,k4_zfmisc_1(A_125,B_123,C_121,D_122))
      | k1_xboole_0 = D_122
      | k1_xboole_0 = C_121
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_543,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_537])).

tff(c_545,plain,
    ( k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_176,c_543])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_72,c_545])).

tff(c_548,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_584,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_606,plain,(
    ! [A_139,B_140,C_141,D_142] : k4_tarski(k3_mcart_1(A_139,B_140,C_141),D_142) = k4_mcart_1(A_139,B_140,C_141,D_142) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_21,B_22] : k2_mcart_1(k4_tarski(A_21,B_22)) = B_22 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_624,plain,(
    ! [A_143,B_144,C_145,D_146] : k2_mcart_1(k4_mcart_1(A_143,B_144,C_145,D_146)) = D_146 ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_20])).

tff(c_633,plain,(
    k2_mcart_1('#skF_5') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_624])).

tff(c_636,plain,(
    ! [C_147,D_148,B_149,E_150,A_151] :
      ( k11_mcart_1(A_151,B_149,C_147,D_148,E_150) = k2_mcart_1(E_150)
      | ~ m1_subset_1(E_150,k4_zfmisc_1(A_151,B_149,C_147,D_148))
      | k1_xboole_0 = D_148
      | k1_xboole_0 = C_147
      | k1_xboole_0 = B_149
      | k1_xboole_0 = A_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_639,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_636])).

tff(c_642,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_639])).

tff(c_647,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_642])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_584,c_647])).

tff(c_649,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_655,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_649])).

tff(c_677,plain,(
    ! [A_159,B_160,C_161,D_162] : k4_tarski(k3_mcart_1(A_159,B_160,C_161),D_162) = k4_mcart_1(A_159,B_160,C_161,D_162) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_719,plain,(
    ! [A_172,B_173,C_174,D_175] : k1_mcart_1(k4_mcart_1(A_172,B_173,C_174,D_175)) = k3_mcart_1(A_172,B_173,C_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_18])).

tff(c_728,plain,(
    k3_mcart_1('#skF_6','#skF_7','#skF_8') = k1_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_719])).

tff(c_554,plain,(
    ! [A_126,B_127,C_128] : k4_tarski(k4_tarski(A_126,B_127),C_128) = k3_mcart_1(A_126,B_127,C_128) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_563,plain,(
    ! [A_126,B_127,C_128] : k1_mcart_1(k3_mcart_1(A_126,B_127,C_128)) = k4_tarski(A_126,B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_18])).

tff(c_737,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k4_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_563])).

tff(c_961,plain,(
    ! [D_209,E_211,B_210,C_208,A_212] :
      ( k9_mcart_1(A_212,B_210,C_208,D_209,E_211) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_211)))
      | ~ m1_subset_1(E_211,k4_zfmisc_1(A_212,B_210,C_208,D_209))
      | k1_xboole_0 = D_209
      | k1_xboole_0 = C_208
      | k1_xboole_0 = B_210
      | k1_xboole_0 = A_212 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_965,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_961])).

tff(c_967,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_737,c_965])).

tff(c_969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_655,c_967])).

tff(c_970,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_649])).

tff(c_997,plain,(
    ! [A_220,B_221,C_222,D_223] : k4_tarski(k3_mcart_1(A_220,B_221,C_222),D_223) = k4_mcart_1(A_220,B_221,C_222,D_223) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1031,plain,(
    ! [A_228,B_229,C_230,D_231] : k1_mcart_1(k4_mcart_1(A_228,B_229,C_230,D_231)) = k3_mcart_1(A_228,B_229,C_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_18])).

tff(c_1040,plain,(
    k3_mcart_1('#skF_6','#skF_7','#skF_8') = k1_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1031])).

tff(c_566,plain,(
    ! [A_126,B_127,C_128] : k2_mcart_1(k3_mcart_1(A_126,B_127,C_128)) = C_128 ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_20])).

tff(c_1052,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_566])).

tff(c_1181,plain,(
    ! [C_249,B_251,E_252,D_250,A_253] :
      ( k2_mcart_1(k1_mcart_1(E_252)) = k10_mcart_1(A_253,B_251,C_249,D_250,E_252)
      | ~ m1_subset_1(E_252,k4_zfmisc_1(A_253,B_251,C_249,D_250))
      | k1_xboole_0 = D_250
      | k1_xboole_0 = C_249
      | k1_xboole_0 = B_251
      | k1_xboole_0 = A_253 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1184,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_1181])).

tff(c_1186,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_1184])).

tff(c_1188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_970,c_1186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:51:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.55  
% 3.21/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.56  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 3.21/1.56  
% 3.21/1.56  %Foreground sorts:
% 3.21/1.56  
% 3.21/1.56  
% 3.21/1.56  %Background operators:
% 3.21/1.56  
% 3.21/1.56  
% 3.21/1.56  %Foreground operators:
% 3.21/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.21/1.56  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.56  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.21/1.56  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.21/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.21/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.21/1.56  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.21/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.21/1.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.21/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.21/1.56  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.21/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.21/1.56  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.56  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.21/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.56  
% 3.21/1.57  tff(f_90, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 3.21/1.57  tff(f_62, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.21/1.57  tff(f_31, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.21/1.57  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.21/1.57  tff(f_58, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 3.21/1.57  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.57  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.57  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.57  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.57  tff(c_22, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.57  tff(c_72, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_22])).
% 3.21/1.57  tff(c_18, plain, (![A_21, B_22]: (k1_mcart_1(k4_tarski(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.21/1.57  tff(c_24, plain, (k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.57  tff(c_124, plain, (![A_47, B_48, C_49, D_50]: (k4_tarski(k3_mcart_1(A_47, B_48, C_49), D_50)=k4_mcart_1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.57  tff(c_158, plain, (![A_55, B_56, C_57, D_58]: (k1_mcart_1(k4_mcart_1(A_55, B_56, C_57, D_58))=k3_mcart_1(A_55, B_56, C_57))), inference(superposition, [status(thm), theory('equality')], [c_124, c_18])).
% 3.21/1.57  tff(c_167, plain, (k3_mcart_1('#skF_6', '#skF_7', '#skF_8')=k1_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24, c_158])).
% 3.21/1.57  tff(c_73, plain, (![A_34, B_35, C_36]: (k4_tarski(k4_tarski(A_34, B_35), C_36)=k3_mcart_1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.57  tff(c_82, plain, (![A_34, B_35, C_36]: (k1_mcart_1(k3_mcart_1(A_34, B_35, C_36))=k4_tarski(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_73, c_18])).
% 3.21/1.57  tff(c_176, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k4_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_167, c_82])).
% 3.21/1.57  tff(c_34, plain, (m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.57  tff(c_537, plain, (![C_121, D_122, E_124, A_125, B_123]: (k8_mcart_1(A_125, B_123, C_121, D_122, E_124)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_124))) | ~m1_subset_1(E_124, k4_zfmisc_1(A_125, B_123, C_121, D_122)) | k1_xboole_0=D_122 | k1_xboole_0=C_121 | k1_xboole_0=B_123 | k1_xboole_0=A_125)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.57  tff(c_543, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_537])).
% 3.21/1.57  tff(c_545, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_176, c_543])).
% 3.21/1.57  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_72, c_545])).
% 3.21/1.57  tff(c_548, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitRight, [status(thm)], [c_22])).
% 3.21/1.57  tff(c_584, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_548])).
% 3.21/1.57  tff(c_606, plain, (![A_139, B_140, C_141, D_142]: (k4_tarski(k3_mcart_1(A_139, B_140, C_141), D_142)=k4_mcart_1(A_139, B_140, C_141, D_142))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.57  tff(c_20, plain, (![A_21, B_22]: (k2_mcart_1(k4_tarski(A_21, B_22))=B_22)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.21/1.57  tff(c_624, plain, (![A_143, B_144, C_145, D_146]: (k2_mcart_1(k4_mcart_1(A_143, B_144, C_145, D_146))=D_146)), inference(superposition, [status(thm), theory('equality')], [c_606, c_20])).
% 3.21/1.57  tff(c_633, plain, (k2_mcart_1('#skF_5')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_24, c_624])).
% 3.21/1.57  tff(c_636, plain, (![C_147, D_148, B_149, E_150, A_151]: (k11_mcart_1(A_151, B_149, C_147, D_148, E_150)=k2_mcart_1(E_150) | ~m1_subset_1(E_150, k4_zfmisc_1(A_151, B_149, C_147, D_148)) | k1_xboole_0=D_148 | k1_xboole_0=C_147 | k1_xboole_0=B_149 | k1_xboole_0=A_151)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.57  tff(c_639, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_636])).
% 3.21/1.57  tff(c_642, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_639])).
% 3.21/1.57  tff(c_647, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_633, c_642])).
% 3.21/1.57  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_584, c_647])).
% 3.21/1.57  tff(c_649, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_548])).
% 3.21/1.57  tff(c_655, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_649])).
% 3.21/1.57  tff(c_677, plain, (![A_159, B_160, C_161, D_162]: (k4_tarski(k3_mcart_1(A_159, B_160, C_161), D_162)=k4_mcart_1(A_159, B_160, C_161, D_162))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.57  tff(c_719, plain, (![A_172, B_173, C_174, D_175]: (k1_mcart_1(k4_mcart_1(A_172, B_173, C_174, D_175))=k3_mcart_1(A_172, B_173, C_174))), inference(superposition, [status(thm), theory('equality')], [c_677, c_18])).
% 3.21/1.57  tff(c_728, plain, (k3_mcart_1('#skF_6', '#skF_7', '#skF_8')=k1_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24, c_719])).
% 3.21/1.57  tff(c_554, plain, (![A_126, B_127, C_128]: (k4_tarski(k4_tarski(A_126, B_127), C_128)=k3_mcart_1(A_126, B_127, C_128))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.57  tff(c_563, plain, (![A_126, B_127, C_128]: (k1_mcart_1(k3_mcart_1(A_126, B_127, C_128))=k4_tarski(A_126, B_127))), inference(superposition, [status(thm), theory('equality')], [c_554, c_18])).
% 3.21/1.57  tff(c_737, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k4_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_728, c_563])).
% 3.21/1.57  tff(c_961, plain, (![D_209, E_211, B_210, C_208, A_212]: (k9_mcart_1(A_212, B_210, C_208, D_209, E_211)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_211))) | ~m1_subset_1(E_211, k4_zfmisc_1(A_212, B_210, C_208, D_209)) | k1_xboole_0=D_209 | k1_xboole_0=C_208 | k1_xboole_0=B_210 | k1_xboole_0=A_212)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.57  tff(c_965, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_961])).
% 3.21/1.57  tff(c_967, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_737, c_965])).
% 3.21/1.57  tff(c_969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_655, c_967])).
% 3.21/1.57  tff(c_970, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_649])).
% 3.21/1.57  tff(c_997, plain, (![A_220, B_221, C_222, D_223]: (k4_tarski(k3_mcart_1(A_220, B_221, C_222), D_223)=k4_mcart_1(A_220, B_221, C_222, D_223))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.57  tff(c_1031, plain, (![A_228, B_229, C_230, D_231]: (k1_mcart_1(k4_mcart_1(A_228, B_229, C_230, D_231))=k3_mcart_1(A_228, B_229, C_230))), inference(superposition, [status(thm), theory('equality')], [c_997, c_18])).
% 3.21/1.57  tff(c_1040, plain, (k3_mcart_1('#skF_6', '#skF_7', '#skF_8')=k1_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1031])).
% 3.21/1.57  tff(c_566, plain, (![A_126, B_127, C_128]: (k2_mcart_1(k3_mcart_1(A_126, B_127, C_128))=C_128)), inference(superposition, [status(thm), theory('equality')], [c_554, c_20])).
% 3.21/1.57  tff(c_1052, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1040, c_566])).
% 3.21/1.57  tff(c_1181, plain, (![C_249, B_251, E_252, D_250, A_253]: (k2_mcart_1(k1_mcart_1(E_252))=k10_mcart_1(A_253, B_251, C_249, D_250, E_252) | ~m1_subset_1(E_252, k4_zfmisc_1(A_253, B_251, C_249, D_250)) | k1_xboole_0=D_250 | k1_xboole_0=C_249 | k1_xboole_0=B_251 | k1_xboole_0=A_253)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.57  tff(c_1184, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_1181])).
% 3.21/1.57  tff(c_1186, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_1184])).
% 3.21/1.57  tff(c_1188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_970, c_1186])).
% 3.21/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.57  
% 3.21/1.57  Inference rules
% 3.21/1.57  ----------------------
% 3.21/1.57  #Ref     : 0
% 3.21/1.57  #Sup     : 304
% 3.21/1.57  #Fact    : 0
% 3.21/1.57  #Define  : 0
% 3.21/1.57  #Split   : 3
% 3.21/1.57  #Chain   : 0
% 3.21/1.57  #Close   : 0
% 3.21/1.57  
% 3.21/1.57  Ordering : KBO
% 3.21/1.57  
% 3.21/1.57  Simplification rules
% 3.21/1.57  ----------------------
% 3.21/1.57  #Subsume      : 0
% 3.21/1.57  #Demod        : 137
% 3.21/1.57  #Tautology    : 208
% 3.21/1.57  #SimpNegUnit  : 11
% 3.21/1.57  #BackRed      : 0
% 3.21/1.57  
% 3.21/1.57  #Partial instantiations: 0
% 3.21/1.57  #Strategies tried      : 1
% 3.21/1.57  
% 3.21/1.57  Timing (in seconds)
% 3.21/1.57  ----------------------
% 3.21/1.57  Preprocessing        : 0.33
% 3.21/1.57  Parsing              : 0.18
% 3.21/1.57  CNF conversion       : 0.02
% 3.21/1.57  Main loop            : 0.42
% 3.21/1.57  Inferencing          : 0.18
% 3.21/1.57  Reduction            : 0.14
% 3.21/1.57  Demodulation         : 0.10
% 3.21/1.57  BG Simplification    : 0.03
% 3.21/1.57  Subsumption          : 0.04
% 3.21/1.57  Abstraction          : 0.03
% 3.21/1.57  MUC search           : 0.00
% 3.21/1.57  Cooper               : 0.00
% 3.21/1.57  Total                : 0.78
% 3.21/1.57  Index Insertion      : 0.00
% 3.21/1.57  Index Deletion       : 0.00
% 3.21/1.58  Index Matching       : 0.00
% 3.21/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
