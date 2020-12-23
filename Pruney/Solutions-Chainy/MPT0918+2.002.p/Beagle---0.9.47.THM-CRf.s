%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:14 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 156 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :    6
%              Number of atoms          :  127 ( 496 expanded)
%              Number of equality atoms :  116 ( 452 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff(f_88,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_56,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_76,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_16,plain,(
    ! [A_18,B_19] : k1_mcart_1(k4_tarski(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_95,plain,(
    ! [A_37,B_38,C_39,D_40] : k4_tarski(k3_mcart_1(A_37,B_38,C_39),D_40) = k4_mcart_1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_150,plain,(
    ! [A_49,B_50,C_51,D_52] : k1_mcart_1(k4_mcart_1(A_49,B_50,C_51,D_52)) = k3_mcart_1(A_49,B_50,C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_16])).

tff(c_159,plain,(
    k3_mcart_1('#skF_6','#skF_7','#skF_8') = k1_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_150])).

tff(c_55,plain,(
    ! [A_28,B_29,C_30] : k4_tarski(k4_tarski(A_28,B_29),C_30) = k3_mcart_1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_28,B_29,C_30] : k1_mcart_1(k3_mcart_1(A_28,B_29,C_30)) = k4_tarski(A_28,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_16])).

tff(c_168,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k4_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_64])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_485,plain,(
    ! [C_110,A_108,D_109,E_107,B_106] :
      ( k8_mcart_1(A_108,B_106,C_110,D_109,E_107) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_107)))
      | ~ m1_subset_1(E_107,k4_zfmisc_1(A_108,B_106,C_110,D_109))
      | k1_xboole_0 = D_109
      | k1_xboole_0 = C_110
      | k1_xboole_0 = B_106
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_491,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_485])).

tff(c_493,plain,
    ( k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_168,c_491])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_76,c_493])).

tff(c_496,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_520,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_521,plain,(
    ! [A_117,B_118,C_119,D_120] : k4_tarski(k3_mcart_1(A_117,B_118,C_119),D_120) = k4_mcart_1(A_117,B_118,C_119,D_120) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_18,B_19] : k2_mcart_1(k4_tarski(A_18,B_19)) = B_19 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_539,plain,(
    ! [A_121,B_122,C_123,D_124] : k2_mcart_1(k4_mcart_1(A_121,B_122,C_123,D_124)) = D_124 ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_18])).

tff(c_548,plain,(
    k2_mcart_1('#skF_5') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_539])).

tff(c_712,plain,(
    ! [D_149,A_148,E_147,B_146,C_150] :
      ( k11_mcart_1(A_148,B_146,C_150,D_149,E_147) = k2_mcart_1(E_147)
      | ~ m1_subset_1(E_147,k4_zfmisc_1(A_148,B_146,C_150,D_149))
      | k1_xboole_0 = D_149
      | k1_xboole_0 = C_150
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_718,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_712])).

tff(c_720,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_718])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_520,c_720])).

tff(c_723,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_886,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_729,plain,(
    ! [A_151,B_152,C_153,D_154] : k4_tarski(k3_mcart_1(A_151,B_152,C_153),D_154) = k4_mcart_1(A_151,B_152,C_153,D_154) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_763,plain,(
    ! [A_159,B_160,C_161,D_162] : k1_mcart_1(k4_mcart_1(A_159,B_160,C_161,D_162)) = k3_mcart_1(A_159,B_160,C_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_16])).

tff(c_772,plain,(
    k3_mcart_1('#skF_6','#skF_7','#skF_8') = k1_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_763])).

tff(c_781,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k4_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_64])).

tff(c_1102,plain,(
    ! [E_216,B_215,A_217,D_218,C_219] :
      ( k9_mcart_1(A_217,B_215,C_219,D_218,E_216) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_216)))
      | ~ m1_subset_1(E_216,k4_zfmisc_1(A_217,B_215,C_219,D_218))
      | k1_xboole_0 = D_218
      | k1_xboole_0 = C_219
      | k1_xboole_0 = B_215
      | k1_xboole_0 = A_217 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1108,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_1102])).

tff(c_1110,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_781,c_1108])).

tff(c_1112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_886,c_1110])).

tff(c_1113,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_67,plain,(
    ! [A_28,B_29,C_30] : k2_mcart_1(k3_mcart_1(A_28,B_29,C_30)) = C_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_18])).

tff(c_784,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_67])).

tff(c_1287,plain,(
    ! [C_255,B_251,D_254,E_252,A_253] :
      ( k2_mcart_1(k1_mcart_1(E_252)) = k10_mcart_1(A_253,B_251,C_255,D_254,E_252)
      | ~ m1_subset_1(E_252,k4_zfmisc_1(A_253,B_251,C_255,D_254))
      | k1_xboole_0 = D_254
      | k1_xboole_0 = C_255
      | k1_xboole_0 = B_251
      | k1_xboole_0 = A_253 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1293,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_1287])).

tff(c_1295,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_1293])).

tff(c_1297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_1113,c_1295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 3.29/1.51  
% 3.29/1.51  %Foreground sorts:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Background operators:
% 3.29/1.51  
% 3.29/1.51  
% 3.29/1.51  %Foreground operators:
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.29/1.51  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.51  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.29/1.51  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.29/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.51  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.29/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.29/1.51  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.51  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.29/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.51  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.29/1.51  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.51  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.29/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.51  
% 3.29/1.53  tff(f_88, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 3.29/1.53  tff(f_60, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.29/1.53  tff(f_29, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.29/1.53  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.29/1.53  tff(f_56, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 3.29/1.53  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.53  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.53  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.53  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.53  tff(c_20, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.53  tff(c_76, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_20])).
% 3.29/1.53  tff(c_16, plain, (![A_18, B_19]: (k1_mcart_1(k4_tarski(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.53  tff(c_22, plain, (k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.53  tff(c_95, plain, (![A_37, B_38, C_39, D_40]: (k4_tarski(k3_mcart_1(A_37, B_38, C_39), D_40)=k4_mcart_1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.53  tff(c_150, plain, (![A_49, B_50, C_51, D_52]: (k1_mcart_1(k4_mcart_1(A_49, B_50, C_51, D_52))=k3_mcart_1(A_49, B_50, C_51))), inference(superposition, [status(thm), theory('equality')], [c_95, c_16])).
% 3.29/1.53  tff(c_159, plain, (k3_mcart_1('#skF_6', '#skF_7', '#skF_8')=k1_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22, c_150])).
% 3.29/1.53  tff(c_55, plain, (![A_28, B_29, C_30]: (k4_tarski(k4_tarski(A_28, B_29), C_30)=k3_mcart_1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.53  tff(c_64, plain, (![A_28, B_29, C_30]: (k1_mcart_1(k3_mcart_1(A_28, B_29, C_30))=k4_tarski(A_28, B_29))), inference(superposition, [status(thm), theory('equality')], [c_55, c_16])).
% 3.29/1.53  tff(c_168, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k4_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_159, c_64])).
% 3.29/1.53  tff(c_32, plain, (m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.53  tff(c_485, plain, (![C_110, A_108, D_109, E_107, B_106]: (k8_mcart_1(A_108, B_106, C_110, D_109, E_107)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_107))) | ~m1_subset_1(E_107, k4_zfmisc_1(A_108, B_106, C_110, D_109)) | k1_xboole_0=D_109 | k1_xboole_0=C_110 | k1_xboole_0=B_106 | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.53  tff(c_491, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_485])).
% 3.29/1.53  tff(c_493, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_168, c_491])).
% 3.29/1.53  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_76, c_493])).
% 3.29/1.53  tff(c_496, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitRight, [status(thm)], [c_20])).
% 3.29/1.53  tff(c_520, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_496])).
% 3.29/1.53  tff(c_521, plain, (![A_117, B_118, C_119, D_120]: (k4_tarski(k3_mcart_1(A_117, B_118, C_119), D_120)=k4_mcart_1(A_117, B_118, C_119, D_120))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.53  tff(c_18, plain, (![A_18, B_19]: (k2_mcart_1(k4_tarski(A_18, B_19))=B_19)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.53  tff(c_539, plain, (![A_121, B_122, C_123, D_124]: (k2_mcart_1(k4_mcart_1(A_121, B_122, C_123, D_124))=D_124)), inference(superposition, [status(thm), theory('equality')], [c_521, c_18])).
% 3.29/1.53  tff(c_548, plain, (k2_mcart_1('#skF_5')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_22, c_539])).
% 3.29/1.53  tff(c_712, plain, (![D_149, A_148, E_147, B_146, C_150]: (k11_mcart_1(A_148, B_146, C_150, D_149, E_147)=k2_mcart_1(E_147) | ~m1_subset_1(E_147, k4_zfmisc_1(A_148, B_146, C_150, D_149)) | k1_xboole_0=D_149 | k1_xboole_0=C_150 | k1_xboole_0=B_146 | k1_xboole_0=A_148)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.53  tff(c_718, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_712])).
% 3.29/1.53  tff(c_720, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_548, c_718])).
% 3.29/1.53  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_520, c_720])).
% 3.29/1.53  tff(c_723, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_496])).
% 3.29/1.53  tff(c_886, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_723])).
% 3.29/1.53  tff(c_729, plain, (![A_151, B_152, C_153, D_154]: (k4_tarski(k3_mcart_1(A_151, B_152, C_153), D_154)=k4_mcart_1(A_151, B_152, C_153, D_154))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.53  tff(c_763, plain, (![A_159, B_160, C_161, D_162]: (k1_mcart_1(k4_mcart_1(A_159, B_160, C_161, D_162))=k3_mcart_1(A_159, B_160, C_161))), inference(superposition, [status(thm), theory('equality')], [c_729, c_16])).
% 3.29/1.53  tff(c_772, plain, (k3_mcart_1('#skF_6', '#skF_7', '#skF_8')=k1_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22, c_763])).
% 3.29/1.53  tff(c_781, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k4_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_772, c_64])).
% 3.29/1.53  tff(c_1102, plain, (![E_216, B_215, A_217, D_218, C_219]: (k9_mcart_1(A_217, B_215, C_219, D_218, E_216)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_216))) | ~m1_subset_1(E_216, k4_zfmisc_1(A_217, B_215, C_219, D_218)) | k1_xboole_0=D_218 | k1_xboole_0=C_219 | k1_xboole_0=B_215 | k1_xboole_0=A_217)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.53  tff(c_1108, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_1102])).
% 3.29/1.53  tff(c_1110, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_781, c_1108])).
% 3.29/1.53  tff(c_1112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_886, c_1110])).
% 3.29/1.53  tff(c_1113, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_723])).
% 3.29/1.53  tff(c_67, plain, (![A_28, B_29, C_30]: (k2_mcart_1(k3_mcart_1(A_28, B_29, C_30))=C_30)), inference(superposition, [status(thm), theory('equality')], [c_55, c_18])).
% 3.29/1.53  tff(c_784, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_772, c_67])).
% 3.29/1.53  tff(c_1287, plain, (![C_255, B_251, D_254, E_252, A_253]: (k2_mcart_1(k1_mcart_1(E_252))=k10_mcart_1(A_253, B_251, C_255, D_254, E_252) | ~m1_subset_1(E_252, k4_zfmisc_1(A_253, B_251, C_255, D_254)) | k1_xboole_0=D_254 | k1_xboole_0=C_255 | k1_xboole_0=B_251 | k1_xboole_0=A_253)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.53  tff(c_1293, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_1287])).
% 3.29/1.53  tff(c_1295, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_784, c_1293])).
% 3.29/1.53  tff(c_1297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_1113, c_1295])).
% 3.29/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  Inference rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Ref     : 0
% 3.29/1.53  #Sup     : 330
% 3.29/1.53  #Fact    : 0
% 3.29/1.53  #Define  : 0
% 3.29/1.53  #Split   : 3
% 3.29/1.53  #Chain   : 0
% 3.29/1.53  #Close   : 0
% 3.29/1.53  
% 3.29/1.53  Ordering : KBO
% 3.29/1.53  
% 3.29/1.53  Simplification rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Subsume      : 0
% 3.29/1.53  #Demod        : 201
% 3.29/1.53  #Tautology    : 245
% 3.29/1.53  #SimpNegUnit  : 10
% 3.29/1.53  #BackRed      : 0
% 3.29/1.53  
% 3.29/1.53  #Partial instantiations: 0
% 3.29/1.53  #Strategies tried      : 1
% 3.29/1.53  
% 3.29/1.53  Timing (in seconds)
% 3.29/1.53  ----------------------
% 3.29/1.53  Preprocessing        : 0.31
% 3.29/1.53  Parsing              : 0.16
% 3.29/1.53  CNF conversion       : 0.02
% 3.29/1.53  Main loop            : 0.45
% 3.29/1.53  Inferencing          : 0.20
% 3.29/1.53  Reduction            : 0.15
% 3.29/1.53  Demodulation         : 0.11
% 3.29/1.53  BG Simplification    : 0.03
% 3.29/1.53  Subsumption          : 0.05
% 3.29/1.53  Abstraction          : 0.03
% 3.29/1.53  MUC search           : 0.00
% 3.29/1.53  Cooper               : 0.00
% 3.29/1.53  Total                : 0.80
% 3.29/1.53  Index Insertion      : 0.00
% 3.29/1.53  Index Deletion       : 0.00
% 3.29/1.53  Index Matching       : 0.00
% 3.29/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
