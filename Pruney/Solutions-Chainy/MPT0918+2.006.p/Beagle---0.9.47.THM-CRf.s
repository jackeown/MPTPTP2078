%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:15 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 146 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :    6
%              Number of atoms          :  123 ( 487 expanded)
%              Number of equality atoms :  112 ( 443 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff(f_86,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_54,axiom,(
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

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_74,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_14,plain,(
    ! [A_15,B_16] : k1_mcart_1(k4_tarski(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_75,plain,(
    ! [A_29,B_30,C_31,D_32] : k4_tarski(k4_tarski(k4_tarski(A_29,B_30),C_31),D_32) = k4_mcart_1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [A_37,B_38,C_39,D_40] : k4_tarski(k4_tarski(A_37,B_38),C_39) = k1_mcart_1(k4_mcart_1(A_37,B_38,C_39,D_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_14])).

tff(c_203,plain,(
    ! [A_55,B_56,C_57,D_58] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_55,B_56,C_57,D_58))) = k4_tarski(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_14])).

tff(c_215,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k4_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_203])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_538,plain,(
    ! [A_87,C_85,B_83,E_84,D_86] :
      ( k8_mcart_1(A_87,B_83,C_85,D_86,E_84) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_84)))
      | ~ m1_subset_1(E_84,k4_zfmisc_1(A_87,B_83,C_85,D_86))
      | k1_xboole_0 = D_86
      | k1_xboole_0 = C_85
      | k1_xboole_0 = B_83
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_540,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_538])).

tff(c_542,plain,
    ( k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_215,c_540])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_74,c_542])).

tff(c_545,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_677,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_551,plain,(
    ! [A_88,B_89,C_90,D_91] : k4_tarski(k4_tarski(k4_tarski(A_88,B_89),C_90),D_91) = k4_mcart_1(A_88,B_89,C_90,D_91) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_15,B_16] : k2_mcart_1(k4_tarski(A_15,B_16)) = B_16 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_578,plain,(
    ! [A_92,B_93,C_94,D_95] : k2_mcart_1(k4_mcart_1(A_92,B_93,C_94,D_95)) = D_95 ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_16])).

tff(c_587,plain,(
    k2_mcart_1('#skF_5') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_578])).

tff(c_879,plain,(
    ! [A_121,D_120,C_119,E_118,B_117] :
      ( k11_mcart_1(A_121,B_117,C_119,D_120,E_118) = k2_mcart_1(E_118)
      | ~ m1_subset_1(E_118,k4_zfmisc_1(A_121,B_117,C_119,D_120))
      | k1_xboole_0 = D_120
      | k1_xboole_0 = C_119
      | k1_xboole_0 = B_117
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_882,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_879])).

tff(c_884,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_882])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_677,c_884])).

tff(c_887,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_1094,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_887])).

tff(c_594,plain,(
    ! [A_96,B_97,C_98,D_99] : k4_tarski(k4_tarski(A_96,B_97),C_98) = k1_mcart_1(k4_mcart_1(A_96,B_97,C_98,D_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_14])).

tff(c_657,plain,(
    ! [A_104,B_105,C_106,D_107] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_104,B_105,C_106,D_107))) = k4_tarski(A_104,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_14])).

tff(c_669,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k4_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_657])).

tff(c_1939,plain,(
    ! [B_212,D_215,A_216,E_213,C_214] :
      ( k9_mcart_1(A_216,B_212,C_214,D_215,E_213) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_213)))
      | ~ m1_subset_1(E_213,k4_zfmisc_1(A_216,B_212,C_214,D_215))
      | k1_xboole_0 = D_215
      | k1_xboole_0 = C_214
      | k1_xboole_0 = B_212
      | k1_xboole_0 = A_216 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1945,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_1939])).

tff(c_1947,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_669,c_1945])).

tff(c_1949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_1094,c_1947])).

tff(c_1950,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_887])).

tff(c_637,plain,(
    ! [A_100,B_101,C_102,D_103] : k2_mcart_1(k1_mcart_1(k4_mcart_1(A_100,B_101,C_102,D_103))) = C_102 ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_16])).

tff(c_649,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_637])).

tff(c_2322,plain,(
    ! [B_252,A_256,E_253,D_255,C_254] :
      ( k2_mcart_1(k1_mcart_1(E_253)) = k10_mcart_1(A_256,B_252,C_254,D_255,E_253)
      | ~ m1_subset_1(E_253,k4_zfmisc_1(A_256,B_252,C_254,D_255))
      | k1_xboole_0 = D_255
      | k1_xboole_0 = C_254
      | k1_xboole_0 = B_252
      | k1_xboole_0 = A_256 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2328,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_2322])).

tff(c_2330,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_2328])).

tff(c_2332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_1950,c_2330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.69  
% 3.78/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.69  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 3.78/1.69  
% 3.78/1.69  %Foreground sorts:
% 3.78/1.69  
% 3.78/1.69  
% 3.78/1.69  %Background operators:
% 3.78/1.69  
% 3.78/1.69  
% 3.78/1.69  %Foreground operators:
% 3.78/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.78/1.69  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.78/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.69  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.78/1.69  tff('#skF_7', type, '#skF_7': $i).
% 3.78/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.78/1.69  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.78/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.78/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.78/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.78/1.69  tff('#skF_9', type, '#skF_9': $i).
% 3.78/1.69  tff('#skF_8', type, '#skF_8': $i).
% 3.78/1.69  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.78/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.69  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.78/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.78/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.69  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.78/1.69  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.78/1.69  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.78/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.69  
% 4.09/1.71  tff(f_86, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 4.09/1.71  tff(f_58, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 4.09/1.71  tff(f_27, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 4.09/1.71  tff(f_54, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 4.09/1.71  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.71  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.71  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.71  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.71  tff(c_18, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.71  tff(c_74, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_18])).
% 4.09/1.71  tff(c_14, plain, (![A_15, B_16]: (k1_mcart_1(k4_tarski(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.71  tff(c_20, plain, (k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.71  tff(c_75, plain, (![A_29, B_30, C_31, D_32]: (k4_tarski(k4_tarski(k4_tarski(A_29, B_30), C_31), D_32)=k4_mcart_1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.09/1.71  tff(c_118, plain, (![A_37, B_38, C_39, D_40]: (k4_tarski(k4_tarski(A_37, B_38), C_39)=k1_mcart_1(k4_mcart_1(A_37, B_38, C_39, D_40)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_14])).
% 4.09/1.71  tff(c_203, plain, (![A_55, B_56, C_57, D_58]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_55, B_56, C_57, D_58)))=k4_tarski(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_118, c_14])).
% 4.09/1.71  tff(c_215, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k4_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_20, c_203])).
% 4.09/1.71  tff(c_30, plain, (m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.09/1.71  tff(c_538, plain, (![A_87, C_85, B_83, E_84, D_86]: (k8_mcart_1(A_87, B_83, C_85, D_86, E_84)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_84))) | ~m1_subset_1(E_84, k4_zfmisc_1(A_87, B_83, C_85, D_86)) | k1_xboole_0=D_86 | k1_xboole_0=C_85 | k1_xboole_0=B_83 | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.09/1.71  tff(c_540, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_30, c_538])).
% 4.09/1.71  tff(c_542, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_215, c_540])).
% 4.09/1.71  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_74, c_542])).
% 4.09/1.71  tff(c_545, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitRight, [status(thm)], [c_18])).
% 4.09/1.71  tff(c_677, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_545])).
% 4.09/1.71  tff(c_551, plain, (![A_88, B_89, C_90, D_91]: (k4_tarski(k4_tarski(k4_tarski(A_88, B_89), C_90), D_91)=k4_mcart_1(A_88, B_89, C_90, D_91))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.09/1.71  tff(c_16, plain, (![A_15, B_16]: (k2_mcart_1(k4_tarski(A_15, B_16))=B_16)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.71  tff(c_578, plain, (![A_92, B_93, C_94, D_95]: (k2_mcart_1(k4_mcart_1(A_92, B_93, C_94, D_95))=D_95)), inference(superposition, [status(thm), theory('equality')], [c_551, c_16])).
% 4.09/1.71  tff(c_587, plain, (k2_mcart_1('#skF_5')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_20, c_578])).
% 4.09/1.71  tff(c_879, plain, (![A_121, D_120, C_119, E_118, B_117]: (k11_mcart_1(A_121, B_117, C_119, D_120, E_118)=k2_mcart_1(E_118) | ~m1_subset_1(E_118, k4_zfmisc_1(A_121, B_117, C_119, D_120)) | k1_xboole_0=D_120 | k1_xboole_0=C_119 | k1_xboole_0=B_117 | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.09/1.71  tff(c_882, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_30, c_879])).
% 4.09/1.71  tff(c_884, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_587, c_882])).
% 4.09/1.71  tff(c_886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_677, c_884])).
% 4.09/1.71  tff(c_887, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_545])).
% 4.09/1.71  tff(c_1094, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_887])).
% 4.09/1.71  tff(c_594, plain, (![A_96, B_97, C_98, D_99]: (k4_tarski(k4_tarski(A_96, B_97), C_98)=k1_mcart_1(k4_mcart_1(A_96, B_97, C_98, D_99)))), inference(superposition, [status(thm), theory('equality')], [c_551, c_14])).
% 4.09/1.71  tff(c_657, plain, (![A_104, B_105, C_106, D_107]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_104, B_105, C_106, D_107)))=k4_tarski(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_594, c_14])).
% 4.09/1.71  tff(c_669, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k4_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_20, c_657])).
% 4.09/1.71  tff(c_1939, plain, (![B_212, D_215, A_216, E_213, C_214]: (k9_mcart_1(A_216, B_212, C_214, D_215, E_213)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_213))) | ~m1_subset_1(E_213, k4_zfmisc_1(A_216, B_212, C_214, D_215)) | k1_xboole_0=D_215 | k1_xboole_0=C_214 | k1_xboole_0=B_212 | k1_xboole_0=A_216)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.09/1.71  tff(c_1945, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_30, c_1939])).
% 4.09/1.71  tff(c_1947, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_669, c_1945])).
% 4.09/1.71  tff(c_1949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_1094, c_1947])).
% 4.09/1.71  tff(c_1950, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_887])).
% 4.09/1.71  tff(c_637, plain, (![A_100, B_101, C_102, D_103]: (k2_mcart_1(k1_mcart_1(k4_mcart_1(A_100, B_101, C_102, D_103)))=C_102)), inference(superposition, [status(thm), theory('equality')], [c_594, c_16])).
% 4.09/1.71  tff(c_649, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_20, c_637])).
% 4.09/1.71  tff(c_2322, plain, (![B_252, A_256, E_253, D_255, C_254]: (k2_mcart_1(k1_mcart_1(E_253))=k10_mcart_1(A_256, B_252, C_254, D_255, E_253) | ~m1_subset_1(E_253, k4_zfmisc_1(A_256, B_252, C_254, D_255)) | k1_xboole_0=D_255 | k1_xboole_0=C_254 | k1_xboole_0=B_252 | k1_xboole_0=A_256)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.09/1.71  tff(c_2328, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_30, c_2322])).
% 4.09/1.71  tff(c_2330, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_649, c_2328])).
% 4.09/1.71  tff(c_2332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_1950, c_2330])).
% 4.09/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.71  
% 4.09/1.71  Inference rules
% 4.09/1.71  ----------------------
% 4.09/1.71  #Ref     : 0
% 4.09/1.71  #Sup     : 594
% 4.09/1.71  #Fact    : 0
% 4.09/1.71  #Define  : 0
% 4.09/1.71  #Split   : 3
% 4.09/1.71  #Chain   : 0
% 4.09/1.71  #Close   : 0
% 4.09/1.71  
% 4.09/1.71  Ordering : KBO
% 4.09/1.71  
% 4.09/1.71  Simplification rules
% 4.09/1.71  ----------------------
% 4.09/1.71  #Subsume      : 56
% 4.09/1.71  #Demod        : 488
% 4.09/1.71  #Tautology    : 421
% 4.09/1.71  #SimpNegUnit  : 11
% 4.09/1.71  #BackRed      : 2
% 4.09/1.71  
% 4.09/1.71  #Partial instantiations: 0
% 4.09/1.71  #Strategies tried      : 1
% 4.09/1.71  
% 4.09/1.71  Timing (in seconds)
% 4.09/1.71  ----------------------
% 4.09/1.71  Preprocessing        : 0.32
% 4.09/1.71  Parsing              : 0.17
% 4.09/1.71  CNF conversion       : 0.02
% 4.09/1.71  Main loop            : 0.62
% 4.09/1.71  Inferencing          : 0.25
% 4.09/1.71  Reduction            : 0.24
% 4.09/1.71  Demodulation         : 0.20
% 4.09/1.71  BG Simplification    : 0.03
% 4.09/1.71  Subsumption          : 0.06
% 4.09/1.71  Abstraction          : 0.05
% 4.09/1.71  MUC search           : 0.00
% 4.09/1.71  Cooper               : 0.00
% 4.09/1.71  Total                : 0.97
% 4.09/1.71  Index Insertion      : 0.00
% 4.09/1.71  Index Deletion       : 0.00
% 4.09/1.71  Index Matching       : 0.00
% 4.09/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
