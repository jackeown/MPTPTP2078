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
% DateTime   : Thu Dec  3 10:10:15 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 192 expanded)
%              Number of leaves         :   26 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  173 ( 807 expanded)
%              Number of equality atoms :  155 ( 729 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_107,negated_conjecture,(
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

tff(f_79,axiom,(
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

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
     => ( A = E
        & B = F
        & C = G
        & D = H ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_308,plain,(
    ! [A_138,B_136,E_137,C_134,D_135] :
      ( k11_mcart_1(A_138,B_136,C_134,D_135,E_137) = k2_mcart_1(E_137)
      | ~ m1_subset_1(E_137,k4_zfmisc_1(A_138,B_136,C_134,D_135))
      | k1_xboole_0 = D_135
      | k1_xboole_0 = C_134
      | k1_xboole_0 = B_136
      | k1_xboole_0 = A_138 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_311,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_308])).

tff(c_314,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_311])).

tff(c_20,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_106,plain,(
    ! [D_74,B_75,A_77,C_73,E_76] :
      ( k11_mcart_1(A_77,B_75,C_73,D_74,E_76) = k2_mcart_1(E_76)
      | ~ m1_subset_1(E_76,k4_zfmisc_1(A_77,B_75,C_73,D_74))
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_109,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_112,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_109])).

tff(c_156,plain,(
    ! [E_94,D_96,C_95,B_93,A_97] :
      ( k4_mcart_1(k8_mcart_1(A_97,B_93,C_95,D_96,E_94),k9_mcart_1(A_97,B_93,C_95,D_96,E_94),k10_mcart_1(A_97,B_93,C_95,D_96,E_94),k11_mcart_1(A_97,B_93,C_95,D_96,E_94)) = E_94
      | ~ m1_subset_1(E_94,k4_zfmisc_1(A_97,B_93,C_95,D_96))
      | k1_xboole_0 = D_96
      | k1_xboole_0 = C_95
      | k1_xboole_0 = B_93
      | k1_xboole_0 = A_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_201,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_156])).

tff(c_205,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_201])).

tff(c_206,plain,(
    k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_205])).

tff(c_22,plain,(
    k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_87,plain,(
    ! [H_64,F_57,E_59,C_62,A_63,B_61,G_58,D_60] :
      ( E_59 = A_63
      | k4_mcart_1(E_59,F_57,G_58,H_64) != k4_mcart_1(A_63,B_61,C_62,D_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_63,B_61,C_62,D_60] :
      ( A_63 = '#skF_6'
      | k4_mcart_1(A_63,B_61,C_62,D_60) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_87])).

tff(c_210,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_90])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_210])).

tff(c_250,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_307,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_315,plain,(
    k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_307])).

tff(c_251,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_359,plain,(
    ! [E_155,D_157,A_158,C_156,B_154] :
      ( k4_mcart_1(k8_mcart_1(A_158,B_154,C_156,D_157,E_155),k9_mcart_1(A_158,B_154,C_156,D_157,E_155),k10_mcart_1(A_158,B_154,C_156,D_157,E_155),k11_mcart_1(A_158,B_154,C_156,D_157,E_155)) = E_155
      | ~ m1_subset_1(E_155,k4_zfmisc_1(A_158,B_154,C_156,D_157))
      | k1_xboole_0 = D_157
      | k1_xboole_0 = C_156
      | k1_xboole_0 = B_154
      | k1_xboole_0 = A_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_407,plain,
    ( k4_mcart_1('#skF_6',k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_359])).

tff(c_414,plain,
    ( k4_mcart_1('#skF_6',k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_314,c_407])).

tff(c_415,plain,(
    k4_mcart_1('#skF_6',k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_414])).

tff(c_277,plain,(
    ! [H_117,C_115,A_116,B_114,F_110,D_113,G_111,E_112] :
      ( H_117 = D_113
      | k4_mcart_1(E_112,F_110,G_111,H_117) != k4_mcart_1(A_116,B_114,C_115,D_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_280,plain,(
    ! [D_113,A_116,B_114,C_115] :
      ( D_113 = '#skF_9'
      | k4_mcart_1(A_116,B_114,C_115,D_113) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_277])).

tff(c_422,plain,(
    k2_mcart_1('#skF_5') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_280])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_422])).

tff(c_461,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_467,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_462,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_518,plain,(
    ! [C_181,D_182,B_179,E_180,A_183] :
      ( k4_mcart_1(k8_mcart_1(A_183,B_179,C_181,D_182,E_180),k9_mcart_1(A_183,B_179,C_181,D_182,E_180),k10_mcart_1(A_183,B_179,C_181,D_182,E_180),k11_mcart_1(A_183,B_179,C_181,D_182,E_180)) = E_180
      | ~ m1_subset_1(E_180,k4_zfmisc_1(A_183,B_179,C_181,D_182))
      | k1_xboole_0 = D_182
      | k1_xboole_0 = C_181
      | k1_xboole_0 = B_179
      | k1_xboole_0 = A_183 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_563,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_9') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_518])).

tff(c_570,plain,
    ( k4_mcart_1('#skF_6',k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_9') = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_251,c_563])).

tff(c_571,plain,(
    k4_mcart_1('#skF_6',k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_9') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_570])).

tff(c_41,plain,(
    ! [C_30,A_31,H_32,F_25,B_29,G_26,D_28,E_27] :
      ( F_25 = B_29
      | k4_mcart_1(E_27,F_25,G_26,H_32) != k4_mcart_1(A_31,B_29,C_30,D_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [B_29,A_31,C_30,D_28] :
      ( B_29 = '#skF_7'
      | k4_mcart_1(A_31,B_29,C_30,D_28) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_41])).

tff(c_605,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_44])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_467,c_605])).

tff(c_623,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_624,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_675,plain,(
    ! [E_205,B_204,C_206,D_207,A_208] :
      ( k4_mcart_1(k8_mcart_1(A_208,B_204,C_206,D_207,E_205),k9_mcart_1(A_208,B_204,C_206,D_207,E_205),k10_mcart_1(A_208,B_204,C_206,D_207,E_205),k11_mcart_1(A_208,B_204,C_206,D_207,E_205)) = E_205
      | ~ m1_subset_1(E_205,k4_zfmisc_1(A_208,B_204,C_206,D_207))
      | k1_xboole_0 = D_207
      | k1_xboole_0 = C_206
      | k1_xboole_0 = B_204
      | k1_xboole_0 = A_208 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_726,plain,
    ( k4_mcart_1('#skF_6',k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_675])).

tff(c_736,plain,
    ( k4_mcart_1('#skF_6','#skF_7',k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_9') = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_624,c_462,c_726])).

tff(c_737,plain,(
    k4_mcart_1('#skF_6','#skF_7',k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_9') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_736])).

tff(c_260,plain,(
    ! [C_103,E_100,G_99,B_102,A_104,D_101,H_105,F_98] :
      ( G_99 = C_103
      | k4_mcart_1(E_100,F_98,G_99,H_105) != k4_mcart_1(A_104,B_102,C_103,D_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_263,plain,(
    ! [C_103,A_104,B_102,D_101] :
      ( C_103 = '#skF_8'
      | k4_mcart_1(A_104,B_102,C_103,D_101) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_260])).

tff(c_763,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_737,c_263])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_623,c_763])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:07:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.71  
% 3.49/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.71  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 3.49/1.71  
% 3.49/1.71  %Foreground sorts:
% 3.49/1.71  
% 3.49/1.71  
% 3.49/1.71  %Background operators:
% 3.49/1.71  
% 3.49/1.71  
% 3.49/1.71  %Foreground operators:
% 3.49/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.71  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.71  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.49/1.71  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.71  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.71  tff('#skF_9', type, '#skF_9': $i).
% 3.49/1.71  tff('#skF_8', type, '#skF_8': $i).
% 3.49/1.71  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.71  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.49/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.71  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.49/1.71  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.71  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.49/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.71  
% 3.49/1.73  tff(f_107, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 3.49/1.73  tff(f_79, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 3.49/1.73  tff(f_54, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (E = k4_mcart_1(k8_mcart_1(A, B, C, D, E), k9_mcart_1(A, B, C, D, E), k10_mcart_1(A, B, C, D, E), k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_mcart_1)).
% 3.49/1.73  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_mcart_1)).
% 3.49/1.73  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.73  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.73  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.73  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.73  tff(c_32, plain, (m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.73  tff(c_308, plain, (![A_138, B_136, E_137, C_134, D_135]: (k11_mcart_1(A_138, B_136, C_134, D_135, E_137)=k2_mcart_1(E_137) | ~m1_subset_1(E_137, k4_zfmisc_1(A_138, B_136, C_134, D_135)) | k1_xboole_0=D_135 | k1_xboole_0=C_134 | k1_xboole_0=B_136 | k1_xboole_0=A_138)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.73  tff(c_311, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_308])).
% 3.49/1.73  tff(c_314, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_311])).
% 3.49/1.73  tff(c_20, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.73  tff(c_54, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_20])).
% 3.49/1.73  tff(c_106, plain, (![D_74, B_75, A_77, C_73, E_76]: (k11_mcart_1(A_77, B_75, C_73, D_74, E_76)=k2_mcart_1(E_76) | ~m1_subset_1(E_76, k4_zfmisc_1(A_77, B_75, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_75 | k1_xboole_0=A_77)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.73  tff(c_109, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_106])).
% 3.49/1.73  tff(c_112, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_109])).
% 3.49/1.73  tff(c_156, plain, (![E_94, D_96, C_95, B_93, A_97]: (k4_mcart_1(k8_mcart_1(A_97, B_93, C_95, D_96, E_94), k9_mcart_1(A_97, B_93, C_95, D_96, E_94), k10_mcart_1(A_97, B_93, C_95, D_96, E_94), k11_mcart_1(A_97, B_93, C_95, D_96, E_94))=E_94 | ~m1_subset_1(E_94, k4_zfmisc_1(A_97, B_93, C_95, D_96)) | k1_xboole_0=D_96 | k1_xboole_0=C_95 | k1_xboole_0=B_93 | k1_xboole_0=A_97)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.73  tff(c_201, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_112, c_156])).
% 3.49/1.73  tff(c_205, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_201])).
% 3.49/1.73  tff(c_206, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_205])).
% 3.49/1.73  tff(c_22, plain, (k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.49/1.73  tff(c_87, plain, (![H_64, F_57, E_59, C_62, A_63, B_61, G_58, D_60]: (E_59=A_63 | k4_mcart_1(E_59, F_57, G_58, H_64)!=k4_mcart_1(A_63, B_61, C_62, D_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.73  tff(c_90, plain, (![A_63, B_61, C_62, D_60]: (A_63='#skF_6' | k4_mcart_1(A_63, B_61, C_62, D_60)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22, c_87])).
% 3.49/1.73  tff(c_210, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_206, c_90])).
% 3.49/1.73  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_210])).
% 3.49/1.73  tff(c_250, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitRight, [status(thm)], [c_20])).
% 3.49/1.73  tff(c_307, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_250])).
% 3.49/1.73  tff(c_315, plain, (k2_mcart_1('#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_307])).
% 3.49/1.73  tff(c_251, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_20])).
% 3.49/1.73  tff(c_359, plain, (![E_155, D_157, A_158, C_156, B_154]: (k4_mcart_1(k8_mcart_1(A_158, B_154, C_156, D_157, E_155), k9_mcart_1(A_158, B_154, C_156, D_157, E_155), k10_mcart_1(A_158, B_154, C_156, D_157, E_155), k11_mcart_1(A_158, B_154, C_156, D_157, E_155))=E_155 | ~m1_subset_1(E_155, k4_zfmisc_1(A_158, B_154, C_156, D_157)) | k1_xboole_0=D_157 | k1_xboole_0=C_156 | k1_xboole_0=B_154 | k1_xboole_0=A_158)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.73  tff(c_407, plain, (k4_mcart_1('#skF_6', k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_251, c_359])).
% 3.49/1.73  tff(c_414, plain, (k4_mcart_1('#skF_6', k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_314, c_407])).
% 3.49/1.73  tff(c_415, plain, (k4_mcart_1('#skF_6', k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_414])).
% 3.49/1.73  tff(c_277, plain, (![H_117, C_115, A_116, B_114, F_110, D_113, G_111, E_112]: (H_117=D_113 | k4_mcart_1(E_112, F_110, G_111, H_117)!=k4_mcart_1(A_116, B_114, C_115, D_113))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.73  tff(c_280, plain, (![D_113, A_116, B_114, C_115]: (D_113='#skF_9' | k4_mcart_1(A_116, B_114, C_115, D_113)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22, c_277])).
% 3.49/1.73  tff(c_422, plain, (k2_mcart_1('#skF_5')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_415, c_280])).
% 3.49/1.73  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_422])).
% 3.49/1.73  tff(c_461, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_250])).
% 3.49/1.73  tff(c_467, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_461])).
% 3.49/1.73  tff(c_462, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9'), inference(splitRight, [status(thm)], [c_250])).
% 3.49/1.73  tff(c_518, plain, (![C_181, D_182, B_179, E_180, A_183]: (k4_mcart_1(k8_mcart_1(A_183, B_179, C_181, D_182, E_180), k9_mcart_1(A_183, B_179, C_181, D_182, E_180), k10_mcart_1(A_183, B_179, C_181, D_182, E_180), k11_mcart_1(A_183, B_179, C_181, D_182, E_180))=E_180 | ~m1_subset_1(E_180, k4_zfmisc_1(A_183, B_179, C_181, D_182)) | k1_xboole_0=D_182 | k1_xboole_0=C_181 | k1_xboole_0=B_179 | k1_xboole_0=A_183)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.73  tff(c_563, plain, (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_9')='#skF_5' | ~m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_462, c_518])).
% 3.49/1.73  tff(c_570, plain, (k4_mcart_1('#skF_6', k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_9')='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_251, c_563])).
% 3.49/1.73  tff(c_571, plain, (k4_mcart_1('#skF_6', k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_9')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_570])).
% 3.49/1.73  tff(c_41, plain, (![C_30, A_31, H_32, F_25, B_29, G_26, D_28, E_27]: (F_25=B_29 | k4_mcart_1(E_27, F_25, G_26, H_32)!=k4_mcart_1(A_31, B_29, C_30, D_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.73  tff(c_44, plain, (![B_29, A_31, C_30, D_28]: (B_29='#skF_7' | k4_mcart_1(A_31, B_29, C_30, D_28)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22, c_41])).
% 3.49/1.73  tff(c_605, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_571, c_44])).
% 3.49/1.73  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_467, c_605])).
% 3.49/1.73  tff(c_623, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_461])).
% 3.49/1.73  tff(c_624, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_461])).
% 3.49/1.73  tff(c_675, plain, (![E_205, B_204, C_206, D_207, A_208]: (k4_mcart_1(k8_mcart_1(A_208, B_204, C_206, D_207, E_205), k9_mcart_1(A_208, B_204, C_206, D_207, E_205), k10_mcart_1(A_208, B_204, C_206, D_207, E_205), k11_mcart_1(A_208, B_204, C_206, D_207, E_205))=E_205 | ~m1_subset_1(E_205, k4_zfmisc_1(A_208, B_204, C_206, D_207)) | k1_xboole_0=D_207 | k1_xboole_0=C_206 | k1_xboole_0=B_204 | k1_xboole_0=A_208)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.73  tff(c_726, plain, (k4_mcart_1('#skF_6', k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_251, c_675])).
% 3.49/1.73  tff(c_736, plain, (k4_mcart_1('#skF_6', '#skF_7', k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_9')='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_624, c_462, c_726])).
% 3.49/1.73  tff(c_737, plain, (k4_mcart_1('#skF_6', '#skF_7', k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_9')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_736])).
% 3.49/1.73  tff(c_260, plain, (![C_103, E_100, G_99, B_102, A_104, D_101, H_105, F_98]: (G_99=C_103 | k4_mcart_1(E_100, F_98, G_99, H_105)!=k4_mcart_1(A_104, B_102, C_103, D_101))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.73  tff(c_263, plain, (![C_103, A_104, B_102, D_101]: (C_103='#skF_8' | k4_mcart_1(A_104, B_102, C_103, D_101)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22, c_260])).
% 3.49/1.73  tff(c_763, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_737, c_263])).
% 3.49/1.73  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_623, c_763])).
% 3.49/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.73  
% 3.49/1.73  Inference rules
% 3.49/1.73  ----------------------
% 3.49/1.73  #Ref     : 7
% 3.49/1.73  #Sup     : 197
% 3.49/1.73  #Fact    : 0
% 3.49/1.73  #Define  : 0
% 3.49/1.73  #Split   : 3
% 3.49/1.73  #Chain   : 0
% 3.49/1.73  #Close   : 0
% 3.49/1.73  
% 3.49/1.74  Ordering : KBO
% 3.49/1.74  
% 3.49/1.74  Simplification rules
% 3.49/1.74  ----------------------
% 3.49/1.74  #Subsume      : 15
% 3.49/1.74  #Demod        : 25
% 3.49/1.74  #Tautology    : 71
% 3.49/1.74  #SimpNegUnit  : 28
% 3.49/1.74  #BackRed      : 1
% 3.49/1.74  
% 3.49/1.74  #Partial instantiations: 0
% 3.49/1.74  #Strategies tried      : 1
% 3.49/1.74  
% 3.49/1.74  Timing (in seconds)
% 3.49/1.74  ----------------------
% 3.49/1.74  Preprocessing        : 0.42
% 3.49/1.74  Parsing              : 0.25
% 3.49/1.74  CNF conversion       : 0.03
% 3.49/1.74  Main loop            : 0.47
% 3.49/1.74  Inferencing          : 0.19
% 3.49/1.74  Reduction            : 0.10
% 3.49/1.74  Demodulation         : 0.06
% 3.49/1.74  BG Simplification    : 0.03
% 3.49/1.74  Subsumption          : 0.12
% 3.49/1.74  Abstraction          : 0.02
% 3.49/1.74  MUC search           : 0.00
% 3.49/1.74  Cooper               : 0.00
% 3.49/1.74  Total                : 0.93
% 3.49/1.74  Index Insertion      : 0.00
% 3.49/1.74  Index Deletion       : 0.00
% 3.49/1.74  Index Matching       : 0.00
% 3.49/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
