%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:14 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 119 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :    5
%              Number of atoms          :  135 ( 517 expanded)
%              Number of equality atoms :  116 ( 461 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ? [F,G,H,I] :
                ( E = k4_mcart_1(F,G,H,I)
                & ~ ( k8_mcart_1(A,B,C,D,E) = F
                    & k9_mcart_1(A,B,C,D,E) = G
                    & k10_mcart_1(A,B,C,D,E) = H
                    & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_77,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_167,plain,(
    ! [H_75,A_76,B_78,D_80,C_79,G_73,I_74,F_77] :
      ( k8_mcart_1(A_76,B_78,C_79,D_80,k4_mcart_1(F_77,G_73,H_75,I_74)) = F_77
      | ~ m1_subset_1(k4_mcart_1(F_77,G_73,H_75,I_74),k4_zfmisc_1(A_76,B_78,C_79,D_80))
      | k1_xboole_0 = D_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_176,plain,(
    ! [A_76,B_78,C_79,D_80] :
      ( k8_mcart_1(A_76,B_78,C_79,D_80,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_6'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_76,B_78,C_79,D_80))
      | k1_xboole_0 = D_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_76 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_167])).

tff(c_180,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k8_mcart_1(A_81,B_82,C_83,D_84,'#skF_5') = '#skF_6'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_81,B_82,C_83,D_84))
      | k1_xboole_0 = D_84
      | k1_xboole_0 = C_83
      | k1_xboole_0 = B_82
      | k1_xboole_0 = A_81 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_176])).

tff(c_183,plain,
    ( k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_180])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_77,c_183])).

tff(c_188,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_195,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_328,plain,(
    ! [H_139,C_143,F_141,G_137,D_144,I_138,B_142,A_140] :
      ( k11_mcart_1(A_140,B_142,C_143,D_144,k4_mcart_1(F_141,G_137,H_139,I_138)) = I_138
      | ~ m1_subset_1(k4_mcart_1(F_141,G_137,H_139,I_138),k4_zfmisc_1(A_140,B_142,C_143,D_144))
      | k1_xboole_0 = D_144
      | k1_xboole_0 = C_143
      | k1_xboole_0 = B_142
      | k1_xboole_0 = A_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_337,plain,(
    ! [A_140,B_142,C_143,D_144] :
      ( k11_mcart_1(A_140,B_142,C_143,D_144,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_140,B_142,C_143,D_144))
      | k1_xboole_0 = D_144
      | k1_xboole_0 = C_143
      | k1_xboole_0 = B_142
      | k1_xboole_0 = A_140 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_328])).

tff(c_341,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k11_mcart_1(A_145,B_146,C_147,D_148,'#skF_5') = '#skF_9'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_145,B_146,C_147,D_148))
      | k1_xboole_0 = D_148
      | k1_xboole_0 = C_147
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_337])).

tff(c_344,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_341])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_195,c_344])).

tff(c_349,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_355,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_460,plain,(
    ! [B_194,D_196,C_195,G_189,I_190,A_192,H_191,F_193] :
      ( k9_mcart_1(A_192,B_194,C_195,D_196,k4_mcart_1(F_193,G_189,H_191,I_190)) = G_189
      | ~ m1_subset_1(k4_mcart_1(F_193,G_189,H_191,I_190),k4_zfmisc_1(A_192,B_194,C_195,D_196))
      | k1_xboole_0 = D_196
      | k1_xboole_0 = C_195
      | k1_xboole_0 = B_194
      | k1_xboole_0 = A_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_469,plain,(
    ! [A_192,B_194,C_195,D_196] :
      ( k9_mcart_1(A_192,B_194,C_195,D_196,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_7'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_192,B_194,C_195,D_196))
      | k1_xboole_0 = D_196
      | k1_xboole_0 = C_195
      | k1_xboole_0 = B_194
      | k1_xboole_0 = A_192 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_460])).

tff(c_473,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( k9_mcart_1(A_197,B_198,C_199,D_200,'#skF_5') = '#skF_7'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_197,B_198,C_199,D_200))
      | k1_xboole_0 = D_200
      | k1_xboole_0 = C_199
      | k1_xboole_0 = B_198
      | k1_xboole_0 = A_197 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_469])).

tff(c_476,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_473])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_355,c_476])).

tff(c_481,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_571,plain,(
    ! [B_234,A_232,I_230,H_231,C_235,G_229,D_236,F_233] :
      ( k10_mcart_1(A_232,B_234,C_235,D_236,k4_mcart_1(F_233,G_229,H_231,I_230)) = H_231
      | ~ m1_subset_1(k4_mcart_1(F_233,G_229,H_231,I_230),k4_zfmisc_1(A_232,B_234,C_235,D_236))
      | k1_xboole_0 = D_236
      | k1_xboole_0 = C_235
      | k1_xboole_0 = B_234
      | k1_xboole_0 = A_232 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_580,plain,(
    ! [A_232,B_234,C_235,D_236] :
      ( k10_mcart_1(A_232,B_234,C_235,D_236,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_8'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_232,B_234,C_235,D_236))
      | k1_xboole_0 = D_236
      | k1_xboole_0 = C_235
      | k1_xboole_0 = B_234
      | k1_xboole_0 = A_232 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_571])).

tff(c_597,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( k10_mcart_1(A_245,B_246,C_247,D_248,'#skF_5') = '#skF_8'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_245,B_246,C_247,D_248))
      | k1_xboole_0 = D_248
      | k1_xboole_0 = C_247
      | k1_xboole_0 = B_246
      | k1_xboole_0 = A_245 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_580])).

tff(c_600,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_597])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_481,c_600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.41  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.69/1.41  
% 2.69/1.41  %Foreground sorts:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Background operators:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Foreground operators:
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.41  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.41  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.69/1.41  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.69/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.41  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.69/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.69/1.41  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.41  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.69/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.41  
% 2.69/1.42  tff(f_85, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 2.69/1.42  tff(f_57, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_mcart_1)).
% 2.69/1.42  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.42  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.42  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.42  tff(c_18, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.42  tff(c_14, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.42  tff(c_77, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_14])).
% 2.69/1.42  tff(c_26, plain, (m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.42  tff(c_16, plain, (k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.42  tff(c_167, plain, (![H_75, A_76, B_78, D_80, C_79, G_73, I_74, F_77]: (k8_mcart_1(A_76, B_78, C_79, D_80, k4_mcart_1(F_77, G_73, H_75, I_74))=F_77 | ~m1_subset_1(k4_mcart_1(F_77, G_73, H_75, I_74), k4_zfmisc_1(A_76, B_78, C_79, D_80)) | k1_xboole_0=D_80 | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.42  tff(c_176, plain, (![A_76, B_78, C_79, D_80]: (k8_mcart_1(A_76, B_78, C_79, D_80, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_6' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_76, B_78, C_79, D_80)) | k1_xboole_0=D_80 | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_76)), inference(superposition, [status(thm), theory('equality')], [c_16, c_167])).
% 2.69/1.42  tff(c_180, plain, (![A_81, B_82, C_83, D_84]: (k8_mcart_1(A_81, B_82, C_83, D_84, '#skF_5')='#skF_6' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_81, B_82, C_83, D_84)) | k1_xboole_0=D_84 | k1_xboole_0=C_83 | k1_xboole_0=B_82 | k1_xboole_0=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_176])).
% 2.69/1.42  tff(c_183, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_180])).
% 2.69/1.42  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_77, c_183])).
% 2.69/1.42  tff(c_188, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitRight, [status(thm)], [c_14])).
% 2.69/1.42  tff(c_195, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_188])).
% 2.69/1.42  tff(c_328, plain, (![H_139, C_143, F_141, G_137, D_144, I_138, B_142, A_140]: (k11_mcart_1(A_140, B_142, C_143, D_144, k4_mcart_1(F_141, G_137, H_139, I_138))=I_138 | ~m1_subset_1(k4_mcart_1(F_141, G_137, H_139, I_138), k4_zfmisc_1(A_140, B_142, C_143, D_144)) | k1_xboole_0=D_144 | k1_xboole_0=C_143 | k1_xboole_0=B_142 | k1_xboole_0=A_140)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.42  tff(c_337, plain, (![A_140, B_142, C_143, D_144]: (k11_mcart_1(A_140, B_142, C_143, D_144, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_140, B_142, C_143, D_144)) | k1_xboole_0=D_144 | k1_xboole_0=C_143 | k1_xboole_0=B_142 | k1_xboole_0=A_140)), inference(superposition, [status(thm), theory('equality')], [c_16, c_328])).
% 2.69/1.42  tff(c_341, plain, (![A_145, B_146, C_147, D_148]: (k11_mcart_1(A_145, B_146, C_147, D_148, '#skF_5')='#skF_9' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_145, B_146, C_147, D_148)) | k1_xboole_0=D_148 | k1_xboole_0=C_147 | k1_xboole_0=B_146 | k1_xboole_0=A_145)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_337])).
% 2.69/1.42  tff(c_344, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_341])).
% 2.69/1.42  tff(c_348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_195, c_344])).
% 2.69/1.42  tff(c_349, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_188])).
% 2.69/1.42  tff(c_355, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_349])).
% 2.69/1.42  tff(c_460, plain, (![B_194, D_196, C_195, G_189, I_190, A_192, H_191, F_193]: (k9_mcart_1(A_192, B_194, C_195, D_196, k4_mcart_1(F_193, G_189, H_191, I_190))=G_189 | ~m1_subset_1(k4_mcart_1(F_193, G_189, H_191, I_190), k4_zfmisc_1(A_192, B_194, C_195, D_196)) | k1_xboole_0=D_196 | k1_xboole_0=C_195 | k1_xboole_0=B_194 | k1_xboole_0=A_192)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.42  tff(c_469, plain, (![A_192, B_194, C_195, D_196]: (k9_mcart_1(A_192, B_194, C_195, D_196, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_7' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_192, B_194, C_195, D_196)) | k1_xboole_0=D_196 | k1_xboole_0=C_195 | k1_xboole_0=B_194 | k1_xboole_0=A_192)), inference(superposition, [status(thm), theory('equality')], [c_16, c_460])).
% 2.69/1.42  tff(c_473, plain, (![A_197, B_198, C_199, D_200]: (k9_mcart_1(A_197, B_198, C_199, D_200, '#skF_5')='#skF_7' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_197, B_198, C_199, D_200)) | k1_xboole_0=D_200 | k1_xboole_0=C_199 | k1_xboole_0=B_198 | k1_xboole_0=A_197)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_469])).
% 2.69/1.42  tff(c_476, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_473])).
% 2.69/1.42  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_355, c_476])).
% 2.69/1.42  tff(c_481, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_349])).
% 2.69/1.42  tff(c_571, plain, (![B_234, A_232, I_230, H_231, C_235, G_229, D_236, F_233]: (k10_mcart_1(A_232, B_234, C_235, D_236, k4_mcart_1(F_233, G_229, H_231, I_230))=H_231 | ~m1_subset_1(k4_mcart_1(F_233, G_229, H_231, I_230), k4_zfmisc_1(A_232, B_234, C_235, D_236)) | k1_xboole_0=D_236 | k1_xboole_0=C_235 | k1_xboole_0=B_234 | k1_xboole_0=A_232)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.42  tff(c_580, plain, (![A_232, B_234, C_235, D_236]: (k10_mcart_1(A_232, B_234, C_235, D_236, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_8' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_232, B_234, C_235, D_236)) | k1_xboole_0=D_236 | k1_xboole_0=C_235 | k1_xboole_0=B_234 | k1_xboole_0=A_232)), inference(superposition, [status(thm), theory('equality')], [c_16, c_571])).
% 2.69/1.42  tff(c_597, plain, (![A_245, B_246, C_247, D_248]: (k10_mcart_1(A_245, B_246, C_247, D_248, '#skF_5')='#skF_8' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_245, B_246, C_247, D_248)) | k1_xboole_0=D_248 | k1_xboole_0=C_247 | k1_xboole_0=B_246 | k1_xboole_0=A_245)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_580])).
% 2.69/1.42  tff(c_600, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_597])).
% 2.69/1.42  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_481, c_600])).
% 2.69/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  Inference rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Ref     : 0
% 2.69/1.42  #Sup     : 129
% 2.69/1.42  #Fact    : 0
% 2.69/1.42  #Define  : 0
% 2.69/1.42  #Split   : 3
% 2.69/1.42  #Chain   : 0
% 2.69/1.42  #Close   : 0
% 2.69/1.42  
% 2.69/1.42  Ordering : KBO
% 2.69/1.42  
% 2.69/1.42  Simplification rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Subsume      : 0
% 2.69/1.42  #Demod        : 133
% 2.69/1.42  #Tautology    : 86
% 2.69/1.42  #SimpNegUnit  : 11
% 2.69/1.42  #BackRed      : 0
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 0
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.42  Preprocessing        : 0.32
% 2.69/1.42  Parsing              : 0.17
% 2.69/1.42  CNF conversion       : 0.03
% 2.69/1.42  Main loop            : 0.35
% 2.69/1.42  Inferencing          : 0.13
% 2.69/1.42  Reduction            : 0.13
% 2.69/1.42  Demodulation         : 0.09
% 2.69/1.42  BG Simplification    : 0.03
% 2.69/1.42  Subsumption          : 0.03
% 2.69/1.42  Abstraction          : 0.03
% 2.69/1.42  MUC search           : 0.00
% 2.69/1.42  Cooper               : 0.00
% 2.69/1.42  Total                : 0.70
% 2.69/1.42  Index Insertion      : 0.00
% 2.69/1.42  Index Deletion       : 0.00
% 2.69/1.42  Index Matching       : 0.00
% 2.69/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
