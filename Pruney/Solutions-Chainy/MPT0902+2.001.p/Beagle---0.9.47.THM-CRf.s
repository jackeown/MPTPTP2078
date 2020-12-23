%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:52 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 255 expanded)
%              Number of leaves         :   42 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  251 ( 807 expanded)
%              Number of equality atoms :  215 ( 695 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_196,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ~ ! [E] :
                ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
               => ( E != k8_mcart_1(A,B,C,D,E)
                  & E != k9_mcart_1(A,B,C,D,E)
                  & E != k10_mcart_1(A,B,C,D,E)
                  & E != k11_mcart_1(A,B,C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_mcart_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_87,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_105,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_166,axiom,(
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

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => ( C != k1_mcart_1(C)
                & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19] : k4_tarski(k4_tarski(A_17,B_18),C_19) = k3_mcart_1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_38,B_39,C_40,D_41] : k4_tarski(k4_tarski(k4_tarski(A_38,B_39),C_40),D_41) = k4_mcart_1(A_38,B_39,C_40,D_41) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    ! [A_38,B_39,C_40,D_41] : k4_tarski(k3_mcart_1(A_38,B_39,C_40),D_41) = k4_mcart_1(A_38,B_39,C_40,D_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42])).

tff(c_1170,plain,(
    ! [A_319,B_320,C_321] : k4_tarski(k4_tarski(A_319,B_320),C_321) = k3_mcart_1(A_319,B_320,C_321) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1173,plain,(
    ! [A_319,B_320,C_321,C_19] : k3_mcart_1(k4_tarski(A_319,B_320),C_321,C_19) = k4_tarski(k3_mcart_1(A_319,B_320,C_321),C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_30])).

tff(c_3169,plain,(
    ! [A_767,B_768,C_769,C_770] : k3_mcart_1(k4_tarski(A_767,B_768),C_769,C_770) = k4_mcart_1(A_767,B_768,C_769,C_770) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1173])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_86,B_87] : k2_xboole_0(k1_tarski(A_86),B_87) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_121,plain,(
    ! [A_86] : k1_tarski(A_86) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_36,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_3'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1080,plain,(
    ! [C_310,A_311] :
      ( C_310 = A_311
      | ~ r2_hidden(C_310,k1_tarski(A_311)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1084,plain,(
    ! [A_311] :
      ( '#skF_3'(k1_tarski(A_311)) = A_311
      | k1_tarski(A_311) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_1080])).

tff(c_1094,plain,(
    ! [A_311] : '#skF_3'(k1_tarski(A_311)) = A_311 ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_1084])).

tff(c_8,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1191,plain,(
    ! [D_324,A_325,C_326,E_327] :
      ( ~ r2_hidden(D_324,A_325)
      | k3_mcart_1(C_326,D_324,E_327) != '#skF_3'(A_325)
      | k1_xboole_0 = A_325 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1197,plain,(
    ! [C_326,C_8,E_327] :
      ( k3_mcart_1(C_326,C_8,E_327) != '#skF_3'(k1_tarski(C_8))
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1191])).

tff(c_1201,plain,(
    ! [C_326,C_8,E_327] :
      ( k3_mcart_1(C_326,C_8,E_327) != C_8
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1197])).

tff(c_1202,plain,(
    ! [C_326,C_8,E_327] : k3_mcart_1(C_326,C_8,E_327) != C_8 ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_1201])).

tff(c_3185,plain,(
    ! [A_767,B_768,C_769,C_770] : k4_mcart_1(A_767,B_768,C_769,C_770) != C_769 ),
    inference(superposition,[status(thm),theory(equality)],[c_3169,c_1202])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_44,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_4'(A_42),A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1088,plain,(
    ! [A_311] :
      ( '#skF_4'(k1_tarski(A_311)) = A_311
      | k1_tarski(A_311) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_1080])).

tff(c_1097,plain,(
    ! [A_311] : '#skF_4'(k1_tarski(A_311)) = A_311 ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_1088])).

tff(c_2308,plain,(
    ! [F_582,D_583,C_580,A_581,E_579] :
      ( ~ r2_hidden(D_583,A_581)
      | k4_mcart_1(C_580,D_583,E_579,F_582) != '#skF_4'(A_581)
      | k1_xboole_0 = A_581 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2316,plain,(
    ! [C_580,C_8,E_579,F_582] :
      ( k4_mcart_1(C_580,C_8,E_579,F_582) != '#skF_4'(k1_tarski(C_8))
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_2308])).

tff(c_2321,plain,(
    ! [C_580,C_8,E_579,F_582] :
      ( k4_mcart_1(C_580,C_8,E_579,F_582) != C_8
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_2316])).

tff(c_2322,plain,(
    ! [C_580,C_8,E_579,F_582] : k4_mcart_1(C_580,C_8,E_579,F_582) != C_8 ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_2321])).

tff(c_191,plain,(
    ! [C_103,A_104] :
      ( C_103 = A_104
      | ~ r2_hidden(C_103,k1_tarski(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_199,plain,(
    ! [A_104] :
      ( '#skF_4'(k1_tarski(A_104)) = A_104
      | k1_tarski(A_104) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_191])).

tff(c_208,plain,(
    ! [A_104] : '#skF_4'(k1_tarski(A_104)) = A_104 ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_199])).

tff(c_425,plain,(
    ! [A_167,E_165,D_169,C_166,F_168] :
      ( ~ r2_hidden(C_166,A_167)
      | k4_mcart_1(C_166,D_169,E_165,F_168) != '#skF_4'(A_167)
      | k1_xboole_0 = A_167 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_433,plain,(
    ! [C_8,D_169,E_165,F_168] :
      ( k4_mcart_1(C_8,D_169,E_165,F_168) != '#skF_4'(k1_tarski(C_8))
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_425])).

tff(c_438,plain,(
    ! [C_8,D_169,E_165,F_168] :
      ( k4_mcart_1(C_8,D_169,E_165,F_168) != C_8
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_433])).

tff(c_439,plain,(
    ! [C_8,D_169,E_165,F_168] : k4_mcart_1(C_8,D_169,E_165,F_168) != C_8 ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_438])).

tff(c_72,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_183,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_763,plain,(
    ! [D_231,B_234,A_233,E_230,C_232] :
      ( k11_mcart_1(A_233,B_234,C_232,D_231,E_230) = k2_mcart_1(E_230)
      | ~ m1_subset_1(E_230,k4_zfmisc_1(A_233,B_234,C_232,D_231))
      | k1_xboole_0 = D_231
      | k1_xboole_0 = C_232
      | k1_xboole_0 = B_234
      | k1_xboole_0 = A_233 ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_781,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_74,c_763])).

tff(c_788,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_76,c_781])).

tff(c_1022,plain,(
    ! [A_308,C_305,B_306,D_304,E_307] :
      ( k4_mcart_1(k8_mcart_1(A_308,B_306,C_305,D_304,E_307),k9_mcart_1(A_308,B_306,C_305,D_304,E_307),k10_mcart_1(A_308,B_306,C_305,D_304,E_307),k11_mcart_1(A_308,B_306,C_305,D_304,E_307)) = E_307
      | ~ m1_subset_1(E_307,k4_zfmisc_1(A_308,B_306,C_305,D_304))
      | k1_xboole_0 = D_304
      | k1_xboole_0 = C_305
      | k1_xboole_0 = B_306
      | k1_xboole_0 = A_308 ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1061,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_1022])).

tff(c_1068,plain,
    ( k4_mcart_1('#skF_9',k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_183,c_1061])).

tff(c_1070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_76,c_439,c_1068])).

tff(c_1071,plain,
    ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1210,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1071])).

tff(c_1624,plain,(
    ! [C_446,D_445,A_447,E_444,B_448] :
      ( k11_mcart_1(A_447,B_448,C_446,D_445,E_444) = k2_mcart_1(E_444)
      | ~ m1_subset_1(E_444,k4_zfmisc_1(A_447,B_448,C_446,D_445))
      | k1_xboole_0 = D_445
      | k1_xboole_0 = C_446
      | k1_xboole_0 = B_448
      | k1_xboole_0 = A_447 ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1639,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_74,c_1624])).

tff(c_1645,plain,
    ( k2_mcart_1('#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_1639])).

tff(c_1646,plain,(
    k2_mcart_1('#skF_9') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_76,c_1645])).

tff(c_1311,plain,(
    ! [A_371,B_372,C_373,D_374] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_371,B_372),C_373),D_374) = k4_zfmisc_1(A_371,B_372,C_373,D_374) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    ! [C_23,A_20,B_21] :
      ( k2_mcart_1(C_23) != C_23
      | ~ m1_subset_1(C_23,k2_zfmisc_1(A_20,B_21))
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2098,plain,(
    ! [C_536,D_540,A_538,C_537,B_539] :
      ( k2_mcart_1(C_536) != C_536
      | ~ m1_subset_1(C_536,k4_zfmisc_1(A_538,B_539,C_537,D_540))
      | k1_xboole_0 = D_540
      | k2_zfmisc_1(k2_zfmisc_1(A_538,B_539),C_537) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_32])).

tff(c_2116,plain,
    ( k2_mcart_1('#skF_9') != '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_2098])).

tff(c_2124,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1646,c_2116])).

tff(c_2125,plain,(
    k2_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2124])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( k1_xboole_0 = B_12
      | k1_xboole_0 = A_11
      | k2_zfmisc_1(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2150,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2125,c_20])).

tff(c_2164,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2150])).

tff(c_2186,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2164,c_20])).

tff(c_2200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_2186])).

tff(c_2201,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1071])).

tff(c_2229,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2201])).

tff(c_2665,plain,(
    ! [D_644,C_645,B_647,A_646,E_643] :
      ( k11_mcart_1(A_646,B_647,C_645,D_644,E_643) = k2_mcart_1(E_643)
      | ~ m1_subset_1(E_643,k4_zfmisc_1(A_646,B_647,C_645,D_644))
      | k1_xboole_0 = D_644
      | k1_xboole_0 = C_645
      | k1_xboole_0 = B_647
      | k1_xboole_0 = A_646 ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2683,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_74,c_2665])).

tff(c_2690,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_76,c_2683])).

tff(c_2896,plain,(
    ! [A_716,C_713,D_712,E_715,B_714] :
      ( k4_mcart_1(k8_mcart_1(A_716,B_714,C_713,D_712,E_715),k9_mcart_1(A_716,B_714,C_713,D_712,E_715),k10_mcart_1(A_716,B_714,C_713,D_712,E_715),k11_mcart_1(A_716,B_714,C_713,D_712,E_715)) = E_715
      | ~ m1_subset_1(E_715,k4_zfmisc_1(A_716,B_714,C_713,D_712))
      | k1_xboole_0 = D_712
      | k1_xboole_0 = C_713
      | k1_xboole_0 = B_714
      | k1_xboole_0 = A_716 ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2935,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2690,c_2896])).

tff(c_2942,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2229,c_2935])).

tff(c_2944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_76,c_2322,c_2942])).

tff(c_2945,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2201])).

tff(c_3304,plain,(
    ! [E_802,A_805,D_803,B_806,C_804] :
      ( k11_mcart_1(A_805,B_806,C_804,D_803,E_802) = k2_mcart_1(E_802)
      | ~ m1_subset_1(E_802,k4_zfmisc_1(A_805,B_806,C_804,D_803))
      | k1_xboole_0 = D_803
      | k1_xboole_0 = C_804
      | k1_xboole_0 = B_806
      | k1_xboole_0 = A_805 ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3319,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_74,c_3304])).

tff(c_3326,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_76,c_3319])).

tff(c_3608,plain,(
    ! [D_869,C_870,A_873,B_871,E_872] :
      ( k4_mcart_1(k8_mcart_1(A_873,B_871,C_870,D_869,E_872),k9_mcart_1(A_873,B_871,C_870,D_869,E_872),k10_mcart_1(A_873,B_871,C_870,D_869,E_872),k11_mcart_1(A_873,B_871,C_870,D_869,E_872)) = E_872
      | ~ m1_subset_1(E_872,k4_zfmisc_1(A_873,B_871,C_870,D_869))
      | k1_xboole_0 = D_869
      | k1_xboole_0 = C_870
      | k1_xboole_0 = B_871
      | k1_xboole_0 = A_873 ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3644,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3326,c_3608])).

tff(c_3651,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2945,c_3644])).

tff(c_3653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_76,c_3185,c_3651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:41:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.93  
% 5.00/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.93  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 5.00/1.93  
% 5.00/1.93  %Foreground sorts:
% 5.00/1.93  
% 5.00/1.93  
% 5.00/1.93  %Background operators:
% 5.00/1.93  
% 5.00/1.93  
% 5.00/1.93  %Foreground operators:
% 5.00/1.93  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.00/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.00/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.00/1.93  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.00/1.93  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.00/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.00/1.93  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.00/1.93  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 5.00/1.93  tff('#skF_7', type, '#skF_7': $i).
% 5.00/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.00/1.93  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.00/1.93  tff('#skF_6', type, '#skF_6': $i).
% 5.00/1.93  tff('#skF_9', type, '#skF_9': $i).
% 5.00/1.93  tff('#skF_8', type, '#skF_8': $i).
% 5.00/1.93  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.00/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.93  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.00/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.00/1.93  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.00/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.00/1.93  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.00/1.93  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.00/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.00/1.93  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.00/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.00/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.00/1.93  
% 5.00/1.95  tff(f_196, negated_conjecture, ~(![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (((~(E = k8_mcart_1(A, B, C, D, E)) & ~(E = k9_mcart_1(A, B, C, D, E))) & ~(E = k10_mcart_1(A, B, C, D, E))) & ~(E = k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_mcart_1)).
% 5.00/1.95  tff(f_54, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 5.00/1.95  tff(f_89, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 5.00/1.95  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.00/1.95  tff(f_52, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.00/1.95  tff(f_87, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.00/1.95  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.00/1.95  tff(f_105, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 5.00/1.95  tff(f_166, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 5.00/1.95  tff(f_141, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (E = k4_mcart_1(k8_mcart_1(A, B, C, D, E), k9_mcart_1(A, B, C, D, E), k10_mcart_1(A, B, C, D, E), k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_mcart_1)).
% 5.00/1.95  tff(f_107, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 5.00/1.95  tff(f_71, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 5.00/1.95  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.00/1.95  tff(c_82, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.00/1.95  tff(c_80, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.00/1.95  tff(c_78, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.00/1.95  tff(c_76, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.00/1.95  tff(c_30, plain, (![A_17, B_18, C_19]: (k4_tarski(k4_tarski(A_17, B_18), C_19)=k3_mcart_1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.00/1.95  tff(c_42, plain, (![A_38, B_39, C_40, D_41]: (k4_tarski(k4_tarski(k4_tarski(A_38, B_39), C_40), D_41)=k4_mcart_1(A_38, B_39, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.00/1.95  tff(c_83, plain, (![A_38, B_39, C_40, D_41]: (k4_tarski(k3_mcart_1(A_38, B_39, C_40), D_41)=k4_mcart_1(A_38, B_39, C_40, D_41))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42])).
% 5.00/1.95  tff(c_1170, plain, (![A_319, B_320, C_321]: (k4_tarski(k4_tarski(A_319, B_320), C_321)=k3_mcart_1(A_319, B_320, C_321))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.00/1.95  tff(c_1173, plain, (![A_319, B_320, C_321, C_19]: (k3_mcart_1(k4_tarski(A_319, B_320), C_321, C_19)=k4_tarski(k3_mcart_1(A_319, B_320, C_321), C_19))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_30])).
% 5.00/1.95  tff(c_3169, plain, (![A_767, B_768, C_769, C_770]: (k3_mcart_1(k4_tarski(A_767, B_768), C_769, C_770)=k4_mcart_1(A_767, B_768, C_769, C_770))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1173])).
% 5.00/1.95  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.00/1.95  tff(c_117, plain, (![A_86, B_87]: (k2_xboole_0(k1_tarski(A_86), B_87)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.00/1.95  tff(c_121, plain, (![A_86]: (k1_tarski(A_86)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 5.00/1.95  tff(c_36, plain, (![A_24]: (r2_hidden('#skF_3'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.00/1.95  tff(c_1080, plain, (![C_310, A_311]: (C_310=A_311 | ~r2_hidden(C_310, k1_tarski(A_311)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.00/1.95  tff(c_1084, plain, (![A_311]: ('#skF_3'(k1_tarski(A_311))=A_311 | k1_tarski(A_311)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_1080])).
% 5.00/1.95  tff(c_1094, plain, (![A_311]: ('#skF_3'(k1_tarski(A_311))=A_311)), inference(negUnitSimplification, [status(thm)], [c_121, c_1084])).
% 5.00/1.95  tff(c_8, plain, (![C_8]: (r2_hidden(C_8, k1_tarski(C_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.00/1.95  tff(c_1191, plain, (![D_324, A_325, C_326, E_327]: (~r2_hidden(D_324, A_325) | k3_mcart_1(C_326, D_324, E_327)!='#skF_3'(A_325) | k1_xboole_0=A_325)), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.00/1.95  tff(c_1197, plain, (![C_326, C_8, E_327]: (k3_mcart_1(C_326, C_8, E_327)!='#skF_3'(k1_tarski(C_8)) | k1_tarski(C_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1191])).
% 5.00/1.95  tff(c_1201, plain, (![C_326, C_8, E_327]: (k3_mcart_1(C_326, C_8, E_327)!=C_8 | k1_tarski(C_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1197])).
% 5.00/1.95  tff(c_1202, plain, (![C_326, C_8, E_327]: (k3_mcart_1(C_326, C_8, E_327)!=C_8)), inference(negUnitSimplification, [status(thm)], [c_121, c_1201])).
% 5.00/1.95  tff(c_3185, plain, (![A_767, B_768, C_769, C_770]: (k4_mcart_1(A_767, B_768, C_769, C_770)!=C_769)), inference(superposition, [status(thm), theory('equality')], [c_3169, c_1202])).
% 5.00/1.95  tff(c_74, plain, (m1_subset_1('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.00/1.95  tff(c_44, plain, (![A_42]: (r2_hidden('#skF_4'(A_42), A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.00/1.95  tff(c_1088, plain, (![A_311]: ('#skF_4'(k1_tarski(A_311))=A_311 | k1_tarski(A_311)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_1080])).
% 5.00/1.95  tff(c_1097, plain, (![A_311]: ('#skF_4'(k1_tarski(A_311))=A_311)), inference(negUnitSimplification, [status(thm)], [c_121, c_1088])).
% 5.00/1.95  tff(c_2308, plain, (![F_582, D_583, C_580, A_581, E_579]: (~r2_hidden(D_583, A_581) | k4_mcart_1(C_580, D_583, E_579, F_582)!='#skF_4'(A_581) | k1_xboole_0=A_581)), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.00/1.95  tff(c_2316, plain, (![C_580, C_8, E_579, F_582]: (k4_mcart_1(C_580, C_8, E_579, F_582)!='#skF_4'(k1_tarski(C_8)) | k1_tarski(C_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2308])).
% 5.00/1.95  tff(c_2321, plain, (![C_580, C_8, E_579, F_582]: (k4_mcart_1(C_580, C_8, E_579, F_582)!=C_8 | k1_tarski(C_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1097, c_2316])).
% 5.00/1.95  tff(c_2322, plain, (![C_580, C_8, E_579, F_582]: (k4_mcart_1(C_580, C_8, E_579, F_582)!=C_8)), inference(negUnitSimplification, [status(thm)], [c_121, c_2321])).
% 5.00/1.95  tff(c_191, plain, (![C_103, A_104]: (C_103=A_104 | ~r2_hidden(C_103, k1_tarski(A_104)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.00/1.95  tff(c_199, plain, (![A_104]: ('#skF_4'(k1_tarski(A_104))=A_104 | k1_tarski(A_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_191])).
% 5.00/1.95  tff(c_208, plain, (![A_104]: ('#skF_4'(k1_tarski(A_104))=A_104)), inference(negUnitSimplification, [status(thm)], [c_121, c_199])).
% 5.00/1.95  tff(c_425, plain, (![A_167, E_165, D_169, C_166, F_168]: (~r2_hidden(C_166, A_167) | k4_mcart_1(C_166, D_169, E_165, F_168)!='#skF_4'(A_167) | k1_xboole_0=A_167)), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.00/1.95  tff(c_433, plain, (![C_8, D_169, E_165, F_168]: (k4_mcart_1(C_8, D_169, E_165, F_168)!='#skF_4'(k1_tarski(C_8)) | k1_tarski(C_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_425])).
% 5.00/1.95  tff(c_438, plain, (![C_8, D_169, E_165, F_168]: (k4_mcart_1(C_8, D_169, E_165, F_168)!=C_8 | k1_tarski(C_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_433])).
% 5.00/1.95  tff(c_439, plain, (![C_8, D_169, E_165, F_168]: (k4_mcart_1(C_8, D_169, E_165, F_168)!=C_8)), inference(negUnitSimplification, [status(thm)], [c_121, c_438])).
% 5.00/1.95  tff(c_72, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.00/1.95  tff(c_183, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_72])).
% 5.00/1.95  tff(c_763, plain, (![D_231, B_234, A_233, E_230, C_232]: (k11_mcart_1(A_233, B_234, C_232, D_231, E_230)=k2_mcart_1(E_230) | ~m1_subset_1(E_230, k4_zfmisc_1(A_233, B_234, C_232, D_231)) | k1_xboole_0=D_231 | k1_xboole_0=C_232 | k1_xboole_0=B_234 | k1_xboole_0=A_233)), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.00/1.95  tff(c_781, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_74, c_763])).
% 5.00/1.95  tff(c_788, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_76, c_781])).
% 5.00/1.95  tff(c_1022, plain, (![A_308, C_305, B_306, D_304, E_307]: (k4_mcart_1(k8_mcart_1(A_308, B_306, C_305, D_304, E_307), k9_mcart_1(A_308, B_306, C_305, D_304, E_307), k10_mcart_1(A_308, B_306, C_305, D_304, E_307), k11_mcart_1(A_308, B_306, C_305, D_304, E_307))=E_307 | ~m1_subset_1(E_307, k4_zfmisc_1(A_308, B_306, C_305, D_304)) | k1_xboole_0=D_304 | k1_xboole_0=C_305 | k1_xboole_0=B_306 | k1_xboole_0=A_308)), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.00/1.95  tff(c_1061, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_788, c_1022])).
% 5.00/1.95  tff(c_1068, plain, (k4_mcart_1('#skF_9', k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_183, c_1061])).
% 5.00/1.95  tff(c_1070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_76, c_439, c_1068])).
% 5.00/1.95  tff(c_1071, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_72])).
% 5.00/1.95  tff(c_1210, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_1071])).
% 5.00/1.95  tff(c_1624, plain, (![C_446, D_445, A_447, E_444, B_448]: (k11_mcart_1(A_447, B_448, C_446, D_445, E_444)=k2_mcart_1(E_444) | ~m1_subset_1(E_444, k4_zfmisc_1(A_447, B_448, C_446, D_445)) | k1_xboole_0=D_445 | k1_xboole_0=C_446 | k1_xboole_0=B_448 | k1_xboole_0=A_447)), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.00/1.95  tff(c_1639, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_74, c_1624])).
% 5.00/1.95  tff(c_1645, plain, (k2_mcart_1('#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1210, c_1639])).
% 5.00/1.95  tff(c_1646, plain, (k2_mcart_1('#skF_9')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_76, c_1645])).
% 5.00/1.95  tff(c_1311, plain, (![A_371, B_372, C_373, D_374]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_371, B_372), C_373), D_374)=k4_zfmisc_1(A_371, B_372, C_373, D_374))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.00/1.95  tff(c_32, plain, (![C_23, A_20, B_21]: (k2_mcart_1(C_23)!=C_23 | ~m1_subset_1(C_23, k2_zfmisc_1(A_20, B_21)) | k1_xboole_0=B_21 | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.00/1.95  tff(c_2098, plain, (![C_536, D_540, A_538, C_537, B_539]: (k2_mcart_1(C_536)!=C_536 | ~m1_subset_1(C_536, k4_zfmisc_1(A_538, B_539, C_537, D_540)) | k1_xboole_0=D_540 | k2_zfmisc_1(k2_zfmisc_1(A_538, B_539), C_537)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1311, c_32])).
% 5.00/1.95  tff(c_2116, plain, (k2_mcart_1('#skF_9')!='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_2098])).
% 5.00/1.95  tff(c_2124, plain, (k1_xboole_0='#skF_8' | k2_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1646, c_2116])).
% 5.00/1.95  tff(c_2125, plain, (k2_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_2124])).
% 5.00/1.95  tff(c_20, plain, (![B_12, A_11]: (k1_xboole_0=B_12 | k1_xboole_0=A_11 | k2_zfmisc_1(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.00/1.95  tff(c_2150, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2125, c_20])).
% 5.00/1.95  tff(c_2164, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_2150])).
% 5.00/1.95  tff(c_2186, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2164, c_20])).
% 5.00/1.95  tff(c_2200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_2186])).
% 5.00/1.95  tff(c_2201, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_1071])).
% 5.00/1.95  tff(c_2229, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_2201])).
% 5.00/1.95  tff(c_2665, plain, (![D_644, C_645, B_647, A_646, E_643]: (k11_mcart_1(A_646, B_647, C_645, D_644, E_643)=k2_mcart_1(E_643) | ~m1_subset_1(E_643, k4_zfmisc_1(A_646, B_647, C_645, D_644)) | k1_xboole_0=D_644 | k1_xboole_0=C_645 | k1_xboole_0=B_647 | k1_xboole_0=A_646)), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.00/1.95  tff(c_2683, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_74, c_2665])).
% 5.00/1.95  tff(c_2690, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_76, c_2683])).
% 5.00/1.95  tff(c_2896, plain, (![A_716, C_713, D_712, E_715, B_714]: (k4_mcart_1(k8_mcart_1(A_716, B_714, C_713, D_712, E_715), k9_mcart_1(A_716, B_714, C_713, D_712, E_715), k10_mcart_1(A_716, B_714, C_713, D_712, E_715), k11_mcart_1(A_716, B_714, C_713, D_712, E_715))=E_715 | ~m1_subset_1(E_715, k4_zfmisc_1(A_716, B_714, C_713, D_712)) | k1_xboole_0=D_712 | k1_xboole_0=C_713 | k1_xboole_0=B_714 | k1_xboole_0=A_716)), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.00/1.95  tff(c_2935, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2690, c_2896])).
% 5.00/1.95  tff(c_2942, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2229, c_2935])).
% 5.00/1.95  tff(c_2944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_76, c_2322, c_2942])).
% 5.00/1.95  tff(c_2945, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_2201])).
% 5.00/1.95  tff(c_3304, plain, (![E_802, A_805, D_803, B_806, C_804]: (k11_mcart_1(A_805, B_806, C_804, D_803, E_802)=k2_mcart_1(E_802) | ~m1_subset_1(E_802, k4_zfmisc_1(A_805, B_806, C_804, D_803)) | k1_xboole_0=D_803 | k1_xboole_0=C_804 | k1_xboole_0=B_806 | k1_xboole_0=A_805)), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.00/1.95  tff(c_3319, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_74, c_3304])).
% 5.00/1.95  tff(c_3326, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_76, c_3319])).
% 5.00/1.95  tff(c_3608, plain, (![D_869, C_870, A_873, B_871, E_872]: (k4_mcart_1(k8_mcart_1(A_873, B_871, C_870, D_869, E_872), k9_mcart_1(A_873, B_871, C_870, D_869, E_872), k10_mcart_1(A_873, B_871, C_870, D_869, E_872), k11_mcart_1(A_873, B_871, C_870, D_869, E_872))=E_872 | ~m1_subset_1(E_872, k4_zfmisc_1(A_873, B_871, C_870, D_869)) | k1_xboole_0=D_869 | k1_xboole_0=C_870 | k1_xboole_0=B_871 | k1_xboole_0=A_873)), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.00/1.95  tff(c_3644, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3326, c_3608])).
% 5.00/1.95  tff(c_3651, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2945, c_3644])).
% 5.00/1.95  tff(c_3653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_76, c_3185, c_3651])).
% 5.00/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.95  
% 5.00/1.95  Inference rules
% 5.00/1.95  ----------------------
% 5.00/1.95  #Ref     : 0
% 5.00/1.95  #Sup     : 862
% 5.00/1.95  #Fact    : 0
% 5.00/1.95  #Define  : 0
% 5.00/1.95  #Split   : 3
% 5.00/1.95  #Chain   : 0
% 5.00/1.95  #Close   : 0
% 5.00/1.95  
% 5.00/1.95  Ordering : KBO
% 5.00/1.95  
% 5.00/1.95  Simplification rules
% 5.00/1.95  ----------------------
% 5.00/1.95  #Subsume      : 182
% 5.00/1.95  #Demod        : 443
% 5.00/1.95  #Tautology    : 379
% 5.00/1.95  #SimpNegUnit  : 90
% 5.00/1.95  #BackRed      : 7
% 5.00/1.95  
% 5.00/1.95  #Partial instantiations: 0
% 5.00/1.95  #Strategies tried      : 1
% 5.00/1.95  
% 5.00/1.95  Timing (in seconds)
% 5.00/1.95  ----------------------
% 5.00/1.95  Preprocessing        : 0.36
% 5.00/1.95  Parsing              : 0.19
% 5.00/1.95  CNF conversion       : 0.03
% 5.00/1.95  Main loop            : 0.80
% 5.00/1.95  Inferencing          : 0.32
% 5.00/1.95  Reduction            : 0.25
% 5.00/1.95  Demodulation         : 0.17
% 5.00/1.96  BG Simplification    : 0.05
% 5.00/1.96  Subsumption          : 0.14
% 5.00/1.96  Abstraction          : 0.05
% 5.00/1.96  MUC search           : 0.00
% 5.00/1.96  Cooper               : 0.00
% 5.00/1.96  Total                : 1.20
% 5.00/1.96  Index Insertion      : 0.00
% 5.00/1.96  Index Deletion       : 0.00
% 5.00/1.96  Index Matching       : 0.00
% 5.00/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
