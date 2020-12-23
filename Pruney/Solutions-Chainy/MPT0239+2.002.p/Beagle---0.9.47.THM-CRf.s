%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:52 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 212 expanded)
%              Number of leaves         :   25 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 388 expanded)
%              Number of equality atoms :   57 ( 251 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_477,plain,(
    ! [A_158,B_159] : k1_enumset1(A_158,A_158,B_159) = k2_tarski(A_158,B_159) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_495,plain,(
    ! [B_160,A_161] : r2_hidden(B_160,k2_tarski(A_161,B_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_4])).

tff(c_498,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_495])).

tff(c_560,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( r2_hidden(k4_tarski(A_185,B_186),k2_zfmisc_1(C_187,D_188))
      | ~ r2_hidden(B_186,D_188)
      | ~ r2_hidden(A_185,C_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ! [B_30,A_31] : r2_hidden(B_30,k2_tarski(A_31,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_4])).

tff(c_83,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_80])).

tff(c_32,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17))
      | ~ r2_hidden(B_15,D_17)
      | ~ r2_hidden(A_14,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_48,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_101,plain,(
    ! [A_38,C_39,B_40,D_41] :
      ( r2_hidden(A_38,C_39)
      | ~ r2_hidden(k4_tarski(A_38,B_40),k2_zfmisc_1(C_39,D_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_84,c_101])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_112,plain,(
    ! [E_46,C_47,B_48,A_49] :
      ( E_46 = C_47
      | E_46 = B_48
      | E_46 = A_49
      | ~ r2_hidden(E_46,k1_enumset1(A_49,B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_131,plain,(
    ! [E_50,B_51,A_52] :
      ( E_50 = B_51
      | E_50 = A_52
      | E_50 = A_52
      | ~ r2_hidden(E_50,k2_tarski(A_52,B_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_112])).

tff(c_145,plain,(
    ! [E_53,A_54] :
      ( E_53 = A_54
      | E_53 = A_54
      | E_53 = A_54
      | ~ r2_hidden(E_53,k1_tarski(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_131])).

tff(c_151,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_105,c_145])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_58,c_151])).

tff(c_161,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_46])).

tff(c_160,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_243,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_160,c_44])).

tff(c_244,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_243])).

tff(c_247,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_244])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_247])).

tff(c_253,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_264,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_282,plain,(
    ! [B_93,A_94] : r2_hidden(B_93,k2_tarski(A_94,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_4])).

tff(c_285,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_282])).

tff(c_252,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_258,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_286,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_48])).

tff(c_287,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_310,plain,(
    ! [B_105,D_106,A_107,C_108] :
      ( r2_hidden(B_105,D_106)
      | ~ r2_hidden(k4_tarski(A_107,B_105),k2_zfmisc_1(C_108,D_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_314,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_287,c_310])).

tff(c_318,plain,(
    ! [E_109,C_110,B_111,A_112] :
      ( E_109 = C_110
      | E_109 = B_111
      | E_109 = A_112
      | ~ r2_hidden(E_109,k1_enumset1(A_112,B_111,C_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_337,plain,(
    ! [E_113,B_114,A_115] :
      ( E_113 = B_114
      | E_113 = A_115
      | E_113 = A_115
      | ~ r2_hidden(E_113,k2_tarski(A_115,B_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_318])).

tff(c_351,plain,(
    ! [E_116,A_117] :
      ( E_116 = A_117
      | E_116 = A_117
      | E_116 = A_117
      | ~ r2_hidden(E_116,k1_tarski(A_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_337])).

tff(c_354,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_314,c_351])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_258,c_258,c_354])).

tff(c_363,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_384,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_46])).

tff(c_385,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_384])).

tff(c_362,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_449,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_385,c_362,c_44])).

tff(c_450,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_449])).

tff(c_453,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_450])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_285,c_453])).

tff(c_459,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_42,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_472,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_459,c_42])).

tff(c_458,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_38,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_559,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_459,c_472,c_458,c_38])).

tff(c_563,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_560,c_559])).

tff(c_573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_498,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n002.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 16:06:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.39  
% 2.52/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.39  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 2.52/1.39  
% 2.52/1.39  %Foreground sorts:
% 2.52/1.39  
% 2.52/1.39  
% 2.52/1.39  %Background operators:
% 2.52/1.39  
% 2.52/1.39  
% 2.52/1.39  %Foreground operators:
% 2.52/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.52/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.52/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.39  tff('#skF_10', type, '#skF_10': $i).
% 2.52/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.52/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.52/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.52/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.52/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.52/1.39  
% 2.52/1.41  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.52/1.41  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.52/1.41  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.52/1.41  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.52/1.41  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.52/1.41  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.41  tff(c_477, plain, (![A_158, B_159]: (k1_enumset1(A_158, A_158, B_159)=k2_tarski(A_158, B_159))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.41  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.41  tff(c_495, plain, (![B_160, A_161]: (r2_hidden(B_160, k2_tarski(A_161, B_160)))), inference(superposition, [status(thm), theory('equality')], [c_477, c_4])).
% 2.52/1.41  tff(c_498, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_495])).
% 2.52/1.41  tff(c_560, plain, (![A_185, B_186, C_187, D_188]: (r2_hidden(k4_tarski(A_185, B_186), k2_zfmisc_1(C_187, D_188)) | ~r2_hidden(B_186, D_188) | ~r2_hidden(A_185, C_187))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.41  tff(c_62, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.41  tff(c_80, plain, (![B_30, A_31]: (r2_hidden(B_30, k2_tarski(A_31, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_4])).
% 2.52/1.41  tff(c_83, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_80])).
% 2.52/1.41  tff(c_32, plain, (![A_14, B_15, C_16, D_17]: (r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)) | ~r2_hidden(B_15, D_17) | ~r2_hidden(A_14, C_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.41  tff(c_40, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.41  tff(c_58, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_40])).
% 2.52/1.41  tff(c_48, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.41  tff(c_84, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_48])).
% 2.52/1.41  tff(c_101, plain, (![A_38, C_39, B_40, D_41]: (r2_hidden(A_38, C_39) | ~r2_hidden(k4_tarski(A_38, B_40), k2_zfmisc_1(C_39, D_41)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.41  tff(c_105, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_84, c_101])).
% 2.52/1.41  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.41  tff(c_112, plain, (![E_46, C_47, B_48, A_49]: (E_46=C_47 | E_46=B_48 | E_46=A_49 | ~r2_hidden(E_46, k1_enumset1(A_49, B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.41  tff(c_131, plain, (![E_50, B_51, A_52]: (E_50=B_51 | E_50=A_52 | E_50=A_52 | ~r2_hidden(E_50, k2_tarski(A_52, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_112])).
% 2.52/1.41  tff(c_145, plain, (![E_53, A_54]: (E_53=A_54 | E_53=A_54 | E_53=A_54 | ~r2_hidden(E_53, k1_tarski(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_131])).
% 2.52/1.41  tff(c_151, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_105, c_145])).
% 2.52/1.41  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_58, c_151])).
% 2.52/1.41  tff(c_161, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_48])).
% 2.52/1.41  tff(c_46, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.41  tff(c_182, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_161, c_46])).
% 2.52/1.41  tff(c_160, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 2.52/1.41  tff(c_44, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.41  tff(c_243, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_160, c_44])).
% 2.52/1.41  tff(c_244, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_161, c_243])).
% 2.52/1.41  tff(c_247, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_244])).
% 2.52/1.41  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_247])).
% 2.52/1.41  tff(c_253, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_40])).
% 2.52/1.41  tff(c_264, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.41  tff(c_282, plain, (![B_93, A_94]: (r2_hidden(B_93, k2_tarski(A_94, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_4])).
% 2.52/1.41  tff(c_285, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_282])).
% 2.52/1.41  tff(c_252, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.52/1.41  tff(c_258, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_252])).
% 2.52/1.41  tff(c_286, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_48])).
% 2.52/1.41  tff(c_287, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_286])).
% 2.52/1.41  tff(c_310, plain, (![B_105, D_106, A_107, C_108]: (r2_hidden(B_105, D_106) | ~r2_hidden(k4_tarski(A_107, B_105), k2_zfmisc_1(C_108, D_106)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.41  tff(c_314, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_287, c_310])).
% 2.52/1.41  tff(c_318, plain, (![E_109, C_110, B_111, A_112]: (E_109=C_110 | E_109=B_111 | E_109=A_112 | ~r2_hidden(E_109, k1_enumset1(A_112, B_111, C_110)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.41  tff(c_337, plain, (![E_113, B_114, A_115]: (E_113=B_114 | E_113=A_115 | E_113=A_115 | ~r2_hidden(E_113, k2_tarski(A_115, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_318])).
% 2.52/1.41  tff(c_351, plain, (![E_116, A_117]: (E_116=A_117 | E_116=A_117 | E_116=A_117 | ~r2_hidden(E_116, k1_tarski(A_117)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_337])).
% 2.52/1.41  tff(c_354, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_314, c_351])).
% 2.52/1.41  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_258, c_258, c_354])).
% 2.52/1.41  tff(c_363, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_286])).
% 2.52/1.41  tff(c_384, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_46])).
% 2.52/1.41  tff(c_385, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_363, c_384])).
% 2.52/1.41  tff(c_362, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_286])).
% 2.52/1.41  tff(c_449, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_385, c_362, c_44])).
% 2.52/1.41  tff(c_450, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_363, c_449])).
% 2.52/1.41  tff(c_453, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_450])).
% 2.52/1.41  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_285, c_453])).
% 2.52/1.41  tff(c_459, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_252])).
% 2.52/1.41  tff(c_42, plain, ('#skF_5'='#skF_3' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.41  tff(c_472, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_253, c_459, c_42])).
% 2.52/1.41  tff(c_458, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_252])).
% 2.52/1.41  tff(c_38, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.41  tff(c_559, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_459, c_472, c_458, c_38])).
% 2.52/1.41  tff(c_563, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_560, c_559])).
% 2.52/1.41  tff(c_573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_498, c_498, c_563])).
% 2.52/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.41  
% 2.52/1.41  Inference rules
% 2.52/1.41  ----------------------
% 2.52/1.41  #Ref     : 0
% 2.52/1.41  #Sup     : 109
% 2.52/1.41  #Fact    : 0
% 2.52/1.41  #Define  : 0
% 2.52/1.41  #Split   : 5
% 2.52/1.41  #Chain   : 0
% 2.52/1.41  #Close   : 0
% 2.52/1.41  
% 2.52/1.41  Ordering : KBO
% 2.52/1.41  
% 2.52/1.41  Simplification rules
% 2.52/1.41  ----------------------
% 2.52/1.41  #Subsume      : 5
% 2.52/1.41  #Demod        : 47
% 2.52/1.41  #Tautology    : 81
% 2.52/1.41  #SimpNegUnit  : 6
% 2.52/1.41  #BackRed      : 0
% 2.52/1.41  
% 2.52/1.41  #Partial instantiations: 0
% 2.52/1.41  #Strategies tried      : 1
% 2.52/1.41  
% 2.52/1.41  Timing (in seconds)
% 2.52/1.41  ----------------------
% 2.52/1.41  Preprocessing        : 0.33
% 2.52/1.41  Parsing              : 0.16
% 2.52/1.41  CNF conversion       : 0.03
% 2.52/1.41  Main loop            : 0.27
% 2.52/1.41  Inferencing          : 0.11
% 2.52/1.41  Reduction            : 0.08
% 2.52/1.41  Demodulation         : 0.06
% 2.52/1.41  BG Simplification    : 0.02
% 2.52/1.41  Subsumption          : 0.04
% 2.52/1.41  Abstraction          : 0.01
% 2.52/1.41  MUC search           : 0.00
% 2.52/1.41  Cooper               : 0.00
% 2.52/1.41  Total                : 0.64
% 2.52/1.41  Index Insertion      : 0.00
% 2.52/1.41  Index Deletion       : 0.00
% 2.52/1.41  Index Matching       : 0.00
% 2.52/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
