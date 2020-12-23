%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:08 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 237 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 575 expanded)
%              Number of equality atoms :  100 ( 487 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_48,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_135,plain,(
    ! [A_55,C_56,D_57,B_58] : k2_enumset1(k4_tarski(A_55,C_56),k4_tarski(A_55,D_57),k4_tarski(B_58,C_56),k4_tarski(B_58,D_57)) = k2_zfmisc_1(k2_tarski(A_55,B_58),k2_tarski(C_56,D_57)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,F_17,D_13] :
      ( F_17 = D_13
      | F_17 = C_12
      | F_17 = B_11
      | F_17 = A_10
      | ~ r2_hidden(F_17,k2_enumset1(A_10,B_11,C_12,D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_290,plain,(
    ! [C_121,A_122,F_123,B_120,D_124] :
      ( k4_tarski(B_120,D_124) = F_123
      | k4_tarski(B_120,C_121) = F_123
      | k4_tarski(A_122,D_124) = F_123
      | k4_tarski(A_122,C_121) = F_123
      | ~ r2_hidden(F_123,k2_zfmisc_1(k2_tarski(A_122,B_120),k2_tarski(C_121,D_124))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_8])).

tff(c_322,plain,
    ( k4_tarski('#skF_5','#skF_7') = '#skF_3'
    | k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_7') = '#skF_3'
    | k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_290])).

tff(c_323,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_40,plain,(
    ! [A_18,B_19] : k2_mcart_1(k4_tarski(A_18,B_19)) = B_19 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_363,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_40])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_363])).

tff(c_370,plain,
    ( k4_tarski('#skF_4','#skF_7') = '#skF_3'
    | k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_5','#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_372,plain,(
    k4_tarski('#skF_5','#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_412,plain,(
    k2_mcart_1('#skF_3') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_40])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_412])).

tff(c_419,plain,
    ( k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_422,plain,(
    k4_tarski('#skF_4','#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_462,plain,(
    k2_mcart_1('#skF_3') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_40])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_462])).

tff(c_469,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_510,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_40])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_510])).

tff(c_517,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_518,plain,(
    k2_mcart_1('#skF_3') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_525,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_46])).

tff(c_601,plain,(
    ! [A_169,C_170,D_171,B_172] : k2_enumset1(k4_tarski(A_169,C_170),k4_tarski(A_169,D_171),k4_tarski(B_172,C_170),k4_tarski(B_172,D_171)) = k2_zfmisc_1(k2_tarski(A_169,B_172),k2_tarski(C_170,D_171)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_747,plain,(
    ! [F_234,D_233,C_232,A_231,B_235] :
      ( k4_tarski(B_235,D_233) = F_234
      | k4_tarski(B_235,C_232) = F_234
      | k4_tarski(A_231,D_233) = F_234
      | k4_tarski(A_231,C_232) = F_234
      | ~ r2_hidden(F_234,k2_zfmisc_1(k2_tarski(A_231,B_235),k2_tarski(C_232,D_233))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_8])).

tff(c_779,plain,
    ( k4_tarski('#skF_5','#skF_7') = '#skF_3'
    | k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_7') = '#skF_3'
    | k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_747])).

tff(c_780,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_38,plain,(
    ! [A_18,B_19] : k1_mcart_1(k4_tarski(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_817,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_38])).

tff(c_826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_817])).

tff(c_827,plain,
    ( k4_tarski('#skF_4','#skF_7') = '#skF_3'
    | k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_5','#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_829,plain,(
    k4_tarski('#skF_5','#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_866,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_38])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_866])).

tff(c_876,plain,
    ( k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_878,plain,(
    k4_tarski('#skF_4','#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_915,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_38])).

tff(c_924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_915])).

tff(c_925,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_964,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_38])).

tff(c_973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_964])).

tff(c_974,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_975,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_982,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_50])).

tff(c_1057,plain,(
    ! [A_278,C_279,D_280,B_281] : k2_enumset1(k4_tarski(A_278,C_279),k4_tarski(A_278,D_280),k4_tarski(B_281,C_279),k4_tarski(B_281,D_280)) = k2_zfmisc_1(k2_tarski(A_278,B_281),k2_tarski(C_279,D_280)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1203,plain,(
    ! [B_341,D_337,F_339,C_340,A_338] :
      ( k4_tarski(B_341,D_337) = F_339
      | k4_tarski(B_341,C_340) = F_339
      | k4_tarski(A_338,D_337) = F_339
      | k4_tarski(A_338,C_340) = F_339
      | ~ r2_hidden(F_339,k2_zfmisc_1(k2_tarski(A_338,B_341),k2_tarski(C_340,D_337))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1057,c_8])).

tff(c_1235,plain,
    ( k4_tarski('#skF_5','#skF_7') = '#skF_3'
    | k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_7') = '#skF_3'
    | k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_1203])).

tff(c_1236,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1235])).

tff(c_1273,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_38])).

tff(c_1282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_982,c_1273])).

tff(c_1283,plain,
    ( k4_tarski('#skF_4','#skF_7') = '#skF_3'
    | k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_5','#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1235])).

tff(c_1286,plain,(
    k4_tarski('#skF_5','#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1283])).

tff(c_1323,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1286,c_38])).

tff(c_1332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_974,c_1323])).

tff(c_1333,plain,
    ( k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_1335,plain,(
    k4_tarski('#skF_4','#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1333])).

tff(c_1372,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1335,c_38])).

tff(c_1381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_982,c_1372])).

tff(c_1382,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1333])).

tff(c_1420,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1382,c_38])).

tff(c_1429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_974,c_1420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:09:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.54  
% 3.45/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.54  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 3.45/1.54  
% 3.45/1.54  %Foreground sorts:
% 3.45/1.54  
% 3.45/1.54  
% 3.45/1.54  %Background operators:
% 3.45/1.54  
% 3.45/1.54  
% 3.45/1.54  %Foreground operators:
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.45/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.45/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.45/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.45/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.45/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.45/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.45/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.45/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.54  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.45/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.54  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.45/1.54  
% 3.45/1.56  tff(f_64, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 3.45/1.56  tff(f_31, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 3.45/1.56  tff(f_49, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 3.45/1.56  tff(f_53, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.45/1.56  tff(c_48, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.56  tff(c_69, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_48])).
% 3.45/1.56  tff(c_44, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.56  tff(c_70, plain, (k2_mcart_1('#skF_3')!='#skF_7'), inference(splitLeft, [status(thm)], [c_44])).
% 3.45/1.56  tff(c_42, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.56  tff(c_135, plain, (![A_55, C_56, D_57, B_58]: (k2_enumset1(k4_tarski(A_55, C_56), k4_tarski(A_55, D_57), k4_tarski(B_58, C_56), k4_tarski(B_58, D_57))=k2_zfmisc_1(k2_tarski(A_55, B_58), k2_tarski(C_56, D_57)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.56  tff(c_8, plain, (![B_11, A_10, C_12, F_17, D_13]: (F_17=D_13 | F_17=C_12 | F_17=B_11 | F_17=A_10 | ~r2_hidden(F_17, k2_enumset1(A_10, B_11, C_12, D_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.45/1.56  tff(c_290, plain, (![C_121, A_122, F_123, B_120, D_124]: (k4_tarski(B_120, D_124)=F_123 | k4_tarski(B_120, C_121)=F_123 | k4_tarski(A_122, D_124)=F_123 | k4_tarski(A_122, C_121)=F_123 | ~r2_hidden(F_123, k2_zfmisc_1(k2_tarski(A_122, B_120), k2_tarski(C_121, D_124))))), inference(superposition, [status(thm), theory('equality')], [c_135, c_8])).
% 3.45/1.56  tff(c_322, plain, (k4_tarski('#skF_5', '#skF_7')='#skF_3' | k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_7')='#skF_3' | k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_42, c_290])).
% 3.45/1.56  tff(c_323, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_322])).
% 3.45/1.56  tff(c_40, plain, (![A_18, B_19]: (k2_mcart_1(k4_tarski(A_18, B_19))=B_19)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.56  tff(c_363, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_323, c_40])).
% 3.45/1.56  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_363])).
% 3.45/1.56  tff(c_370, plain, (k4_tarski('#skF_4', '#skF_7')='#skF_3' | k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_5', '#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_322])).
% 3.45/1.56  tff(c_372, plain, (k4_tarski('#skF_5', '#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_370])).
% 3.45/1.56  tff(c_412, plain, (k2_mcart_1('#skF_3')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_372, c_40])).
% 3.45/1.56  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_412])).
% 3.45/1.56  tff(c_419, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_370])).
% 3.45/1.56  tff(c_422, plain, (k4_tarski('#skF_4', '#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_419])).
% 3.45/1.56  tff(c_462, plain, (k2_mcart_1('#skF_3')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_422, c_40])).
% 3.45/1.56  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_462])).
% 3.45/1.56  tff(c_469, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_419])).
% 3.45/1.56  tff(c_510, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_469, c_40])).
% 3.45/1.56  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_510])).
% 3.45/1.56  tff(c_517, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 3.45/1.56  tff(c_518, plain, (k2_mcart_1('#skF_3')='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 3.45/1.56  tff(c_46, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.56  tff(c_525, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_518, c_46])).
% 3.45/1.56  tff(c_601, plain, (![A_169, C_170, D_171, B_172]: (k2_enumset1(k4_tarski(A_169, C_170), k4_tarski(A_169, D_171), k4_tarski(B_172, C_170), k4_tarski(B_172, D_171))=k2_zfmisc_1(k2_tarski(A_169, B_172), k2_tarski(C_170, D_171)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.56  tff(c_747, plain, (![F_234, D_233, C_232, A_231, B_235]: (k4_tarski(B_235, D_233)=F_234 | k4_tarski(B_235, C_232)=F_234 | k4_tarski(A_231, D_233)=F_234 | k4_tarski(A_231, C_232)=F_234 | ~r2_hidden(F_234, k2_zfmisc_1(k2_tarski(A_231, B_235), k2_tarski(C_232, D_233))))), inference(superposition, [status(thm), theory('equality')], [c_601, c_8])).
% 3.45/1.56  tff(c_779, plain, (k4_tarski('#skF_5', '#skF_7')='#skF_3' | k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_7')='#skF_3' | k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_42, c_747])).
% 3.45/1.56  tff(c_780, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_779])).
% 3.45/1.56  tff(c_38, plain, (![A_18, B_19]: (k1_mcart_1(k4_tarski(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.56  tff(c_817, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_780, c_38])).
% 3.45/1.56  tff(c_826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_817])).
% 3.45/1.56  tff(c_827, plain, (k4_tarski('#skF_4', '#skF_7')='#skF_3' | k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_5', '#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_779])).
% 3.45/1.56  tff(c_829, plain, (k4_tarski('#skF_5', '#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_827])).
% 3.45/1.56  tff(c_866, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_829, c_38])).
% 3.45/1.56  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_517, c_866])).
% 3.45/1.56  tff(c_876, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_827])).
% 3.45/1.56  tff(c_878, plain, (k4_tarski('#skF_4', '#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_876])).
% 3.45/1.56  tff(c_915, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_878, c_38])).
% 3.45/1.56  tff(c_924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_915])).
% 3.45/1.56  tff(c_925, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_876])).
% 3.45/1.56  tff(c_964, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_925, c_38])).
% 3.45/1.56  tff(c_973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_517, c_964])).
% 3.45/1.56  tff(c_974, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 3.45/1.56  tff(c_975, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 3.45/1.56  tff(c_50, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.56  tff(c_982, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_975, c_50])).
% 3.45/1.56  tff(c_1057, plain, (![A_278, C_279, D_280, B_281]: (k2_enumset1(k4_tarski(A_278, C_279), k4_tarski(A_278, D_280), k4_tarski(B_281, C_279), k4_tarski(B_281, D_280))=k2_zfmisc_1(k2_tarski(A_278, B_281), k2_tarski(C_279, D_280)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.56  tff(c_1203, plain, (![B_341, D_337, F_339, C_340, A_338]: (k4_tarski(B_341, D_337)=F_339 | k4_tarski(B_341, C_340)=F_339 | k4_tarski(A_338, D_337)=F_339 | k4_tarski(A_338, C_340)=F_339 | ~r2_hidden(F_339, k2_zfmisc_1(k2_tarski(A_338, B_341), k2_tarski(C_340, D_337))))), inference(superposition, [status(thm), theory('equality')], [c_1057, c_8])).
% 3.45/1.56  tff(c_1235, plain, (k4_tarski('#skF_5', '#skF_7')='#skF_3' | k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_7')='#skF_3' | k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_42, c_1203])).
% 3.45/1.56  tff(c_1236, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_1235])).
% 3.45/1.56  tff(c_1273, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1236, c_38])).
% 3.45/1.56  tff(c_1282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_982, c_1273])).
% 3.45/1.56  tff(c_1283, plain, (k4_tarski('#skF_4', '#skF_7')='#skF_3' | k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_5', '#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_1235])).
% 3.45/1.56  tff(c_1286, plain, (k4_tarski('#skF_5', '#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_1283])).
% 3.45/1.56  tff(c_1323, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1286, c_38])).
% 3.45/1.56  tff(c_1332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_974, c_1323])).
% 3.45/1.56  tff(c_1333, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_1283])).
% 3.45/1.56  tff(c_1335, plain, (k4_tarski('#skF_4', '#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_1333])).
% 3.45/1.56  tff(c_1372, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1335, c_38])).
% 3.45/1.56  tff(c_1381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_982, c_1372])).
% 3.45/1.56  tff(c_1382, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_1333])).
% 3.45/1.56  tff(c_1420, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1382, c_38])).
% 3.45/1.56  tff(c_1429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_974, c_1420])).
% 3.45/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.56  
% 3.45/1.56  Inference rules
% 3.45/1.56  ----------------------
% 3.45/1.56  #Ref     : 0
% 3.45/1.56  #Sup     : 353
% 3.45/1.56  #Fact    : 0
% 3.45/1.56  #Define  : 0
% 3.45/1.56  #Split   : 11
% 3.45/1.56  #Chain   : 0
% 3.45/1.56  #Close   : 0
% 3.45/1.56  
% 3.45/1.56  Ordering : KBO
% 3.45/1.56  
% 3.45/1.56  Simplification rules
% 3.45/1.56  ----------------------
% 3.45/1.56  #Subsume      : 8
% 3.45/1.56  #Demod        : 63
% 3.45/1.56  #Tautology    : 122
% 3.45/1.56  #SimpNegUnit  : 12
% 3.45/1.56  #BackRed      : 1
% 3.45/1.56  
% 3.45/1.56  #Partial instantiations: 0
% 3.45/1.56  #Strategies tried      : 1
% 3.45/1.56  
% 3.45/1.56  Timing (in seconds)
% 3.45/1.56  ----------------------
% 3.45/1.56  Preprocessing        : 0.31
% 3.45/1.56  Parsing              : 0.15
% 3.45/1.56  CNF conversion       : 0.02
% 3.45/1.56  Main loop            : 0.49
% 3.45/1.56  Inferencing          : 0.19
% 3.45/1.56  Reduction            : 0.14
% 3.45/1.56  Demodulation         : 0.10
% 3.45/1.56  BG Simplification    : 0.03
% 3.45/1.56  Subsumption          : 0.09
% 3.45/1.56  Abstraction          : 0.03
% 3.45/1.56  MUC search           : 0.00
% 3.45/1.56  Cooper               : 0.00
% 3.45/1.56  Total                : 0.83
% 3.45/1.56  Index Insertion      : 0.00
% 3.45/1.56  Index Deletion       : 0.00
% 3.45/1.56  Index Matching       : 0.00
% 3.45/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
