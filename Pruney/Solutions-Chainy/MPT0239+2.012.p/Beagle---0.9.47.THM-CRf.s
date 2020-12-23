%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:53 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 185 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 333 expanded)
%              Number of equality atoms :   41 ( 198 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_428,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(k1_tarski(A_108),B_109) = k1_tarski(A_108)
      | r2_hidden(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [B_14] : k4_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) != k1_tarski(B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_440,plain,(
    ! [A_108] : r2_hidden(A_108,k1_tarski(A_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_18])).

tff(c_497,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( r2_hidden(k4_tarski(A_128,B_129),k2_zfmisc_1(C_130,D_131))
      | ~ r2_hidden(B_129,D_131)
      | ~ r2_hidden(A_128,C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k1_tarski(A_24),B_25) = k1_tarski(A_24)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,(
    ! [A_24] : r2_hidden(A_24,k1_tarski(A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_18])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12))
      | ~ r2_hidden(B_10,D_12)
      | ~ r2_hidden(A_9,C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_148,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_123,plain,(
    ! [A_35,C_36,B_37,D_38] :
      ( r2_hidden(A_35,C_36)
      | ~ r2_hidden(k4_tarski(A_35,B_37),k2_zfmisc_1(C_36,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_127,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_101,c_123])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k1_tarski(A_13)
      | B_14 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden(A_27,B_28)
      | k4_xboole_0(k1_tarski(A_27),B_28) != k1_tarski(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_111,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden(A_13,k1_tarski(B_14))
      | B_14 = A_13 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_103])).

tff(c_141,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_127,c_111])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_141])).

tff(c_147,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_147])).

tff(c_172,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_171,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_146,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_214,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_146,c_28])).

tff(c_215,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_214])).

tff(c_218,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_215])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_98,c_218])).

tff(c_224,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_267,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(k1_tarski(A_69),B_70) = k1_tarski(A_69)
      | r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_287,plain,(
    ! [A_69] : r2_hidden(A_69,k1_tarski(A_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_18])).

tff(c_223,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_229,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_290,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_30])).

tff(c_291,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_308,plain,(
    ! [B_76,D_77,A_78,C_79] :
      ( r2_hidden(B_76,D_77)
      | ~ r2_hidden(k4_tarski(A_78,B_76),k2_zfmisc_1(C_79,D_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_312,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_291,c_308])).

tff(c_293,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden(A_72,B_73)
      | k4_xboole_0(k1_tarski(A_72),B_73) != k1_tarski(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_301,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden(A_13,k1_tarski(B_14))
      | B_14 = A_13 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_293])).

tff(c_321,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_312,c_301])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_321])).

tff(c_327,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_333,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_32])).

tff(c_334,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_327])).

tff(c_352,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_326,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_392,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_352,c_326,c_28])).

tff(c_393,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_392])).

tff(c_396,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_393])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_287,c_396])).

tff(c_402,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_24,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_412,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_402,c_24])).

tff(c_401,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_496,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_402,c_412,c_401,c_22])).

tff(c_500,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_497,c_496])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_440,c_500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.15/1.25  
% 2.15/1.25  %Foreground sorts:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Background operators:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Foreground operators:
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  
% 2.26/1.26  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.26/1.26  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.26/1.26  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.26/1.26  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.26/1.26  tff(c_428, plain, (![A_108, B_109]: (k4_xboole_0(k1_tarski(A_108), B_109)=k1_tarski(A_108) | r2_hidden(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.26  tff(c_18, plain, (![B_14]: (k4_xboole_0(k1_tarski(B_14), k1_tarski(B_14))!=k1_tarski(B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.26  tff(c_440, plain, (![A_108]: (r2_hidden(A_108, k1_tarski(A_108)))), inference(superposition, [status(thm), theory('equality')], [c_428, c_18])).
% 2.26/1.26  tff(c_497, plain, (![A_128, B_129, C_130, D_131]: (r2_hidden(k4_tarski(A_128, B_129), k2_zfmisc_1(C_130, D_131)) | ~r2_hidden(B_129, D_131) | ~r2_hidden(A_128, C_130))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.26/1.26  tff(c_78, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), B_25)=k1_tarski(A_24) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.26  tff(c_98, plain, (![A_24]: (r2_hidden(A_24, k1_tarski(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_18])).
% 2.26/1.26  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)) | ~r2_hidden(B_10, D_12) | ~r2_hidden(A_9, C_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.26/1.26  tff(c_32, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.26  tff(c_148, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_32])).
% 2.26/1.26  tff(c_26, plain, ('#skF_3'='#skF_1' | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.26  tff(c_42, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_26])).
% 2.26/1.26  tff(c_30, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.26  tff(c_101, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_30])).
% 2.26/1.26  tff(c_123, plain, (![A_35, C_36, B_37, D_38]: (r2_hidden(A_35, C_36) | ~r2_hidden(k4_tarski(A_35, B_37), k2_zfmisc_1(C_36, D_38)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.26/1.26  tff(c_127, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_101, c_123])).
% 2.26/1.26  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k1_tarski(A_13) | B_14=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.26  tff(c_103, plain, (![A_27, B_28]: (~r2_hidden(A_27, B_28) | k4_xboole_0(k1_tarski(A_27), B_28)!=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.26  tff(c_111, plain, (![A_13, B_14]: (~r2_hidden(A_13, k1_tarski(B_14)) | B_14=A_13)), inference(superposition, [status(thm), theory('equality')], [c_20, c_103])).
% 2.26/1.26  tff(c_141, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_127, c_111])).
% 2.26/1.26  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_141])).
% 2.26/1.26  tff(c_147, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_30])).
% 2.26/1.26  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_147])).
% 2.26/1.26  tff(c_172, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_32])).
% 2.26/1.26  tff(c_171, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.26/1.26  tff(c_146, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.26/1.26  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.26  tff(c_214, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_146, c_28])).
% 2.26/1.26  tff(c_215, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_172, c_214])).
% 2.26/1.26  tff(c_218, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_215])).
% 2.26/1.26  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_98, c_218])).
% 2.26/1.26  tff(c_224, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_26])).
% 2.26/1.26  tff(c_267, plain, (![A_69, B_70]: (k4_xboole_0(k1_tarski(A_69), B_70)=k1_tarski(A_69) | r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.26  tff(c_287, plain, (![A_69]: (r2_hidden(A_69, k1_tarski(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_267, c_18])).
% 2.26/1.26  tff(c_223, plain, ('#skF_6'!='#skF_8' | '#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.26/1.26  tff(c_229, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_223])).
% 2.26/1.26  tff(c_290, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_30])).
% 2.26/1.26  tff(c_291, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_290])).
% 2.26/1.26  tff(c_308, plain, (![B_76, D_77, A_78, C_79]: (r2_hidden(B_76, D_77) | ~r2_hidden(k4_tarski(A_78, B_76), k2_zfmisc_1(C_79, D_77)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.26/1.26  tff(c_312, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_291, c_308])).
% 2.26/1.26  tff(c_293, plain, (![A_72, B_73]: (~r2_hidden(A_72, B_73) | k4_xboole_0(k1_tarski(A_72), B_73)!=k1_tarski(A_72))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.26  tff(c_301, plain, (![A_13, B_14]: (~r2_hidden(A_13, k1_tarski(B_14)) | B_14=A_13)), inference(superposition, [status(thm), theory('equality')], [c_20, c_293])).
% 2.26/1.26  tff(c_321, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_312, c_301])).
% 2.26/1.26  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_321])).
% 2.26/1.26  tff(c_327, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_290])).
% 2.26/1.26  tff(c_333, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_32])).
% 2.26/1.26  tff(c_334, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_333])).
% 2.26/1.26  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_334, c_327])).
% 2.26/1.26  tff(c_352, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_333])).
% 2.26/1.26  tff(c_326, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_290])).
% 2.26/1.26  tff(c_392, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_352, c_326, c_28])).
% 2.26/1.26  tff(c_393, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_327, c_392])).
% 2.26/1.26  tff(c_396, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_393])).
% 2.26/1.26  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_287, c_287, c_396])).
% 2.26/1.26  tff(c_402, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_223])).
% 2.26/1.26  tff(c_24, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.26  tff(c_412, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_402, c_24])).
% 2.26/1.26  tff(c_401, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_223])).
% 2.26/1.26  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.26  tff(c_496, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_402, c_412, c_401, c_22])).
% 2.26/1.26  tff(c_500, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_497, c_496])).
% 2.26/1.26  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_440, c_440, c_500])).
% 2.26/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.26  
% 2.26/1.26  Inference rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Ref     : 0
% 2.26/1.26  #Sup     : 97
% 2.26/1.26  #Fact    : 0
% 2.26/1.26  #Define  : 0
% 2.26/1.26  #Split   : 7
% 2.26/1.26  #Chain   : 0
% 2.26/1.26  #Close   : 0
% 2.26/1.26  
% 2.26/1.26  Ordering : KBO
% 2.26/1.26  
% 2.26/1.26  Simplification rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Subsume      : 6
% 2.26/1.26  #Demod        : 38
% 2.26/1.26  #Tautology    : 77
% 2.26/1.26  #SimpNegUnit  : 4
% 2.26/1.26  #BackRed      : 2
% 2.26/1.26  
% 2.26/1.26  #Partial instantiations: 0
% 2.26/1.26  #Strategies tried      : 1
% 2.26/1.26  
% 2.26/1.26  Timing (in seconds)
% 2.26/1.26  ----------------------
% 2.26/1.26  Preprocessing        : 0.28
% 2.26/1.26  Parsing              : 0.14
% 2.26/1.26  CNF conversion       : 0.02
% 2.26/1.26  Main loop            : 0.23
% 2.26/1.26  Inferencing          : 0.10
% 2.26/1.26  Reduction            : 0.06
% 2.26/1.27  Demodulation         : 0.04
% 2.26/1.27  BG Simplification    : 0.01
% 2.26/1.27  Subsumption          : 0.03
% 2.26/1.27  Abstraction          : 0.01
% 2.26/1.27  MUC search           : 0.00
% 2.26/1.27  Cooper               : 0.00
% 2.26/1.27  Total                : 0.54
% 2.26/1.27  Index Insertion      : 0.00
% 2.26/1.27  Index Deletion       : 0.00
% 2.26/1.27  Index Matching       : 0.00
% 2.26/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
