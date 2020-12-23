%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:53 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 177 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 317 expanded)
%              Number of equality atoms :   34 ( 156 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_377,plain,(
    ! [A_109,B_110] :
      ( r1_xboole_0(k1_tarski(A_109),B_110)
      | r2_hidden(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [B_16] : ~ r1_xboole_0(k1_tarski(B_16),k1_tarski(B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_386,plain,(
    ! [A_109] : r2_hidden(A_109,k1_tarski(A_109)) ),
    inference(resolution,[status(thm)],[c_377,c_18])).

tff(c_407,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( r2_hidden(k4_tarski(A_123,B_124),k2_zfmisc_1(C_125,D_126))
      | ~ r2_hidden(B_124,D_126)
      | ~ r2_hidden(A_123,C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(k1_tarski(A_27),B_28)
      | r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(resolution,[status(thm)],[c_57,c_18])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14))
      | ~ r2_hidden(B_12,D_14)
      | ~ r2_hidden(A_11,C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_67,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_97,plain,(
    ! [A_39,C_40,B_41,D_42] :
      ( r2_hidden(A_39,C_40)
      | ~ r2_hidden(k4_tarski(A_39,B_41),k2_zfmisc_1(C_40,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_67,c_97])).

tff(c_45,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(k1_tarski(A_23),k1_tarski(B_24))
      | B_24 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden(A_7,B_8)
      | ~ r1_xboole_0(k1_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden(A_23,k1_tarski(B_24))
      | B_24 = A_23 ) ),
    inference(resolution,[status(thm)],[c_45,c_8])).

tff(c_115,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_101,c_53])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_115])).

tff(c_121,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_121])).

tff(c_154,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_153,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_120,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_204,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_120,c_28])).

tff(c_205,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_204])).

tff(c_208,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_205])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_208])).

tff(c_214,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_244,plain,(
    ! [A_75,B_76] :
      ( r1_xboole_0(k1_tarski(A_75),B_76)
      | r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_253,plain,(
    ! [A_75] : r2_hidden(A_75,k1_tarski(A_75)) ),
    inference(resolution,[status(thm)],[c_244,c_18])).

tff(c_213,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_219,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_254,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_30])).

tff(c_255,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_271,plain,(
    ! [B_81,D_82,A_83,C_84] :
      ( r2_hidden(B_81,D_82)
      | ~ r2_hidden(k4_tarski(A_83,B_81),k2_zfmisc_1(C_84,D_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_275,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_255,c_271])).

tff(c_223,plain,(
    ! [A_69,B_70] :
      ( r1_xboole_0(k1_tarski(A_69),k1_tarski(B_70))
      | B_70 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_231,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden(A_69,k1_tarski(B_70))
      | B_70 = A_69 ) ),
    inference(resolution,[status(thm)],[c_223,c_8])).

tff(c_278,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_275,c_231])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_278])).

tff(c_284,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_304,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_32])).

tff(c_305,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_304])).

tff(c_283,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_329,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_305,c_283,c_28])).

tff(c_330,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_329])).

tff(c_333,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_330])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_333])).

tff(c_339,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_24,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_349,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_339,c_24])).

tff(c_338,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_406,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_339,c_349,c_338,c_22])).

tff(c_410,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_407,c_406])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_386,c_410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.32  
% 1.97/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.33  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 1.97/1.33  
% 1.97/1.33  %Foreground sorts:
% 1.97/1.33  
% 1.97/1.33  
% 1.97/1.33  %Background operators:
% 1.97/1.33  
% 1.97/1.33  
% 1.97/1.33  %Foreground operators:
% 1.97/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.33  tff('#skF_7', type, '#skF_7': $i).
% 1.97/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.33  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.33  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.33  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.33  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.33  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.33  tff('#skF_8', type, '#skF_8': $i).
% 1.97/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.33  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.33  
% 2.28/1.34  tff(f_41, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.28/1.34  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.28/1.34  tff(f_47, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.28/1.34  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.28/1.34  tff(f_57, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.28/1.34  tff(f_36, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.28/1.34  tff(c_377, plain, (![A_109, B_110]: (r1_xboole_0(k1_tarski(A_109), B_110) | r2_hidden(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.34  tff(c_18, plain, (![B_16]: (~r1_xboole_0(k1_tarski(B_16), k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.34  tff(c_386, plain, (![A_109]: (r2_hidden(A_109, k1_tarski(A_109)))), inference(resolution, [status(thm)], [c_377, c_18])).
% 2.28/1.34  tff(c_407, plain, (![A_123, B_124, C_125, D_126]: (r2_hidden(k4_tarski(A_123, B_124), k2_zfmisc_1(C_125, D_126)) | ~r2_hidden(B_124, D_126) | ~r2_hidden(A_123, C_125))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.34  tff(c_57, plain, (![A_27, B_28]: (r1_xboole_0(k1_tarski(A_27), B_28) | r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.34  tff(c_66, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(resolution, [status(thm)], [c_57, c_18])).
% 2.28/1.34  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)) | ~r2_hidden(B_12, D_14) | ~r2_hidden(A_11, C_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.34  tff(c_32, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.34  tff(c_122, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_32])).
% 2.28/1.34  tff(c_26, plain, ('#skF_3'='#skF_1' | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.34  tff(c_43, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_26])).
% 2.28/1.34  tff(c_30, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.34  tff(c_67, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_30])).
% 2.28/1.34  tff(c_97, plain, (![A_39, C_40, B_41, D_42]: (r2_hidden(A_39, C_40) | ~r2_hidden(k4_tarski(A_39, B_41), k2_zfmisc_1(C_40, D_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.34  tff(c_101, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_67, c_97])).
% 2.28/1.34  tff(c_45, plain, (![A_23, B_24]: (r1_xboole_0(k1_tarski(A_23), k1_tarski(B_24)) | B_24=A_23)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.28/1.34  tff(c_8, plain, (![A_7, B_8]: (~r2_hidden(A_7, B_8) | ~r1_xboole_0(k1_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.28/1.34  tff(c_53, plain, (![A_23, B_24]: (~r2_hidden(A_23, k1_tarski(B_24)) | B_24=A_23)), inference(resolution, [status(thm)], [c_45, c_8])).
% 2.28/1.34  tff(c_115, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_101, c_53])).
% 2.28/1.34  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_115])).
% 2.28/1.34  tff(c_121, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_30])).
% 2.28/1.34  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_121])).
% 2.28/1.34  tff(c_154, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_32])).
% 2.28/1.34  tff(c_153, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.28/1.34  tff(c_120, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.28/1.34  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.34  tff(c_204, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_120, c_28])).
% 2.28/1.34  tff(c_205, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_154, c_204])).
% 2.28/1.34  tff(c_208, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_205])).
% 2.28/1.34  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_208])).
% 2.28/1.34  tff(c_214, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_26])).
% 2.28/1.34  tff(c_244, plain, (![A_75, B_76]: (r1_xboole_0(k1_tarski(A_75), B_76) | r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.34  tff(c_253, plain, (![A_75]: (r2_hidden(A_75, k1_tarski(A_75)))), inference(resolution, [status(thm)], [c_244, c_18])).
% 2.28/1.34  tff(c_213, plain, ('#skF_6'!='#skF_8' | '#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.28/1.34  tff(c_219, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_213])).
% 2.28/1.34  tff(c_254, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_30])).
% 2.28/1.34  tff(c_255, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_254])).
% 2.28/1.34  tff(c_271, plain, (![B_81, D_82, A_83, C_84]: (r2_hidden(B_81, D_82) | ~r2_hidden(k4_tarski(A_83, B_81), k2_zfmisc_1(C_84, D_82)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.34  tff(c_275, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_255, c_271])).
% 2.28/1.34  tff(c_223, plain, (![A_69, B_70]: (r1_xboole_0(k1_tarski(A_69), k1_tarski(B_70)) | B_70=A_69)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.28/1.34  tff(c_231, plain, (![A_69, B_70]: (~r2_hidden(A_69, k1_tarski(B_70)) | B_70=A_69)), inference(resolution, [status(thm)], [c_223, c_8])).
% 2.28/1.34  tff(c_278, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_275, c_231])).
% 2.28/1.34  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_278])).
% 2.28/1.34  tff(c_284, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_254])).
% 2.28/1.34  tff(c_304, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_32])).
% 2.28/1.34  tff(c_305, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_284, c_304])).
% 2.28/1.34  tff(c_283, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_254])).
% 2.28/1.34  tff(c_329, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_305, c_283, c_28])).
% 2.28/1.34  tff(c_330, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_284, c_329])).
% 2.28/1.34  tff(c_333, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_330])).
% 2.28/1.34  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_333])).
% 2.28/1.34  tff(c_339, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_213])).
% 2.28/1.34  tff(c_24, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.34  tff(c_349, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_339, c_24])).
% 2.28/1.34  tff(c_338, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_213])).
% 2.28/1.34  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.34  tff(c_406, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_339, c_349, c_338, c_22])).
% 2.28/1.34  tff(c_410, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_407, c_406])).
% 2.28/1.34  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_386, c_386, c_410])).
% 2.28/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.34  
% 2.28/1.34  Inference rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Ref     : 0
% 2.28/1.34  #Sup     : 79
% 2.28/1.34  #Fact    : 0
% 2.28/1.34  #Define  : 0
% 2.28/1.34  #Split   : 6
% 2.28/1.34  #Chain   : 0
% 2.28/1.34  #Close   : 0
% 2.28/1.34  
% 2.28/1.34  Ordering : KBO
% 2.28/1.34  
% 2.28/1.34  Simplification rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Subsume      : 5
% 2.28/1.34  #Demod        : 36
% 2.28/1.34  #Tautology    : 63
% 2.28/1.34  #SimpNegUnit  : 5
% 2.28/1.34  #BackRed      : 2
% 2.28/1.34  
% 2.28/1.34  #Partial instantiations: 0
% 2.28/1.34  #Strategies tried      : 1
% 2.28/1.34  
% 2.28/1.34  Timing (in seconds)
% 2.28/1.34  ----------------------
% 2.28/1.34  Preprocessing        : 0.30
% 2.28/1.34  Parsing              : 0.16
% 2.28/1.34  CNF conversion       : 0.02
% 2.28/1.34  Main loop            : 0.21
% 2.28/1.34  Inferencing          : 0.09
% 2.28/1.34  Reduction            : 0.06
% 2.28/1.34  Demodulation         : 0.04
% 2.28/1.35  BG Simplification    : 0.01
% 2.28/1.35  Subsumption          : 0.03
% 2.28/1.35  Abstraction          : 0.01
% 2.28/1.35  MUC search           : 0.00
% 2.28/1.35  Cooper               : 0.00
% 2.28/1.35  Total                : 0.54
% 2.28/1.35  Index Insertion      : 0.00
% 2.28/1.35  Index Deletion       : 0.00
% 2.28/1.35  Index Matching       : 0.00
% 2.28/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
