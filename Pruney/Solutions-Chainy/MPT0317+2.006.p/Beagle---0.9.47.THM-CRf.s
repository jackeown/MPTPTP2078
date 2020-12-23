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
% DateTime   : Thu Dec  3 09:54:00 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 129 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 232 expanded)
%              Number of equality atoms :   19 (  78 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_30,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_26,plain,(
    ! [A_11,C_13,B_12,D_14] :
      ( r2_hidden(A_11,C_13)
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_57,c_26])).

tff(c_64,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_60])).

tff(c_66,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_67])).

tff(c_73,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14))
      | ~ r2_hidden(B_12,D_14)
      | ~ r2_hidden(A_11,C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_131,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_34])).

tff(c_132,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_131])).

tff(c_135,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_132])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_4,c_135])).

tff(c_140,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_142,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_146,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_152,plain,(
    ! [B_45,D_46,A_47,C_48] :
      ( r2_hidden(B_45,D_46)
      | ~ r2_hidden(k4_tarski(A_47,B_45),k2_zfmisc_1(C_48,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_156,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_146,c_152])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_159,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_159])).

tff(c_165,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_172,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_38])).

tff(c_164,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_226,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_34])).

tff(c_227,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_226])).

tff(c_230,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_227])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_4,c_230])).

tff(c_236,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_141,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_242,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_32])).

tff(c_243,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_243])).

tff(c_250,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_277,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( r2_hidden(k4_tarski(A_83,B_84),k2_zfmisc_1(C_85,D_86))
      | ~ r2_hidden(B_84,D_86)
      | ~ r2_hidden(A_83,C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_235,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_262,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_236,c_235,c_28])).

tff(c_280,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_277,c_262])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_4,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:27:44 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.67  
% 2.62/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.67  %$ r2_hidden > k2_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 2.62/1.67  
% 2.62/1.67  %Foreground sorts:
% 2.62/1.67  
% 2.62/1.67  
% 2.62/1.67  %Background operators:
% 2.62/1.67  
% 2.62/1.67  
% 2.62/1.67  %Foreground operators:
% 2.62/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.62/1.67  tff('#skF_7', type, '#skF_7': $i).
% 2.62/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.67  tff('#skF_10', type, '#skF_10': $i).
% 2.62/1.67  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.67  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.67  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.67  tff('#skF_9', type, '#skF_9': $i).
% 2.62/1.67  tff('#skF_8', type, '#skF_8': $i).
% 2.62/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.67  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.67  
% 2.62/1.69  tff(f_53, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.62/1.69  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 2.62/1.69  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.62/1.69  tff(c_30, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.69  tff(c_55, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_30])).
% 2.62/1.69  tff(c_36, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.69  tff(c_57, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_36])).
% 2.62/1.69  tff(c_26, plain, (![A_11, C_13, B_12, D_14]: (r2_hidden(A_11, C_13) | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.62/1.69  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_57, c_26])).
% 2.62/1.69  tff(c_64, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_60])).
% 2.62/1.69  tff(c_66, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_36])).
% 2.62/1.69  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.69  tff(c_67, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_38])).
% 2.62/1.69  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_67])).
% 2.62/1.69  tff(c_73, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 2.62/1.69  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.69  tff(c_22, plain, (![A_11, B_12, C_13, D_14]: (r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)) | ~r2_hidden(B_12, D_14) | ~r2_hidden(A_11, C_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.62/1.69  tff(c_65, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.62/1.69  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.69  tff(c_131, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_34])).
% 2.62/1.69  tff(c_132, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_131])).
% 2.62/1.69  tff(c_135, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_132])).
% 2.62/1.69  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_4, c_135])).
% 2.62/1.69  tff(c_140, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.62/1.69  tff(c_142, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_140])).
% 2.62/1.69  tff(c_146, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_36])).
% 2.62/1.69  tff(c_152, plain, (![B_45, D_46, A_47, C_48]: (r2_hidden(B_45, D_46) | ~r2_hidden(k4_tarski(A_47, B_45), k2_zfmisc_1(C_48, D_46)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.62/1.69  tff(c_156, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_146, c_152])).
% 2.62/1.69  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.69  tff(c_159, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_156, c_2])).
% 2.62/1.69  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_159])).
% 2.62/1.69  tff(c_165, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_36])).
% 2.62/1.69  tff(c_172, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_165, c_38])).
% 2.62/1.69  tff(c_164, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.62/1.69  tff(c_226, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_34])).
% 2.62/1.69  tff(c_227, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_165, c_226])).
% 2.62/1.69  tff(c_230, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_227])).
% 2.62/1.69  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_4, c_230])).
% 2.62/1.69  tff(c_236, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_140])).
% 2.62/1.69  tff(c_141, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_30])).
% 2.62/1.69  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_5') | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.69  tff(c_242, plain, (r2_hidden('#skF_3', '#skF_5') | '#skF_10'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_32])).
% 2.62/1.69  tff(c_243, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_242])).
% 2.62/1.69  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_243])).
% 2.62/1.69  tff(c_250, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_242])).
% 2.62/1.69  tff(c_277, plain, (![A_83, B_84, C_85, D_86]: (r2_hidden(k4_tarski(A_83, B_84), k2_zfmisc_1(C_85, D_86)) | ~r2_hidden(B_84, D_86) | ~r2_hidden(A_83, C_85))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.62/1.69  tff(c_235, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_140])).
% 2.62/1.69  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.69  tff(c_262, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_236, c_235, c_28])).
% 2.62/1.69  tff(c_280, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_277, c_262])).
% 2.62/1.69  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_4, c_280])).
% 2.62/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.69  
% 2.62/1.69  Inference rules
% 2.62/1.69  ----------------------
% 2.62/1.69  #Ref     : 0
% 2.62/1.69  #Sup     : 46
% 2.62/1.69  #Fact    : 0
% 2.62/1.69  #Define  : 0
% 2.62/1.69  #Split   : 6
% 2.62/1.69  #Chain   : 0
% 2.62/1.69  #Close   : 0
% 2.62/1.69  
% 2.62/1.69  Ordering : KBO
% 2.62/1.69  
% 2.62/1.69  Simplification rules
% 2.62/1.69  ----------------------
% 2.62/1.69  #Subsume      : 9
% 2.62/1.69  #Demod        : 28
% 2.62/1.69  #Tautology    : 33
% 2.62/1.69  #SimpNegUnit  : 6
% 2.62/1.69  #BackRed      : 0
% 2.62/1.69  
% 2.62/1.69  #Partial instantiations: 0
% 2.62/1.69  #Strategies tried      : 1
% 2.62/1.69  
% 2.62/1.69  Timing (in seconds)
% 2.62/1.69  ----------------------
% 2.62/1.70  Preprocessing        : 0.45
% 2.62/1.70  Parsing              : 0.22
% 2.62/1.70  CNF conversion       : 0.04
% 2.62/1.70  Main loop            : 0.34
% 2.62/1.70  Inferencing          : 0.13
% 2.62/1.70  Reduction            : 0.10
% 2.62/1.70  Demodulation         : 0.06
% 2.62/1.70  BG Simplification    : 0.02
% 2.62/1.70  Subsumption          : 0.07
% 2.62/1.70  Abstraction          : 0.02
% 2.62/1.70  MUC search           : 0.00
% 2.62/1.70  Cooper               : 0.00
% 2.62/1.70  Total                : 0.85
% 2.62/1.70  Index Insertion      : 0.00
% 2.62/1.70  Index Deletion       : 0.00
% 2.62/1.70  Index Matching       : 0.00
% 2.62/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
