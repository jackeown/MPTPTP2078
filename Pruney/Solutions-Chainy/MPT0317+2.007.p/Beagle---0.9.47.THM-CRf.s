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
% DateTime   : Thu Dec  3 09:54:00 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 129 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :   77 ( 232 expanded)
%              Number of equality atoms :   19 (  78 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_24,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_49,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8,D_10] :
      ( r2_hidden(A_7,C_9)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_51,c_20])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_54])).

tff(c_60,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_61])).

tff(c_67,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10))
      | ~ r2_hidden(B_8,D_10)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_125,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_28])).

tff(c_126,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_125])).

tff(c_129,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_4,c_129])).

tff(c_134,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_136,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_140,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_146,plain,(
    ! [B_41,D_42,A_43,C_44] :
      ( r2_hidden(B_41,D_42)
      | ~ r2_hidden(k4_tarski(A_43,B_41),k2_zfmisc_1(C_44,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_150,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_140,c_146])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_153,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_153])).

tff(c_159,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_165,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_32])).

tff(c_158,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_220,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_28])).

tff(c_221,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_220])).

tff(c_224,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_221])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_4,c_224])).

tff(c_230,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_135,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_236,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_26])).

tff(c_237,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_237])).

tff(c_244,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_229,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_279,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_230,c_229,c_22])).

tff(c_282,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_279])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_4,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.21  
% 1.90/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.21  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 1.90/1.21  
% 1.90/1.21  %Foreground sorts:
% 1.90/1.21  
% 1.90/1.21  
% 1.90/1.21  %Background operators:
% 1.90/1.21  
% 1.90/1.21  
% 1.90/1.21  %Foreground operators:
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.90/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.90/1.21  tff('#skF_10', type, '#skF_10': $i).
% 1.90/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.90/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.21  tff('#skF_9', type, '#skF_9': $i).
% 1.90/1.21  tff('#skF_8', type, '#skF_8': $i).
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.21  
% 1.90/1.22  tff(f_47, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 1.90/1.22  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.90/1.22  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.90/1.22  tff(c_24, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.22  tff(c_49, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_24])).
% 1.90/1.22  tff(c_30, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.22  tff(c_51, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_30])).
% 1.90/1.22  tff(c_20, plain, (![A_7, C_9, B_8, D_10]: (r2_hidden(A_7, C_9) | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.22  tff(c_54, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_51, c_20])).
% 1.90/1.22  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_54])).
% 1.90/1.22  tff(c_60, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_30])).
% 1.90/1.22  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.22  tff(c_61, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_32])).
% 1.90/1.22  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_61])).
% 1.90/1.22  tff(c_67, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 1.90/1.22  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.22  tff(c_16, plain, (![A_7, B_8, C_9, D_10]: (r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)) | ~r2_hidden(B_8, D_10) | ~r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.22  tff(c_59, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 1.90/1.22  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.22  tff(c_125, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_28])).
% 1.90/1.22  tff(c_126, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_125])).
% 1.90/1.22  tff(c_129, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_126])).
% 1.90/1.22  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_4, c_129])).
% 1.90/1.22  tff(c_134, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 1.90/1.22  tff(c_136, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_134])).
% 1.90/1.22  tff(c_140, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_30])).
% 1.90/1.22  tff(c_146, plain, (![B_41, D_42, A_43, C_44]: (r2_hidden(B_41, D_42) | ~r2_hidden(k4_tarski(A_43, B_41), k2_zfmisc_1(C_44, D_42)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.22  tff(c_150, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_140, c_146])).
% 1.90/1.22  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.22  tff(c_153, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_150, c_2])).
% 1.90/1.22  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_153])).
% 1.90/1.22  tff(c_159, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_30])).
% 1.90/1.22  tff(c_165, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_159, c_32])).
% 1.90/1.22  tff(c_158, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 1.90/1.22  tff(c_220, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_28])).
% 1.90/1.22  tff(c_221, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_159, c_220])).
% 1.90/1.22  tff(c_224, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_221])).
% 1.90/1.22  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_4, c_224])).
% 1.90/1.22  tff(c_230, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_134])).
% 1.90/1.22  tff(c_135, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_24])).
% 1.90/1.22  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_5') | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.22  tff(c_236, plain, (r2_hidden('#skF_3', '#skF_5') | '#skF_10'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_26])).
% 1.90/1.22  tff(c_237, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_236])).
% 1.90/1.22  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_237])).
% 1.90/1.22  tff(c_244, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_236])).
% 1.90/1.22  tff(c_229, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_134])).
% 1.90/1.22  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.22  tff(c_279, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_230, c_229, c_22])).
% 1.90/1.22  tff(c_282, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_279])).
% 1.90/1.22  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_244, c_4, c_282])).
% 1.90/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.22  
% 1.90/1.22  Inference rules
% 1.90/1.22  ----------------------
% 1.90/1.22  #Ref     : 0
% 1.90/1.22  #Sup     : 46
% 1.90/1.22  #Fact    : 0
% 1.90/1.22  #Define  : 0
% 1.90/1.22  #Split   : 6
% 1.90/1.22  #Chain   : 0
% 1.90/1.22  #Close   : 0
% 1.90/1.22  
% 1.90/1.22  Ordering : KBO
% 1.90/1.22  
% 1.90/1.22  Simplification rules
% 1.90/1.22  ----------------------
% 1.90/1.22  #Subsume      : 6
% 1.90/1.22  #Demod        : 28
% 1.90/1.22  #Tautology    : 35
% 1.90/1.22  #SimpNegUnit  : 6
% 1.90/1.22  #BackRed      : 0
% 1.90/1.22  
% 1.90/1.22  #Partial instantiations: 0
% 1.90/1.22  #Strategies tried      : 1
% 1.90/1.22  
% 1.90/1.22  Timing (in seconds)
% 1.90/1.22  ----------------------
% 1.90/1.23  Preprocessing        : 0.28
% 1.90/1.23  Parsing              : 0.14
% 1.90/1.23  CNF conversion       : 0.02
% 1.90/1.23  Main loop            : 0.20
% 1.90/1.23  Inferencing          : 0.08
% 1.90/1.23  Reduction            : 0.06
% 1.90/1.23  Demodulation         : 0.03
% 1.90/1.23  BG Simplification    : 0.01
% 1.90/1.23  Subsumption          : 0.04
% 1.90/1.23  Abstraction          : 0.01
% 1.90/1.23  MUC search           : 0.00
% 1.90/1.23  Cooper               : 0.00
% 1.90/1.23  Total                : 0.51
% 1.90/1.23  Index Insertion      : 0.00
% 1.90/1.23  Index Deletion       : 0.00
% 1.90/1.23  Index Matching       : 0.00
% 1.90/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
