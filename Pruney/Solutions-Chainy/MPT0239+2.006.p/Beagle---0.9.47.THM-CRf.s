%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:53 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 148 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 276 expanded)
%              Number of equality atoms :   31 ( 159 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10))
      | ~ r2_hidden(B_8,D_10)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_43,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8,D_10] :
      ( r2_hidden(A_7,C_9)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_43,c_20])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_59,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_55])).

tff(c_61,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    '#skF_5' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_32])).

tff(c_60,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_60,c_28])).

tff(c_134,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_133])).

tff(c_137,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_134])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_137])).

tff(c_143,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_142,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_148,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_159,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_30])).

tff(c_160,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_18,plain,(
    ! [B_8,D_10,A_7,C_9] :
      ( r2_hidden(B_8,D_10)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_167,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_160,c_18])).

tff(c_173,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_173])).

tff(c_179,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_184,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_32])).

tff(c_185,plain,(
    '#skF_5' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_184])).

tff(c_178,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_253,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_185,c_178,c_28])).

tff(c_254,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_253])).

tff(c_257,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_254])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_257])).

tff(c_263,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_26,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_279,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_263,c_26])).

tff(c_262,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_321,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_263,c_279,c_262,c_22])).

tff(c_324,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_321])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  %$ r2_hidden > k6_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 1.99/1.25  
% 1.99/1.25  %Foreground sorts:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Background operators:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Foreground operators:
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.99/1.25  tff('#skF_7', type, '#skF_7': $i).
% 1.99/1.25  tff('#skF_10', type, '#skF_10': $i).
% 1.99/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.25  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.25  tff('#skF_9', type, '#skF_9': $i).
% 1.99/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.25  tff('#skF_8', type, '#skF_8': $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.25  
% 1.99/1.27  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.99/1.27  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.99/1.27  tff(f_47, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 1.99/1.27  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.27  tff(c_16, plain, (![A_7, B_8, C_9, D_10]: (r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)) | ~r2_hidden(B_8, D_10) | ~r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.27  tff(c_24, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.27  tff(c_34, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_24])).
% 1.99/1.27  tff(c_30, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.27  tff(c_43, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_30])).
% 1.99/1.27  tff(c_20, plain, (![A_7, C_9, B_8, D_10]: (r2_hidden(A_7, C_9) | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.27  tff(c_50, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_43, c_20])).
% 1.99/1.27  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.27  tff(c_55, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_50, c_2])).
% 1.99/1.27  tff(c_59, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_55])).
% 1.99/1.27  tff(c_61, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_30])).
% 1.99/1.27  tff(c_32, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.27  tff(c_75, plain, ('#skF_5'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_61, c_32])).
% 1.99/1.27  tff(c_60, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 1.99/1.27  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.27  tff(c_133, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_60, c_28])).
% 1.99/1.27  tff(c_134, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_61, c_133])).
% 1.99/1.27  tff(c_137, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_134])).
% 1.99/1.27  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_137])).
% 1.99/1.27  tff(c_143, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_24])).
% 1.99/1.27  tff(c_142, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 1.99/1.27  tff(c_148, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_142])).
% 1.99/1.27  tff(c_159, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_30])).
% 1.99/1.27  tff(c_160, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_159])).
% 1.99/1.27  tff(c_18, plain, (![B_8, D_10, A_7, C_9]: (r2_hidden(B_8, D_10) | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.27  tff(c_167, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_160, c_18])).
% 1.99/1.27  tff(c_173, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_167, c_2])).
% 1.99/1.27  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_173])).
% 1.99/1.27  tff(c_179, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_159])).
% 1.99/1.27  tff(c_184, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_32])).
% 1.99/1.27  tff(c_185, plain, ('#skF_5'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_179, c_184])).
% 1.99/1.27  tff(c_178, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_159])).
% 1.99/1.27  tff(c_253, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_185, c_178, c_28])).
% 1.99/1.27  tff(c_254, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_179, c_253])).
% 1.99/1.27  tff(c_257, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_254])).
% 1.99/1.27  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_257])).
% 1.99/1.27  tff(c_263, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_142])).
% 1.99/1.27  tff(c_26, plain, ('#skF_5'='#skF_3' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.27  tff(c_279, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_263, c_26])).
% 1.99/1.27  tff(c_262, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_142])).
% 1.99/1.27  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.27  tff(c_321, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_263, c_279, c_262, c_22])).
% 1.99/1.27  tff(c_324, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_321])).
% 1.99/1.27  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_324])).
% 1.99/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.27  
% 1.99/1.27  Inference rules
% 1.99/1.27  ----------------------
% 1.99/1.27  #Ref     : 0
% 1.99/1.27  #Sup     : 58
% 1.99/1.27  #Fact    : 0
% 1.99/1.27  #Define  : 0
% 1.99/1.27  #Split   : 5
% 1.99/1.27  #Chain   : 0
% 1.99/1.27  #Close   : 0
% 1.99/1.27  
% 1.99/1.27  Ordering : KBO
% 1.99/1.27  
% 1.99/1.27  Simplification rules
% 1.99/1.27  ----------------------
% 1.99/1.27  #Subsume      : 4
% 1.99/1.27  #Demod        : 40
% 1.99/1.27  #Tautology    : 46
% 1.99/1.27  #SimpNegUnit  : 6
% 1.99/1.27  #BackRed      : 0
% 1.99/1.27  
% 1.99/1.27  #Partial instantiations: 0
% 1.99/1.27  #Strategies tried      : 1
% 1.99/1.27  
% 1.99/1.27  Timing (in seconds)
% 1.99/1.27  ----------------------
% 1.99/1.27  Preprocessing        : 0.28
% 1.99/1.27  Parsing              : 0.14
% 1.99/1.27  CNF conversion       : 0.02
% 1.99/1.27  Main loop            : 0.22
% 1.99/1.27  Inferencing          : 0.08
% 1.99/1.27  Reduction            : 0.06
% 1.99/1.27  Demodulation         : 0.04
% 1.99/1.27  BG Simplification    : 0.01
% 1.99/1.27  Subsumption          : 0.04
% 1.99/1.27  Abstraction          : 0.01
% 1.99/1.27  MUC search           : 0.00
% 1.99/1.27  Cooper               : 0.00
% 1.99/1.27  Total                : 0.53
% 1.99/1.27  Index Insertion      : 0.00
% 1.99/1.27  Index Deletion       : 0.00
% 1.99/1.27  Index Matching       : 0.00
% 1.99/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
