%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:57 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 146 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 265 expanded)
%              Number of equality atoms :   17 (  94 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_28,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r2_hidden('#skF_10','#skF_12')
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_106,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_46,plain,(
    ! [A_16,C_18,B_17,D_19] :
      ( r2_hidden(A_16,C_18)
      | ~ r2_hidden(k4_tarski(A_16,B_17),k2_zfmisc_1(C_18,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_117,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_110,c_46])).

tff(c_26,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_117,c_26])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_121])).

tff(c_127,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_128])).

tff(c_134,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_570,plain,(
    ! [A_762,B_763,C_764,D_765] :
      ( r2_hidden(k4_tarski(A_762,B_763),k2_zfmisc_1(C_764,D_765))
      | ~ r2_hidden(B_763,D_765)
      | ~ r2_hidden(A_762,C_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_456,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_54])).

tff(c_457,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_456])).

tff(c_573,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_570,c_457])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_134,c_573])).

tff(c_590,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_589,plain,
    ( ~ r2_hidden('#skF_10','#skF_12')
    | '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_595,plain,(
    ~ r2_hidden('#skF_10','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_599,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_58])).

tff(c_600,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_599])).

tff(c_607,plain,(
    ! [B_792,D_793,A_794,C_795] :
      ( r2_hidden(B_792,D_793)
      | ~ r2_hidden(k4_tarski(A_794,B_792),k2_zfmisc_1(C_795,D_793)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_610,plain,(
    r2_hidden('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_600,c_607])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_610])).

tff(c_616,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(splitRight,[status(thm)],[c_599])).

tff(c_857,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_56])).

tff(c_858,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_857])).

tff(c_1001,plain,(
    ! [A_1483,B_1484,C_1485,D_1486] :
      ( r2_hidden(k4_tarski(A_1483,B_1484),k2_zfmisc_1(C_1485,D_1486))
      | ~ r2_hidden(B_1484,D_1486)
      | ~ r2_hidden(A_1483,C_1485) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_615,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_599])).

tff(c_918,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_615,c_54])).

tff(c_919,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_918])).

tff(c_1004,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1001,c_919])).

tff(c_1019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_858,c_1004])).

tff(c_1021,plain,(
    r2_hidden('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_50,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_12')
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1028,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_1021,c_50])).

tff(c_1449,plain,(
    ! [A_2176,B_2177,C_2178,D_2179] :
      ( r2_hidden(k4_tarski(A_2176,B_2177),k2_zfmisc_1(C_2178,D_2179))
      | ~ r2_hidden(B_2177,D_2179)
      | ~ r2_hidden(A_2176,C_2178) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1020,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))
    | ~ r2_hidden('#skF_10','#skF_12')
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1285,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_1021,c_1020,c_48])).

tff(c_1452,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1449,c_1285])).

tff(c_1464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1028,c_1452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:29:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.55  
% 3.19/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.55  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_12 > #skF_4
% 3.19/1.55  
% 3.19/1.55  %Foreground sorts:
% 3.19/1.55  
% 3.19/1.55  
% 3.19/1.55  %Background operators:
% 3.19/1.55  
% 3.19/1.55  
% 3.19/1.55  %Foreground operators:
% 3.19/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.55  tff('#skF_11', type, '#skF_11': $i).
% 3.19/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.19/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.19/1.55  tff('#skF_10', type, '#skF_10': $i).
% 3.19/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.19/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.55  tff('#skF_9', type, '#skF_9': $i).
% 3.19/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.19/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.19/1.55  tff('#skF_12', type, '#skF_12': $i).
% 3.19/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.19/1.55  
% 3.19/1.56  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.19/1.56  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.19/1.56  tff(f_57, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.19/1.56  tff(c_28, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.56  tff(c_52, plain, ('#skF_7'='#skF_5' | ~r2_hidden('#skF_10', '#skF_12') | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.56  tff(c_106, plain, ('#skF_11'!='#skF_9'), inference(splitLeft, [status(thm)], [c_52])).
% 3.19/1.56  tff(c_58, plain, ('#skF_7'='#skF_5' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.56  tff(c_110, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(splitLeft, [status(thm)], [c_58])).
% 3.19/1.56  tff(c_46, plain, (![A_16, C_18, B_17, D_19]: (r2_hidden(A_16, C_18) | ~r2_hidden(k4_tarski(A_16, B_17), k2_zfmisc_1(C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.56  tff(c_117, plain, (r2_hidden('#skF_9', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_110, c_46])).
% 3.19/1.56  tff(c_26, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.56  tff(c_121, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_117, c_26])).
% 3.19/1.56  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_121])).
% 3.19/1.56  tff(c_127, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(splitRight, [status(thm)], [c_58])).
% 3.19/1.56  tff(c_56, plain, (r2_hidden('#skF_6', '#skF_8') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.56  tff(c_128, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.19/1.56  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_128])).
% 3.19/1.56  tff(c_134, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 3.19/1.56  tff(c_570, plain, (![A_762, B_763, C_764, D_765]: (r2_hidden(k4_tarski(A_762, B_763), k2_zfmisc_1(C_764, D_765)) | ~r2_hidden(B_763, D_765) | ~r2_hidden(A_762, C_764))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.56  tff(c_126, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 3.19/1.56  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.56  tff(c_456, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_54])).
% 3.19/1.56  tff(c_457, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_127, c_456])).
% 3.19/1.56  tff(c_573, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_570, c_457])).
% 3.19/1.56  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_134, c_573])).
% 3.19/1.56  tff(c_590, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 3.19/1.56  tff(c_589, plain, (~r2_hidden('#skF_10', '#skF_12') | '#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 3.19/1.56  tff(c_595, plain, (~r2_hidden('#skF_10', '#skF_12')), inference(splitLeft, [status(thm)], [c_589])).
% 3.19/1.56  tff(c_599, plain, ('#skF_7'='#skF_5' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_58])).
% 3.19/1.56  tff(c_600, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(splitLeft, [status(thm)], [c_599])).
% 3.19/1.56  tff(c_607, plain, (![B_792, D_793, A_794, C_795]: (r2_hidden(B_792, D_793) | ~r2_hidden(k4_tarski(A_794, B_792), k2_zfmisc_1(C_795, D_793)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.56  tff(c_610, plain, (r2_hidden('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_600, c_607])).
% 3.19/1.56  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_610])).
% 3.19/1.56  tff(c_616, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(splitRight, [status(thm)], [c_599])).
% 3.19/1.56  tff(c_857, plain, (r2_hidden('#skF_6', '#skF_8') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_56])).
% 3.19/1.56  tff(c_858, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_616, c_857])).
% 3.19/1.56  tff(c_1001, plain, (![A_1483, B_1484, C_1485, D_1486]: (r2_hidden(k4_tarski(A_1483, B_1484), k2_zfmisc_1(C_1485, D_1486)) | ~r2_hidden(B_1484, D_1486) | ~r2_hidden(A_1483, C_1485))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.56  tff(c_615, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_599])).
% 3.19/1.56  tff(c_918, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_615, c_54])).
% 3.19/1.56  tff(c_919, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_616, c_918])).
% 3.19/1.56  tff(c_1004, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_1001, c_919])).
% 3.19/1.56  tff(c_1019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_858, c_1004])).
% 3.19/1.56  tff(c_1021, plain, (r2_hidden('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_589])).
% 3.19/1.56  tff(c_50, plain, (r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_10', '#skF_12') | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.56  tff(c_1028, plain, (r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_590, c_1021, c_50])).
% 3.19/1.56  tff(c_1449, plain, (![A_2176, B_2177, C_2178, D_2179]: (r2_hidden(k4_tarski(A_2176, B_2177), k2_zfmisc_1(C_2178, D_2179)) | ~r2_hidden(B_2177, D_2179) | ~r2_hidden(A_2176, C_2178))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.56  tff(c_1020, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_589])).
% 3.19/1.56  tff(c_48, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')) | ~r2_hidden('#skF_10', '#skF_12') | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.56  tff(c_1285, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_1021, c_1020, c_48])).
% 3.19/1.56  tff(c_1452, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_1449, c_1285])).
% 3.19/1.56  tff(c_1464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1028, c_1452])).
% 3.19/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.56  
% 3.19/1.56  Inference rules
% 3.19/1.56  ----------------------
% 3.19/1.56  #Ref     : 0
% 3.19/1.56  #Sup     : 190
% 3.19/1.56  #Fact    : 0
% 3.19/1.56  #Define  : 0
% 3.19/1.56  #Split   : 6
% 3.19/1.56  #Chain   : 0
% 3.19/1.56  #Close   : 0
% 3.19/1.56  
% 3.19/1.56  Ordering : KBO
% 3.19/1.56  
% 3.19/1.56  Simplification rules
% 3.19/1.56  ----------------------
% 3.19/1.56  #Subsume      : 14
% 3.19/1.56  #Demod        : 77
% 3.19/1.56  #Tautology    : 44
% 3.19/1.56  #SimpNegUnit  : 6
% 3.19/1.56  #BackRed      : 0
% 3.19/1.56  
% 3.19/1.56  #Partial instantiations: 1564
% 3.19/1.56  #Strategies tried      : 1
% 3.19/1.56  
% 3.19/1.56  Timing (in seconds)
% 3.19/1.56  ----------------------
% 3.19/1.56  Preprocessing        : 0.31
% 3.19/1.57  Parsing              : 0.16
% 3.19/1.57  CNF conversion       : 0.03
% 3.19/1.57  Main loop            : 0.43
% 3.19/1.57  Inferencing          : 0.22
% 3.19/1.57  Reduction            : 0.10
% 3.19/1.57  Demodulation         : 0.07
% 3.19/1.57  BG Simplification    : 0.03
% 3.19/1.57  Subsumption          : 0.06
% 3.19/1.57  Abstraction          : 0.02
% 3.19/1.57  MUC search           : 0.00
% 3.19/1.57  Cooper               : 0.00
% 3.19/1.57  Total                : 0.77
% 3.19/1.57  Index Insertion      : 0.00
% 3.19/1.57  Index Deletion       : 0.00
% 3.19/1.57  Index Matching       : 0.00
% 3.19/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
