%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:57 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 149 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 274 expanded)
%              Number of equality atoms :   17 (  98 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r2_hidden('#skF_10','#skF_12')
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_98,plain,(
    ! [A_32,C_33,B_34,D_35] :
      ( r2_hidden(A_32,C_33)
      | ~ r2_hidden(k4_tarski(A_32,B_34),k2_zfmisc_1(C_33,D_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_92,c_98])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_105])).

tff(c_111,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_118,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_48])).

tff(c_34,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16))
      | ~ r2_hidden(B_14,D_16)
      | ~ r2_hidden(A_13,C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_46,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_181,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_46])).

tff(c_182,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_181])).

tff(c_185,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_118,c_185])).

tff(c_191,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_190,plain,
    ( ~ r2_hidden('#skF_10','#skF_12')
    | '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_196,plain,(
    ~ r2_hidden('#skF_10','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_214,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_50])).

tff(c_215,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_36,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_218,plain,(
    r2_hidden('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_215,c_36])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_218])).

tff(c_224,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_229,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_48])).

tff(c_230,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_230])).

tff(c_232,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_223,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_301,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_223,c_46])).

tff(c_302,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_301])).

tff(c_305,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_302])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_232,c_305])).

tff(c_311,plain,(
    r2_hidden('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_42,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_12')
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_317,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_311,c_42])).

tff(c_351,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( r2_hidden(k4_tarski(A_106,B_107),k2_zfmisc_1(C_108,D_109))
      | ~ r2_hidden(B_107,D_109)
      | ~ r2_hidden(A_106,C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_310,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_40,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))
    | ~ r2_hidden('#skF_10','#skF_12')
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_350,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_311,c_310,c_40])).

tff(c_354,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_351,c_350])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_317,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:21:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.32  
% 2.30/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.32  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 2.30/1.32  
% 2.30/1.32  %Foreground sorts:
% 2.30/1.32  
% 2.30/1.32  
% 2.30/1.32  %Background operators:
% 2.30/1.32  
% 2.30/1.32  
% 2.30/1.32  %Foreground operators:
% 2.30/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.32  tff('#skF_11', type, '#skF_11': $i).
% 2.30/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.30/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.30/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.30/1.32  tff('#skF_10', type, '#skF_10': $i).
% 2.30/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.32  tff('#skF_9', type, '#skF_9': $i).
% 2.30/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.30/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.30/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.32  tff('#skF_12', type, '#skF_12': $i).
% 2.30/1.32  
% 2.30/1.34  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.30/1.34  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.30/1.34  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.30/1.34  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.30/1.34  tff(c_44, plain, ('#skF_7'='#skF_5' | ~r2_hidden('#skF_10', '#skF_12') | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.34  tff(c_77, plain, ('#skF_11'!='#skF_9'), inference(splitLeft, [status(thm)], [c_44])).
% 2.30/1.34  tff(c_50, plain, ('#skF_7'='#skF_5' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.34  tff(c_92, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.30/1.34  tff(c_98, plain, (![A_32, C_33, B_34, D_35]: (r2_hidden(A_32, C_33) | ~r2_hidden(k4_tarski(A_32, B_34), k2_zfmisc_1(C_33, D_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.30/1.34  tff(c_102, plain, (r2_hidden('#skF_9', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_92, c_98])).
% 2.30/1.34  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.30/1.34  tff(c_105, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_102, c_2])).
% 2.30/1.34  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_105])).
% 2.30/1.34  tff(c_111, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(splitRight, [status(thm)], [c_50])).
% 2.30/1.34  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_8') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.34  tff(c_118, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_111, c_48])).
% 2.30/1.34  tff(c_34, plain, (![A_13, B_14, C_15, D_16]: (r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)) | ~r2_hidden(B_14, D_16) | ~r2_hidden(A_13, C_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.30/1.34  tff(c_110, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 2.30/1.34  tff(c_46, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.34  tff(c_181, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_46])).
% 2.30/1.34  tff(c_182, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_111, c_181])).
% 2.30/1.34  tff(c_185, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_182])).
% 2.30/1.34  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_118, c_185])).
% 2.30/1.34  tff(c_191, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_44])).
% 2.30/1.34  tff(c_190, plain, (~r2_hidden('#skF_10', '#skF_12') | '#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 2.30/1.34  tff(c_196, plain, (~r2_hidden('#skF_10', '#skF_12')), inference(splitLeft, [status(thm)], [c_190])).
% 2.30/1.34  tff(c_214, plain, ('#skF_7'='#skF_5' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_50])).
% 2.30/1.34  tff(c_215, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(splitLeft, [status(thm)], [c_214])).
% 2.30/1.34  tff(c_36, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.30/1.34  tff(c_218, plain, (r2_hidden('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_215, c_36])).
% 2.30/1.34  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_218])).
% 2.30/1.34  tff(c_224, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(splitRight, [status(thm)], [c_214])).
% 2.30/1.34  tff(c_229, plain, (r2_hidden('#skF_6', '#skF_8') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_48])).
% 2.30/1.34  tff(c_230, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(splitLeft, [status(thm)], [c_229])).
% 2.30/1.34  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_230])).
% 2.30/1.34  tff(c_232, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_229])).
% 2.30/1.34  tff(c_223, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_214])).
% 2.30/1.34  tff(c_301, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_223, c_46])).
% 2.30/1.34  tff(c_302, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_224, c_301])).
% 2.30/1.34  tff(c_305, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_302])).
% 2.30/1.34  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_232, c_305])).
% 2.30/1.34  tff(c_311, plain, (r2_hidden('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_190])).
% 2.30/1.34  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_10', '#skF_12') | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.34  tff(c_317, plain, (r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_311, c_42])).
% 2.30/1.34  tff(c_351, plain, (![A_106, B_107, C_108, D_109]: (r2_hidden(k4_tarski(A_106, B_107), k2_zfmisc_1(C_108, D_109)) | ~r2_hidden(B_107, D_109) | ~r2_hidden(A_106, C_108))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.30/1.34  tff(c_310, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_190])).
% 2.30/1.34  tff(c_40, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')) | ~r2_hidden('#skF_10', '#skF_12') | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.34  tff(c_350, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_311, c_310, c_40])).
% 2.30/1.34  tff(c_354, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_351, c_350])).
% 2.30/1.34  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_317, c_354])).
% 2.30/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.34  
% 2.30/1.34  Inference rules
% 2.30/1.34  ----------------------
% 2.30/1.34  #Ref     : 0
% 2.30/1.34  #Sup     : 57
% 2.30/1.34  #Fact    : 0
% 2.30/1.34  #Define  : 0
% 2.30/1.34  #Split   : 6
% 2.30/1.34  #Chain   : 0
% 2.30/1.34  #Close   : 0
% 2.30/1.34  
% 2.30/1.34  Ordering : KBO
% 2.30/1.34  
% 2.30/1.34  Simplification rules
% 2.30/1.34  ----------------------
% 2.30/1.34  #Subsume      : 9
% 2.30/1.34  #Demod        : 31
% 2.30/1.34  #Tautology    : 35
% 2.30/1.34  #SimpNegUnit  : 6
% 2.30/1.34  #BackRed      : 0
% 2.30/1.34  
% 2.30/1.34  #Partial instantiations: 0
% 2.30/1.34  #Strategies tried      : 1
% 2.30/1.34  
% 2.30/1.34  Timing (in seconds)
% 2.30/1.34  ----------------------
% 2.30/1.34  Preprocessing        : 0.31
% 2.30/1.34  Parsing              : 0.16
% 2.30/1.34  CNF conversion       : 0.02
% 2.30/1.34  Main loop            : 0.24
% 2.30/1.34  Inferencing          : 0.09
% 2.30/1.34  Reduction            : 0.07
% 2.30/1.34  Demodulation         : 0.05
% 2.30/1.34  BG Simplification    : 0.02
% 2.30/1.34  Subsumption          : 0.05
% 2.30/1.34  Abstraction          : 0.01
% 2.30/1.34  MUC search           : 0.00
% 2.30/1.34  Cooper               : 0.00
% 2.30/1.34  Total                : 0.59
% 2.30/1.34  Index Insertion      : 0.00
% 2.30/1.34  Index Deletion       : 0.00
% 2.30/1.34  Index Matching       : 0.00
% 2.30/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
