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
% DateTime   : Thu Dec  3 09:53:58 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 144 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 258 expanded)
%              Number of equality atoms :   17 (  93 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_79,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_84,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r2_hidden(A_44,C_45)
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1(C_45,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_79,c_84])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_91])).

tff(c_97,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_40])).

tff(c_26,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( r2_hidden(k4_tarski(A_27,B_28),k2_zfmisc_1(C_29,D_30))
      | ~ r2_hidden(B_28,D_30)
      | ~ r2_hidden(A_27,C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_38,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_174,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_38])).

tff(c_175,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_174])).

tff(c_178,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_175])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_104,c_178])).

tff(c_184,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_183,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_189,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_211,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_42])).

tff(c_212,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_219,plain,(
    ! [B_84,D_85,A_86,C_87] :
      ( r2_hidden(B_84,D_85)
      | ~ r2_hidden(k4_tarski(A_86,B_84),k2_zfmisc_1(C_87,D_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_222,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_212,c_219])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_222])).

tff(c_228,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_235,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_40])).

tff(c_236,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_235])).

tff(c_227,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_317,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_227,c_38])).

tff(c_318,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_317])).

tff(c_321,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_318])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_236,c_321])).

tff(c_327,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_34,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_342,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_327,c_34])).

tff(c_390,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( r2_hidden(k4_tarski(A_151,B_152),k2_zfmisc_1(C_153,D_154))
      | ~ r2_hidden(B_152,D_154)
      | ~ r2_hidden(A_151,C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_326,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_32,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_374,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_327,c_326,c_32])).

tff(c_393,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_390,c_374])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_342,c_393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:21:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 2.18/1.26  
% 2.18/1.26  %Foreground sorts:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Background operators:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Foreground operators:
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.26  tff('#skF_10', type, '#skF_10': $i).
% 2.18/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.26  tff('#skF_9', type, '#skF_9': $i).
% 2.18/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.18/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.26  
% 2.18/1.27  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.18/1.27  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.18/1.27  tff(f_50, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.18/1.27  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.27  tff(c_36, plain, ('#skF_5'='#skF_3' | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_59, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_36])).
% 2.18/1.27  tff(c_42, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_79, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.18/1.27  tff(c_84, plain, (![A_44, C_45, B_46, D_47]: (r2_hidden(A_44, C_45) | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1(C_45, D_47)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.27  tff(c_88, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_79, c_84])).
% 2.18/1.27  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.27  tff(c_91, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_88, c_2])).
% 2.18/1.27  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_91])).
% 2.18/1.27  tff(c_97, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_42])).
% 2.18/1.27  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_104, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_97, c_40])).
% 2.18/1.27  tff(c_26, plain, (![A_27, B_28, C_29, D_30]: (r2_hidden(k4_tarski(A_27, B_28), k2_zfmisc_1(C_29, D_30)) | ~r2_hidden(B_28, D_30) | ~r2_hidden(A_27, C_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.27  tff(c_96, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 2.18/1.27  tff(c_38, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_174, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_38])).
% 2.18/1.27  tff(c_175, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_97, c_174])).
% 2.18/1.27  tff(c_178, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_175])).
% 2.18/1.27  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_104, c_178])).
% 2.18/1.27  tff(c_184, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_36])).
% 2.18/1.27  tff(c_183, plain, (~r2_hidden('#skF_8', '#skF_10') | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.18/1.27  tff(c_189, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_183])).
% 2.18/1.27  tff(c_211, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_42])).
% 2.18/1.27  tff(c_212, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_211])).
% 2.18/1.27  tff(c_219, plain, (![B_84, D_85, A_86, C_87]: (r2_hidden(B_84, D_85) | ~r2_hidden(k4_tarski(A_86, B_84), k2_zfmisc_1(C_87, D_85)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.27  tff(c_222, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_212, c_219])).
% 2.18/1.27  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_222])).
% 2.18/1.27  tff(c_228, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_211])).
% 2.18/1.27  tff(c_235, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_40])).
% 2.18/1.27  tff(c_236, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_228, c_235])).
% 2.18/1.27  tff(c_227, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_211])).
% 2.18/1.27  tff(c_317, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_227, c_38])).
% 2.18/1.27  tff(c_318, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_228, c_317])).
% 2.18/1.27  tff(c_321, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_318])).
% 2.18/1.27  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_236, c_321])).
% 2.18/1.27  tff(c_327, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_183])).
% 2.18/1.27  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_342, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_327, c_34])).
% 2.18/1.27  tff(c_390, plain, (![A_151, B_152, C_153, D_154]: (r2_hidden(k4_tarski(A_151, B_152), k2_zfmisc_1(C_153, D_154)) | ~r2_hidden(B_152, D_154) | ~r2_hidden(A_151, C_153))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.27  tff(c_326, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_183])).
% 2.18/1.27  tff(c_32, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_374, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_327, c_326, c_32])).
% 2.18/1.27  tff(c_393, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_390, c_374])).
% 2.18/1.27  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_342, c_393])).
% 2.18/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  Inference rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Ref     : 0
% 2.18/1.27  #Sup     : 69
% 2.18/1.27  #Fact    : 0
% 2.18/1.27  #Define  : 0
% 2.18/1.27  #Split   : 5
% 2.18/1.27  #Chain   : 0
% 2.18/1.27  #Close   : 0
% 2.18/1.27  
% 2.18/1.27  Ordering : KBO
% 2.18/1.27  
% 2.18/1.27  Simplification rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Subsume      : 5
% 2.18/1.27  #Demod        : 32
% 2.18/1.27  #Tautology    : 55
% 2.18/1.27  #SimpNegUnit  : 6
% 2.18/1.27  #BackRed      : 0
% 2.18/1.27  
% 2.18/1.27  #Partial instantiations: 0
% 2.18/1.27  #Strategies tried      : 1
% 2.18/1.27  
% 2.18/1.27  Timing (in seconds)
% 2.18/1.27  ----------------------
% 2.18/1.28  Preprocessing        : 0.30
% 2.18/1.28  Parsing              : 0.16
% 2.18/1.28  CNF conversion       : 0.02
% 2.18/1.28  Main loop            : 0.23
% 2.18/1.28  Inferencing          : 0.10
% 2.18/1.28  Reduction            : 0.06
% 2.18/1.28  Demodulation         : 0.04
% 2.18/1.28  BG Simplification    : 0.02
% 2.18/1.28  Subsumption          : 0.04
% 2.18/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.56
% 2.18/1.28  Index Insertion      : 0.00
% 2.18/1.28  Index Deletion       : 0.00
% 2.18/1.28  Index Matching       : 0.00
% 2.18/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
