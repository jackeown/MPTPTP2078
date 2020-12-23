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
% DateTime   : Thu Dec  3 09:54:01 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 149 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :    6
%              Number of atoms          :   92 ( 246 expanded)
%              Number of equality atoms :   31 ( 102 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_40,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_36,plain,(
    ! [A_28,C_30,B_29,D_31] :
      ( r2_hidden(A_28,C_30)
      | ~ r2_hidden(k4_tarski(A_28,B_29),k2_zfmisc_1(C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_125,c_36])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_128])).

tff(c_134,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_139,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_48])).

tff(c_61,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [A_27] : k1_enumset1(A_27,A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,(
    ! [B_39] : k2_tarski(B_39,B_39) = k1_tarski(B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_30])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [B_39] : r2_hidden(B_39,k1_tarski(B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_4])).

tff(c_32,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( r2_hidden(k4_tarski(A_28,B_29),k2_zfmisc_1(C_30,D_31))
      | ~ r2_hidden(B_29,D_31)
      | ~ r2_hidden(A_28,C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_133,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_185,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_44])).

tff(c_186,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_185])).

tff(c_189,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_83,c_189])).

tff(c_195,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_194,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_196,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_233,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_269,plain,(
    ! [B_101,D_102,A_103,C_104] :
      ( r2_hidden(B_101,D_102)
      | ~ r2_hidden(k4_tarski(A_103,B_101),k2_zfmisc_1(C_104,D_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_273,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_233,c_269])).

tff(c_197,plain,(
    ! [A_85,B_86] : k1_enumset1(A_85,A_85,B_86) = k2_tarski(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_204,plain,(
    ! [B_86] : k2_tarski(B_86,B_86) = k1_tarski(B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_30])).

tff(c_234,plain,(
    ! [D_89,B_90,A_91] :
      ( D_89 = B_90
      | D_89 = A_91
      | ~ r2_hidden(D_89,k2_tarski(A_91,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_237,plain,(
    ! [D_89,B_86] :
      ( D_89 = B_86
      | D_89 = B_86
      | ~ r2_hidden(D_89,k1_tarski(B_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_234])).

tff(c_276,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_273,c_237])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_196,c_276])).

tff(c_282,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_287,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_48])).

tff(c_213,plain,(
    ! [B_87] : k2_tarski(B_87,B_87) = k1_tarski(B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_30])).

tff(c_219,plain,(
    ! [B_87] : r2_hidden(B_87,k1_tarski(B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_4])).

tff(c_281,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_345,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_44])).

tff(c_346,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_345])).

tff(c_349,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_346])).

tff(c_353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_219,c_349])).

tff(c_355,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_42,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_397,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_355,c_42])).

tff(c_364,plain,(
    ! [A_129,B_130] : k1_enumset1(A_129,A_129,B_130) = k2_tarski(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_380,plain,(
    ! [B_131] : k2_tarski(B_131,B_131) = k1_tarski(B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_30])).

tff(c_386,plain,(
    ! [B_131] : r2_hidden(B_131,k1_tarski(B_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_4])).

tff(c_453,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( r2_hidden(k4_tarski(A_158,B_159),k2_zfmisc_1(C_160,D_161))
      | ~ r2_hidden(B_159,D_161)
      | ~ r2_hidden(A_158,C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_354,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_38,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_443,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_355,c_354,c_38])).

tff(c_456,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_453,c_443])).

tff(c_466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_386,c_456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.35  
% 2.23/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.35  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.23/1.35  
% 2.23/1.35  %Foreground sorts:
% 2.23/1.35  
% 2.23/1.35  
% 2.23/1.35  %Background operators:
% 2.23/1.35  
% 2.23/1.35  
% 2.23/1.35  %Foreground operators:
% 2.23/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.35  tff('#skF_10', type, '#skF_10': $i).
% 2.23/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.23/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.23/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.23/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.35  
% 2.23/1.37  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.23/1.37  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.23/1.37  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.23/1.37  tff(f_46, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 2.23/1.37  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.23/1.37  tff(c_40, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.37  tff(c_60, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_40])).
% 2.23/1.37  tff(c_46, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.37  tff(c_125, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_46])).
% 2.23/1.37  tff(c_36, plain, (![A_28, C_30, B_29, D_31]: (r2_hidden(A_28, C_30) | ~r2_hidden(k4_tarski(A_28, B_29), k2_zfmisc_1(C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.37  tff(c_128, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_125, c_36])).
% 2.23/1.37  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_128])).
% 2.23/1.37  tff(c_134, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_46])).
% 2.23/1.37  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.37  tff(c_139, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_134, c_48])).
% 2.23/1.37  tff(c_61, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.37  tff(c_30, plain, (![A_27]: (k1_enumset1(A_27, A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.37  tff(c_77, plain, (![B_39]: (k2_tarski(B_39, B_39)=k1_tarski(B_39))), inference(superposition, [status(thm), theory('equality')], [c_61, c_30])).
% 2.23/1.37  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.37  tff(c_83, plain, (![B_39]: (r2_hidden(B_39, k1_tarski(B_39)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_4])).
% 2.23/1.37  tff(c_32, plain, (![A_28, B_29, C_30, D_31]: (r2_hidden(k4_tarski(A_28, B_29), k2_zfmisc_1(C_30, D_31)) | ~r2_hidden(B_29, D_31) | ~r2_hidden(A_28, C_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.37  tff(c_133, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.23/1.37  tff(c_44, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.37  tff(c_185, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_44])).
% 2.23/1.37  tff(c_186, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_134, c_185])).
% 2.23/1.37  tff(c_189, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_186])).
% 2.23/1.37  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_83, c_189])).
% 2.23/1.37  tff(c_195, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_40])).
% 2.23/1.37  tff(c_194, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.23/1.37  tff(c_196, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_194])).
% 2.23/1.37  tff(c_233, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_46])).
% 2.23/1.37  tff(c_269, plain, (![B_101, D_102, A_103, C_104]: (r2_hidden(B_101, D_102) | ~r2_hidden(k4_tarski(A_103, B_101), k2_zfmisc_1(C_104, D_102)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.37  tff(c_273, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_233, c_269])).
% 2.23/1.37  tff(c_197, plain, (![A_85, B_86]: (k1_enumset1(A_85, A_85, B_86)=k2_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.37  tff(c_204, plain, (![B_86]: (k2_tarski(B_86, B_86)=k1_tarski(B_86))), inference(superposition, [status(thm), theory('equality')], [c_197, c_30])).
% 2.23/1.37  tff(c_234, plain, (![D_89, B_90, A_91]: (D_89=B_90 | D_89=A_91 | ~r2_hidden(D_89, k2_tarski(A_91, B_90)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.37  tff(c_237, plain, (![D_89, B_86]: (D_89=B_86 | D_89=B_86 | ~r2_hidden(D_89, k1_tarski(B_86)))), inference(superposition, [status(thm), theory('equality')], [c_204, c_234])).
% 2.23/1.37  tff(c_276, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_273, c_237])).
% 2.23/1.37  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_196, c_276])).
% 2.23/1.37  tff(c_282, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_46])).
% 2.23/1.37  tff(c_287, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_282, c_48])).
% 2.23/1.37  tff(c_213, plain, (![B_87]: (k2_tarski(B_87, B_87)=k1_tarski(B_87))), inference(superposition, [status(thm), theory('equality')], [c_197, c_30])).
% 2.23/1.37  tff(c_219, plain, (![B_87]: (r2_hidden(B_87, k1_tarski(B_87)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_4])).
% 2.23/1.37  tff(c_281, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.23/1.37  tff(c_345, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_44])).
% 2.23/1.37  tff(c_346, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_282, c_345])).
% 2.23/1.37  tff(c_349, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_346])).
% 2.23/1.37  tff(c_353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_287, c_219, c_349])).
% 2.23/1.37  tff(c_355, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_194])).
% 2.23/1.37  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_5') | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.37  tff(c_397, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_355, c_42])).
% 2.23/1.37  tff(c_364, plain, (![A_129, B_130]: (k1_enumset1(A_129, A_129, B_130)=k2_tarski(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.37  tff(c_380, plain, (![B_131]: (k2_tarski(B_131, B_131)=k1_tarski(B_131))), inference(superposition, [status(thm), theory('equality')], [c_364, c_30])).
% 2.23/1.37  tff(c_386, plain, (![B_131]: (r2_hidden(B_131, k1_tarski(B_131)))), inference(superposition, [status(thm), theory('equality')], [c_380, c_4])).
% 2.23/1.37  tff(c_453, plain, (![A_158, B_159, C_160, D_161]: (r2_hidden(k4_tarski(A_158, B_159), k2_zfmisc_1(C_160, D_161)) | ~r2_hidden(B_159, D_161) | ~r2_hidden(A_158, C_160))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.37  tff(c_354, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_194])).
% 2.23/1.37  tff(c_38, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.37  tff(c_443, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_355, c_354, c_38])).
% 2.23/1.37  tff(c_456, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_453, c_443])).
% 2.23/1.37  tff(c_466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_397, c_386, c_456])).
% 2.23/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.37  
% 2.23/1.37  Inference rules
% 2.23/1.37  ----------------------
% 2.23/1.37  #Ref     : 0
% 2.23/1.37  #Sup     : 85
% 2.23/1.37  #Fact    : 0
% 2.23/1.37  #Define  : 0
% 2.23/1.37  #Split   : 4
% 2.23/1.37  #Chain   : 0
% 2.23/1.37  #Close   : 0
% 2.23/1.37  
% 2.23/1.37  Ordering : KBO
% 2.23/1.37  
% 2.23/1.37  Simplification rules
% 2.23/1.37  ----------------------
% 2.23/1.37  #Subsume      : 5
% 2.23/1.37  #Demod        : 29
% 2.23/1.37  #Tautology    : 67
% 2.23/1.37  #SimpNegUnit  : 6
% 2.23/1.37  #BackRed      : 0
% 2.23/1.37  
% 2.23/1.37  #Partial instantiations: 0
% 2.23/1.37  #Strategies tried      : 1
% 2.23/1.37  
% 2.23/1.37  Timing (in seconds)
% 2.23/1.37  ----------------------
% 2.23/1.37  Preprocessing        : 0.33
% 2.23/1.37  Parsing              : 0.16
% 2.23/1.37  CNF conversion       : 0.03
% 2.23/1.37  Main loop            : 0.26
% 2.23/1.37  Inferencing          : 0.11
% 2.23/1.37  Reduction            : 0.08
% 2.23/1.37  Demodulation         : 0.06
% 2.23/1.37  BG Simplification    : 0.02
% 2.23/1.37  Subsumption          : 0.04
% 2.23/1.37  Abstraction          : 0.01
% 2.23/1.37  MUC search           : 0.00
% 2.23/1.37  Cooper               : 0.00
% 2.23/1.37  Total                : 0.63
% 2.23/1.37  Index Insertion      : 0.00
% 2.23/1.37  Index Deletion       : 0.00
% 2.23/1.37  Index Matching       : 0.00
% 2.23/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
