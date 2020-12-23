%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:58 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 169 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 296 expanded)
%              Number of equality atoms :   31 ( 124 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_350,plain,(
    ! [A_108,B_109] : k1_enumset1(A_108,A_108,B_109) = k2_tarski(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_12] : k1_enumset1(A_12,A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_366,plain,(
    ! [B_110] : k2_tarski(B_110,B_110) = k1_tarski(B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_24])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_372,plain,(
    ! [B_110] : r2_hidden(B_110,k1_tarski(B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_4])).

tff(c_57,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [B_28] : k2_tarski(B_28,B_28) = k1_tarski(B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_24])).

tff(c_79,plain,(
    ! [B_28] : r2_hidden(B_28,k1_tarski(B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_4])).

tff(c_38,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_121,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_126,plain,(
    ! [A_42,C_43,B_44,D_45] :
      ( r2_hidden(A_42,C_43)
      | ~ r2_hidden(k4_tarski(A_42,B_44),k2_zfmisc_1(C_43,D_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_121,c_126])).

tff(c_64,plain,(
    ! [B_27] : k2_tarski(B_27,B_27) = k1_tarski(B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_24])).

tff(c_91,plain,(
    ! [D_30,B_31,A_32] :
      ( D_30 = B_31
      | D_30 = A_32
      | ~ r2_hidden(D_30,k2_tarski(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_94,plain,(
    ! [D_30,B_27] :
      ( D_30 = B_27
      | D_30 = B_27
      | ~ r2_hidden(D_30,k1_tarski(B_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_91])).

tff(c_134,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_130,c_94])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_134])).

tff(c_140,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_42])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20))
      | ~ r2_hidden(B_18,D_20)
      | ~ r2_hidden(A_17,C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_139,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_171,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_40])).

tff(c_172,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_171])).

tff(c_175,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_146,c_175])).

tff(c_181,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_187,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_203,plain,(
    ! [B_60] : k2_tarski(B_60,B_60) = k1_tarski(B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_24])).

tff(c_209,plain,(
    ! [B_60] : r2_hidden(B_60,k1_tarski(B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_4])).

tff(c_180,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_186,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_223,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_44])).

tff(c_224,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_260,plain,(
    ! [B_74,D_75,A_76,C_77] :
      ( r2_hidden(B_74,D_75)
      | ~ r2_hidden(k4_tarski(A_76,B_74),k2_zfmisc_1(C_77,D_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_263,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_224,c_260])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_263])).

tff(c_269,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_288,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_42])).

tff(c_289,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_288])).

tff(c_268,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_335,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_268,c_40])).

tff(c_336,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_335])).

tff(c_339,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_336])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_289,c_339])).

tff(c_345,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_36,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_383,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_345,c_36])).

tff(c_430,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( r2_hidden(k4_tarski(A_132,B_133),k2_zfmisc_1(C_134,D_135))
      | ~ r2_hidden(B_133,D_135)
      | ~ r2_hidden(A_132,C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_344,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_429,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_345,c_344,c_34])).

tff(c_433,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_430,c_429])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_383,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.36  
% 2.23/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.36  %$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.23/1.36  
% 2.23/1.36  %Foreground sorts:
% 2.23/1.36  
% 2.23/1.36  
% 2.23/1.36  %Background operators:
% 2.23/1.36  
% 2.23/1.36  
% 2.23/1.36  %Foreground operators:
% 2.23/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.36  tff('#skF_10', type, '#skF_10': $i).
% 2.23/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.23/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.23/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.36  
% 2.23/1.38  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.23/1.38  tff(f_40, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.23/1.38  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.23/1.38  tff(f_55, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.23/1.38  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.23/1.38  tff(c_350, plain, (![A_108, B_109]: (k1_enumset1(A_108, A_108, B_109)=k2_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.38  tff(c_24, plain, (![A_12]: (k1_enumset1(A_12, A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.38  tff(c_366, plain, (![B_110]: (k2_tarski(B_110, B_110)=k1_tarski(B_110))), inference(superposition, [status(thm), theory('equality')], [c_350, c_24])).
% 2.23/1.38  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.38  tff(c_372, plain, (![B_110]: (r2_hidden(B_110, k1_tarski(B_110)))), inference(superposition, [status(thm), theory('equality')], [c_366, c_4])).
% 2.23/1.38  tff(c_57, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.38  tff(c_73, plain, (![B_28]: (k2_tarski(B_28, B_28)=k1_tarski(B_28))), inference(superposition, [status(thm), theory('equality')], [c_57, c_24])).
% 2.23/1.38  tff(c_79, plain, (![B_28]: (r2_hidden(B_28, k1_tarski(B_28)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_4])).
% 2.23/1.38  tff(c_38, plain, ('#skF_5'='#skF_3' | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.38  tff(c_56, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_38])).
% 2.23/1.38  tff(c_44, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.38  tff(c_121, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.23/1.38  tff(c_126, plain, (![A_42, C_43, B_44, D_45]: (r2_hidden(A_42, C_43) | ~r2_hidden(k4_tarski(A_42, B_44), k2_zfmisc_1(C_43, D_45)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.38  tff(c_130, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_121, c_126])).
% 2.23/1.38  tff(c_64, plain, (![B_27]: (k2_tarski(B_27, B_27)=k1_tarski(B_27))), inference(superposition, [status(thm), theory('equality')], [c_57, c_24])).
% 2.23/1.38  tff(c_91, plain, (![D_30, B_31, A_32]: (D_30=B_31 | D_30=A_32 | ~r2_hidden(D_30, k2_tarski(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.38  tff(c_94, plain, (![D_30, B_27]: (D_30=B_27 | D_30=B_27 | ~r2_hidden(D_30, k1_tarski(B_27)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_91])).
% 2.23/1.38  tff(c_134, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_130, c_94])).
% 2.23/1.38  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_134])).
% 2.23/1.38  tff(c_140, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_44])).
% 2.23/1.38  tff(c_42, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.38  tff(c_146, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_140, c_42])).
% 2.23/1.38  tff(c_28, plain, (![A_17, B_18, C_19, D_20]: (r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)) | ~r2_hidden(B_18, D_20) | ~r2_hidden(A_17, C_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.38  tff(c_139, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.23/1.38  tff(c_40, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.38  tff(c_171, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_40])).
% 2.23/1.38  tff(c_172, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_140, c_171])).
% 2.23/1.38  tff(c_175, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_172])).
% 2.23/1.38  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_146, c_175])).
% 2.23/1.38  tff(c_181, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_38])).
% 2.23/1.38  tff(c_187, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.38  tff(c_203, plain, (![B_60]: (k2_tarski(B_60, B_60)=k1_tarski(B_60))), inference(superposition, [status(thm), theory('equality')], [c_187, c_24])).
% 2.23/1.38  tff(c_209, plain, (![B_60]: (r2_hidden(B_60, k1_tarski(B_60)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_4])).
% 2.23/1.38  tff(c_180, plain, (~r2_hidden('#skF_8', '#skF_10') | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 2.23/1.38  tff(c_186, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_180])).
% 2.23/1.38  tff(c_223, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_44])).
% 2.23/1.38  tff(c_224, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_223])).
% 2.23/1.38  tff(c_260, plain, (![B_74, D_75, A_76, C_77]: (r2_hidden(B_74, D_75) | ~r2_hidden(k4_tarski(A_76, B_74), k2_zfmisc_1(C_77, D_75)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.38  tff(c_263, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_224, c_260])).
% 2.23/1.38  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_263])).
% 2.23/1.38  tff(c_269, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_223])).
% 2.23/1.38  tff(c_288, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_42])).
% 2.23/1.38  tff(c_289, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_269, c_288])).
% 2.23/1.38  tff(c_268, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_223])).
% 2.23/1.38  tff(c_335, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_268, c_40])).
% 2.23/1.38  tff(c_336, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_269, c_335])).
% 2.23/1.38  tff(c_339, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_336])).
% 2.23/1.38  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_289, c_339])).
% 2.23/1.38  tff(c_345, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_180])).
% 2.23/1.38  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.38  tff(c_383, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_345, c_36])).
% 2.23/1.38  tff(c_430, plain, (![A_132, B_133, C_134, D_135]: (r2_hidden(k4_tarski(A_132, B_133), k2_zfmisc_1(C_134, D_135)) | ~r2_hidden(B_133, D_135) | ~r2_hidden(A_132, C_134))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.38  tff(c_344, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_180])).
% 2.23/1.38  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.38  tff(c_429, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_345, c_344, c_34])).
% 2.23/1.38  tff(c_433, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_430, c_429])).
% 2.23/1.38  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_372, c_383, c_433])).
% 2.23/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.38  
% 2.23/1.38  Inference rules
% 2.23/1.38  ----------------------
% 2.23/1.38  #Ref     : 0
% 2.23/1.38  #Sup     : 80
% 2.23/1.38  #Fact    : 0
% 2.23/1.38  #Define  : 0
% 2.23/1.38  #Split   : 5
% 2.23/1.38  #Chain   : 0
% 2.23/1.38  #Close   : 0
% 2.23/1.38  
% 2.23/1.38  Ordering : KBO
% 2.23/1.38  
% 2.23/1.38  Simplification rules
% 2.23/1.38  ----------------------
% 2.23/1.38  #Subsume      : 5
% 2.23/1.38  #Demod        : 33
% 2.23/1.38  #Tautology    : 62
% 2.23/1.38  #SimpNegUnit  : 6
% 2.23/1.38  #BackRed      : 0
% 2.23/1.38  
% 2.23/1.38  #Partial instantiations: 0
% 2.23/1.38  #Strategies tried      : 1
% 2.23/1.38  
% 2.23/1.38  Timing (in seconds)
% 2.23/1.38  ----------------------
% 2.52/1.39  Preprocessing        : 0.32
% 2.52/1.39  Parsing              : 0.16
% 2.52/1.39  CNF conversion       : 0.02
% 2.52/1.39  Main loop            : 0.27
% 2.52/1.39  Inferencing          : 0.11
% 2.52/1.39  Reduction            : 0.08
% 2.52/1.39  Demodulation         : 0.06
% 2.52/1.39  BG Simplification    : 0.02
% 2.52/1.39  Subsumption          : 0.04
% 2.52/1.39  Abstraction          : 0.01
% 2.52/1.39  MUC search           : 0.00
% 2.52/1.39  Cooper               : 0.00
% 2.52/1.39  Total                : 0.63
% 2.52/1.39  Index Insertion      : 0.00
% 2.52/1.39  Index Deletion       : 0.00
% 2.52/1.39  Index Matching       : 0.00
% 2.52/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
