%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:58 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 160 expanded)
%              Number of leaves         :   28 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 284 expanded)
%              Number of equality atoms :   23 ( 112 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    ! [D_40,B_41] : r2_hidden(D_40,k2_tarski(D_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_60])).

tff(c_44,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_110,plain,(
    ! [A_55,C_56,B_57,D_58] :
      ( r2_hidden(A_55,C_56)
      | ~ r2_hidden(k4_tarski(A_55,B_57),k2_zfmisc_1(C_56,D_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_114,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_89,c_110])).

tff(c_90,plain,(
    ! [D_50,B_51,A_52] :
      ( D_50 = B_51
      | D_50 = A_52
      | ~ r2_hidden(D_50,k2_tarski(A_52,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,(
    ! [D_50,A_7] :
      ( D_50 = A_7
      | D_50 = A_7
      | ~ r2_hidden(D_50,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_90])).

tff(c_117,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_114,c_99])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_117])).

tff(c_123,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_148,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_48])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( r2_hidden(k4_tarski(A_35,B_36),k2_zfmisc_1(C_37,D_38))
      | ~ r2_hidden(B_36,D_38)
      | ~ r2_hidden(A_35,C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_46,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_185,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_46])).

tff(c_186,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_185])).

tff(c_189,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_148,c_189])).

tff(c_195,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_194,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_200,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_242,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_50])).

tff(c_243,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_36,plain,(
    ! [B_36,D_38,A_35,C_37] :
      ( r2_hidden(B_36,D_38)
      | ~ r2_hidden(k4_tarski(A_35,B_36),k2_zfmisc_1(C_37,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_246,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_243,c_36])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_246])).

tff(c_252,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_258,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_48])).

tff(c_259,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_258])).

tff(c_251,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_295,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_251,c_46])).

tff(c_296,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_295])).

tff(c_299,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_296])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_259,c_299])).

tff(c_305,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_42,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_320,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_305,c_42])).

tff(c_304,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_40,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_382,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_305,c_304,c_40])).

tff(c_385,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_382])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_320,c_385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.32  
% 2.15/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.32  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.15/1.32  
% 2.15/1.32  %Foreground sorts:
% 2.15/1.32  
% 2.15/1.32  
% 2.15/1.32  %Background operators:
% 2.15/1.32  
% 2.15/1.32  
% 2.15/1.32  %Foreground operators:
% 2.15/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.32  tff('#skF_10', type, '#skF_10': $i).
% 2.15/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.32  tff('#skF_9', type, '#skF_9': $i).
% 2.15/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.32  
% 2.42/1.34  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.42/1.34  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.42/1.34  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.42/1.34  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.42/1.34  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.42/1.34  tff(c_60, plain, (![D_40, B_41]: (r2_hidden(D_40, k2_tarski(D_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.42/1.34  tff(c_63, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_60])).
% 2.42/1.34  tff(c_44, plain, ('#skF_5'='#skF_3' | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.34  tff(c_70, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_44])).
% 2.42/1.34  tff(c_50, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.34  tff(c_89, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.42/1.34  tff(c_110, plain, (![A_55, C_56, B_57, D_58]: (r2_hidden(A_55, C_56) | ~r2_hidden(k4_tarski(A_55, B_57), k2_zfmisc_1(C_56, D_58)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.34  tff(c_114, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_89, c_110])).
% 2.42/1.34  tff(c_90, plain, (![D_50, B_51, A_52]: (D_50=B_51 | D_50=A_52 | ~r2_hidden(D_50, k2_tarski(A_52, B_51)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.42/1.34  tff(c_99, plain, (![D_50, A_7]: (D_50=A_7 | D_50=A_7 | ~r2_hidden(D_50, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_90])).
% 2.42/1.34  tff(c_117, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_114, c_99])).
% 2.42/1.34  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_117])).
% 2.42/1.34  tff(c_123, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_50])).
% 2.42/1.34  tff(c_48, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.34  tff(c_148, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_123, c_48])).
% 2.42/1.34  tff(c_34, plain, (![A_35, B_36, C_37, D_38]: (r2_hidden(k4_tarski(A_35, B_36), k2_zfmisc_1(C_37, D_38)) | ~r2_hidden(B_36, D_38) | ~r2_hidden(A_35, C_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.34  tff(c_122, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 2.42/1.34  tff(c_46, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.34  tff(c_185, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_46])).
% 2.42/1.34  tff(c_186, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_123, c_185])).
% 2.42/1.34  tff(c_189, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_186])).
% 2.42/1.34  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_148, c_189])).
% 2.42/1.34  tff(c_195, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_44])).
% 2.42/1.34  tff(c_194, plain, (~r2_hidden('#skF_8', '#skF_10') | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.42/1.34  tff(c_200, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_194])).
% 2.42/1.34  tff(c_242, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_50])).
% 2.42/1.34  tff(c_243, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_242])).
% 2.42/1.34  tff(c_36, plain, (![B_36, D_38, A_35, C_37]: (r2_hidden(B_36, D_38) | ~r2_hidden(k4_tarski(A_35, B_36), k2_zfmisc_1(C_37, D_38)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.34  tff(c_246, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_243, c_36])).
% 2.42/1.34  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_246])).
% 2.42/1.34  tff(c_252, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_242])).
% 2.42/1.34  tff(c_258, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_48])).
% 2.42/1.34  tff(c_259, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_252, c_258])).
% 2.42/1.34  tff(c_251, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_242])).
% 2.42/1.34  tff(c_295, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_251, c_46])).
% 2.42/1.34  tff(c_296, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_252, c_295])).
% 2.42/1.34  tff(c_299, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_296])).
% 2.42/1.34  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_259, c_299])).
% 2.42/1.34  tff(c_305, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_194])).
% 2.42/1.34  tff(c_42, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.34  tff(c_320, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_305, c_42])).
% 2.42/1.34  tff(c_304, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_194])).
% 2.42/1.34  tff(c_40, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.34  tff(c_382, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_305, c_304, c_40])).
% 2.42/1.34  tff(c_385, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_382])).
% 2.42/1.34  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_320, c_385])).
% 2.42/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  Inference rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Ref     : 0
% 2.42/1.34  #Sup     : 66
% 2.42/1.34  #Fact    : 0
% 2.42/1.34  #Define  : 0
% 2.42/1.34  #Split   : 5
% 2.42/1.34  #Chain   : 0
% 2.42/1.34  #Close   : 0
% 2.42/1.34  
% 2.42/1.34  Ordering : KBO
% 2.42/1.34  
% 2.42/1.34  Simplification rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Subsume      : 5
% 2.42/1.34  #Demod        : 26
% 2.42/1.34  #Tautology    : 55
% 2.42/1.34  #SimpNegUnit  : 6
% 2.42/1.34  #BackRed      : 0
% 2.42/1.34  
% 2.42/1.34  #Partial instantiations: 0
% 2.42/1.34  #Strategies tried      : 1
% 2.42/1.34  
% 2.42/1.34  Timing (in seconds)
% 2.42/1.34  ----------------------
% 2.42/1.34  Preprocessing        : 0.33
% 2.42/1.34  Parsing              : 0.17
% 2.42/1.34  CNF conversion       : 0.02
% 2.42/1.34  Main loop            : 0.21
% 2.42/1.34  Inferencing          : 0.08
% 2.42/1.34  Reduction            : 0.07
% 2.42/1.34  Demodulation         : 0.05
% 2.42/1.34  BG Simplification    : 0.02
% 2.42/1.34  Subsumption          : 0.03
% 2.42/1.34  Abstraction          : 0.01
% 2.42/1.34  MUC search           : 0.00
% 2.42/1.34  Cooper               : 0.00
% 2.42/1.34  Total                : 0.58
% 2.42/1.34  Index Insertion      : 0.00
% 2.42/1.34  Index Deletion       : 0.00
% 2.42/1.34  Index Matching       : 0.00
% 2.42/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
