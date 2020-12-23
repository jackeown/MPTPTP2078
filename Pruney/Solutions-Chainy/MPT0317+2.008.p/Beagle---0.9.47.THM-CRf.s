%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:00 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 149 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 267 expanded)
%              Number of equality atoms :   28 ( 103 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

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

tff(c_30,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_80,plain,(
    ! [B_23,D_24,A_25,C_26] :
      ( r2_hidden(B_23,D_24)
      | ~ r2_hidden(k4_tarski(A_25,B_23),k2_zfmisc_1(C_26,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_84,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_79,c_80])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [D_18,B_19,A_20] :
      ( D_18 = B_19
      | D_18 = A_20
      | ~ r2_hidden(D_18,k2_tarski(A_20,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [D_18,A_7] :
      ( D_18 = A_7
      | D_18 = A_7
      | ~ r2_hidden(D_18,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_88,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_84,c_68])).

tff(c_90,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_79])).

tff(c_101,plain,(
    ! [A_27,C_28,B_29,D_30] :
      ( r2_hidden(A_27,C_28)
      | ~ r2_hidden(k4_tarski(A_27,B_29),k2_zfmisc_1(C_28,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_90,c_101])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_104])).

tff(c_110,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_38])).

tff(c_48,plain,(
    ! [D_13,B_14] : r2_hidden(D_13,k2_tarski(D_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_51,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_48])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11))
      | ~ r2_hidden(B_9,D_11)
      | ~ r2_hidden(A_8,C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_135,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_34])).

tff(c_136,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_135])).

tff(c_139,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_51,c_139])).

tff(c_145,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_144,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_146,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_171,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_177,plain,(
    ! [B_61,D_62,A_63,C_64] :
      ( r2_hidden(B_61,D_62)
      | ~ r2_hidden(k4_tarski(A_63,B_61),k2_zfmisc_1(C_64,D_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_171,c_177])).

tff(c_150,plain,(
    ! [D_52,B_53,A_54] :
      ( D_52 = B_53
      | D_52 = A_54
      | ~ r2_hidden(D_52,k2_tarski(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_159,plain,(
    ! [D_52,A_7] :
      ( D_52 = A_7
      | D_52 = A_7
      | ~ r2_hidden(D_52,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_150])).

tff(c_184,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_181,c_159])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_146,c_184])).

tff(c_190,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_191,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_191])).

tff(c_197,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_189,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_224,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_34])).

tff(c_225,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_224])).

tff(c_228,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_51,c_228])).

tff(c_234,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_32,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_244,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_234,c_32])).

tff(c_233,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_279,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_234,c_233,c_28])).

tff(c_282,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_279])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_51,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:00:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.13/1.31  
% 2.13/1.31  %Foreground sorts:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Background operators:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Foreground operators:
% 2.13/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.13/1.31  tff('#skF_10', type, '#skF_10': $i).
% 2.13/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.31  tff('#skF_9', type, '#skF_9': $i).
% 2.13/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.31  
% 2.23/1.32  tff(f_49, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.23/1.32  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.23/1.32  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/1.32  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.23/1.32  tff(c_30, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.32  tff(c_58, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_30])).
% 2.23/1.32  tff(c_36, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.32  tff(c_79, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_36])).
% 2.23/1.32  tff(c_80, plain, (![B_23, D_24, A_25, C_26]: (r2_hidden(B_23, D_24) | ~r2_hidden(k4_tarski(A_25, B_23), k2_zfmisc_1(C_26, D_24)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.32  tff(c_84, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_79, c_80])).
% 2.23/1.32  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.32  tff(c_59, plain, (![D_18, B_19, A_20]: (D_18=B_19 | D_18=A_20 | ~r2_hidden(D_18, k2_tarski(A_20, B_19)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.32  tff(c_68, plain, (![D_18, A_7]: (D_18=A_7 | D_18=A_7 | ~r2_hidden(D_18, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_59])).
% 2.23/1.32  tff(c_88, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_84, c_68])).
% 2.23/1.32  tff(c_90, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_79])).
% 2.23/1.32  tff(c_101, plain, (![A_27, C_28, B_29, D_30]: (r2_hidden(A_27, C_28) | ~r2_hidden(k4_tarski(A_27, B_29), k2_zfmisc_1(C_28, D_30)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.32  tff(c_104, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_90, c_101])).
% 2.23/1.32  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_104])).
% 2.23/1.32  tff(c_110, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_36])).
% 2.23/1.32  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.32  tff(c_116, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_110, c_38])).
% 2.23/1.32  tff(c_48, plain, (![D_13, B_14]: (r2_hidden(D_13, k2_tarski(D_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.32  tff(c_51, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_48])).
% 2.23/1.32  tff(c_22, plain, (![A_8, B_9, C_10, D_11]: (r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)) | ~r2_hidden(B_9, D_11) | ~r2_hidden(A_8, C_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.32  tff(c_109, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.23/1.32  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.32  tff(c_135, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_34])).
% 2.23/1.32  tff(c_136, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_110, c_135])).
% 2.23/1.32  tff(c_139, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_136])).
% 2.23/1.32  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_51, c_139])).
% 2.23/1.32  tff(c_145, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_30])).
% 2.23/1.32  tff(c_144, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.23/1.32  tff(c_146, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_144])).
% 2.23/1.32  tff(c_171, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_36])).
% 2.23/1.32  tff(c_177, plain, (![B_61, D_62, A_63, C_64]: (r2_hidden(B_61, D_62) | ~r2_hidden(k4_tarski(A_63, B_61), k2_zfmisc_1(C_64, D_62)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.32  tff(c_181, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_171, c_177])).
% 2.23/1.32  tff(c_150, plain, (![D_52, B_53, A_54]: (D_52=B_53 | D_52=A_54 | ~r2_hidden(D_52, k2_tarski(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.32  tff(c_159, plain, (![D_52, A_7]: (D_52=A_7 | D_52=A_7 | ~r2_hidden(D_52, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_150])).
% 2.23/1.32  tff(c_184, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_181, c_159])).
% 2.23/1.32  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_146, c_184])).
% 2.23/1.32  tff(c_190, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_36])).
% 2.23/1.32  tff(c_191, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_38])).
% 2.23/1.32  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_191])).
% 2.23/1.32  tff(c_197, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 2.23/1.32  tff(c_189, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.23/1.32  tff(c_224, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_34])).
% 2.23/1.32  tff(c_225, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_190, c_224])).
% 2.23/1.32  tff(c_228, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_225])).
% 2.23/1.32  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_51, c_228])).
% 2.23/1.32  tff(c_234, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_144])).
% 2.23/1.32  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_5') | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.32  tff(c_244, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_234, c_32])).
% 2.23/1.32  tff(c_233, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_144])).
% 2.23/1.32  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.32  tff(c_279, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_234, c_233, c_28])).
% 2.23/1.32  tff(c_282, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_279])).
% 2.23/1.32  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_244, c_51, c_282])).
% 2.23/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  Inference rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Ref     : 0
% 2.23/1.32  #Sup     : 46
% 2.23/1.32  #Fact    : 0
% 2.23/1.32  #Define  : 0
% 2.23/1.32  #Split   : 6
% 2.23/1.32  #Chain   : 0
% 2.23/1.32  #Close   : 0
% 2.23/1.32  
% 2.23/1.32  Ordering : KBO
% 2.23/1.32  
% 2.23/1.32  Simplification rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Subsume      : 6
% 2.23/1.32  #Demod        : 28
% 2.23/1.32  #Tautology    : 35
% 2.23/1.32  #SimpNegUnit  : 6
% 2.23/1.32  #BackRed      : 2
% 2.23/1.32  
% 2.23/1.32  #Partial instantiations: 0
% 2.23/1.32  #Strategies tried      : 1
% 2.23/1.32  
% 2.23/1.32  Timing (in seconds)
% 2.23/1.32  ----------------------
% 2.27/1.32  Preprocessing        : 0.30
% 2.27/1.32  Parsing              : 0.15
% 2.27/1.32  CNF conversion       : 0.02
% 2.27/1.32  Main loop            : 0.21
% 2.27/1.32  Inferencing          : 0.08
% 2.27/1.33  Reduction            : 0.06
% 2.27/1.33  Demodulation         : 0.05
% 2.27/1.33  BG Simplification    : 0.01
% 2.27/1.33  Subsumption          : 0.04
% 2.27/1.33  Abstraction          : 0.01
% 2.27/1.33  MUC search           : 0.00
% 2.27/1.33  Cooper               : 0.00
% 2.27/1.33  Total                : 0.55
% 2.27/1.33  Index Insertion      : 0.00
% 2.27/1.33  Index Deletion       : 0.00
% 2.27/1.33  Index Matching       : 0.00
% 2.27/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
