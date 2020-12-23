%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:52 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 190 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 365 expanded)
%              Number of equality atoms :   49 ( 232 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_344,plain,(
    ! [A_121] : k1_enumset1(A_121,A_121,A_121) = k1_tarski(A_121) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_350,plain,(
    ! [A_121] : r2_hidden(A_121,k1_tarski(A_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_6])).

tff(c_28,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12))
      | ~ r2_hidden(B_10,D_12)
      | ~ r2_hidden(A_9,C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    ! [A_22] : k1_enumset1(A_22,A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_4])).

tff(c_38,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_76,plain,(
    ! [A_28,C_29,B_30,D_31] :
      ( r2_hidden(A_28,C_29)
      | ~ r2_hidden(k4_tarski(A_28,B_30),k2_zfmisc_1(C_29,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_69,c_76])).

tff(c_26,plain,(
    ! [A_8] : k1_enumset1(A_8,A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [E_32,C_33,B_34,A_35] :
      ( E_32 = C_33
      | E_32 = B_34
      | E_32 = A_35
      | ~ r2_hidden(E_32,k1_enumset1(A_35,B_34,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_101,plain,(
    ! [E_36,A_37] :
      ( E_36 = A_37
      | E_36 = A_37
      | E_36 = A_37
      | ~ r2_hidden(E_36,k1_tarski(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_82])).

tff(c_104,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_80,c_101])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_45,c_45,c_104])).

tff(c_116,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_117])).

tff(c_124,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_115,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_115,c_40])).

tff(c_180,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_179])).

tff(c_183,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_180])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_183])).

tff(c_189,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_196,plain,(
    ! [A_67] : k1_enumset1(A_67,A_67,A_67) = k1_tarski(A_67) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_202,plain,(
    ! [A_67] : r2_hidden(A_67,k1_tarski(A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_8])).

tff(c_188,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_194,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_221,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_44])).

tff(c_222,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_223,plain,(
    ! [B_75,D_76,A_77,C_78] :
      ( r2_hidden(B_75,D_76)
      | ~ r2_hidden(k4_tarski(A_77,B_75),k2_zfmisc_1(C_78,D_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_227,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_222,c_223])).

tff(c_235,plain,(
    ! [E_83,C_84,B_85,A_86] :
      ( E_83 = C_84
      | E_83 = B_85
      | E_83 = A_86
      | ~ r2_hidden(E_83,k1_enumset1(A_86,B_85,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_254,plain,(
    ! [E_87,A_88] :
      ( E_87 = A_88
      | E_87 = A_88
      | E_87 = A_88
      | ~ r2_hidden(E_87,k1_tarski(A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_235])).

tff(c_257,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_227,c_254])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_194,c_194,c_257])).

tff(c_266,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_271,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_42])).

tff(c_272,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_271])).

tff(c_265,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_323,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_272,c_265,c_40])).

tff(c_324,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_323])).

tff(c_327,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_324])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_202,c_327])).

tff(c_333,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_36,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_360,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_333,c_36])).

tff(c_332,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_411,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_333,c_360,c_332,c_34])).

tff(c_414,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_411])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_350,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 2.09/1.26  
% 2.09/1.26  %Foreground sorts:
% 2.09/1.26  
% 2.09/1.26  
% 2.09/1.26  %Background operators:
% 2.09/1.26  
% 2.09/1.26  
% 2.09/1.26  %Foreground operators:
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.26  tff('#skF_10', type, '#skF_10': $i).
% 2.09/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.09/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.26  tff('#skF_9', type, '#skF_9': $i).
% 2.09/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.09/1.26  
% 2.23/1.28  tff(f_42, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 2.23/1.28  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.23/1.28  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.23/1.28  tff(f_55, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.23/1.28  tff(c_344, plain, (![A_121]: (k1_enumset1(A_121, A_121, A_121)=k1_tarski(A_121))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.28  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.28  tff(c_350, plain, (![A_121]: (r2_hidden(A_121, k1_tarski(A_121)))), inference(superposition, [status(thm), theory('equality')], [c_344, c_6])).
% 2.23/1.28  tff(c_28, plain, (![A_9, B_10, C_11, D_12]: (r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)) | ~r2_hidden(B_10, D_12) | ~r2_hidden(A_9, C_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.28  tff(c_49, plain, (![A_22]: (k1_enumset1(A_22, A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.28  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.28  tff(c_55, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_4])).
% 2.23/1.28  tff(c_38, plain, ('#skF_5'='#skF_3' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.28  tff(c_45, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_38])).
% 2.23/1.28  tff(c_44, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.28  tff(c_69, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_44])).
% 2.23/1.28  tff(c_76, plain, (![A_28, C_29, B_30, D_31]: (r2_hidden(A_28, C_29) | ~r2_hidden(k4_tarski(A_28, B_30), k2_zfmisc_1(C_29, D_31)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.28  tff(c_80, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_69, c_76])).
% 2.23/1.28  tff(c_26, plain, (![A_8]: (k1_enumset1(A_8, A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.28  tff(c_82, plain, (![E_32, C_33, B_34, A_35]: (E_32=C_33 | E_32=B_34 | E_32=A_35 | ~r2_hidden(E_32, k1_enumset1(A_35, B_34, C_33)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.28  tff(c_101, plain, (![E_36, A_37]: (E_36=A_37 | E_36=A_37 | E_36=A_37 | ~r2_hidden(E_36, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_82])).
% 2.23/1.28  tff(c_104, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_80, c_101])).
% 2.23/1.28  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_45, c_45, c_104])).
% 2.23/1.28  tff(c_116, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_44])).
% 2.23/1.28  tff(c_42, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.28  tff(c_117, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_42])).
% 2.23/1.28  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_117])).
% 2.23/1.28  tff(c_124, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.23/1.28  tff(c_115, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.23/1.28  tff(c_40, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.28  tff(c_179, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_115, c_40])).
% 2.23/1.28  tff(c_180, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_116, c_179])).
% 2.23/1.28  tff(c_183, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_180])).
% 2.23/1.28  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_183])).
% 2.23/1.28  tff(c_189, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_38])).
% 2.23/1.28  tff(c_196, plain, (![A_67]: (k1_enumset1(A_67, A_67, A_67)=k1_tarski(A_67))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.28  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.28  tff(c_202, plain, (![A_67]: (r2_hidden(A_67, k1_tarski(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_196, c_8])).
% 2.23/1.28  tff(c_188, plain, ('#skF_10'!='#skF_8' | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 2.23/1.28  tff(c_194, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_188])).
% 2.23/1.28  tff(c_221, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_44])).
% 2.23/1.28  tff(c_222, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_221])).
% 2.23/1.28  tff(c_223, plain, (![B_75, D_76, A_77, C_78]: (r2_hidden(B_75, D_76) | ~r2_hidden(k4_tarski(A_77, B_75), k2_zfmisc_1(C_78, D_76)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.28  tff(c_227, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_222, c_223])).
% 2.23/1.28  tff(c_235, plain, (![E_83, C_84, B_85, A_86]: (E_83=C_84 | E_83=B_85 | E_83=A_86 | ~r2_hidden(E_83, k1_enumset1(A_86, B_85, C_84)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.28  tff(c_254, plain, (![E_87, A_88]: (E_87=A_88 | E_87=A_88 | E_87=A_88 | ~r2_hidden(E_87, k1_tarski(A_88)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_235])).
% 2.23/1.28  tff(c_257, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_227, c_254])).
% 2.23/1.28  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_194, c_194, c_257])).
% 2.23/1.28  tff(c_266, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_221])).
% 2.23/1.28  tff(c_271, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_42])).
% 2.23/1.28  tff(c_272, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_266, c_271])).
% 2.23/1.28  tff(c_265, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_221])).
% 2.23/1.28  tff(c_323, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_272, c_265, c_40])).
% 2.23/1.28  tff(c_324, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_266, c_323])).
% 2.23/1.28  tff(c_327, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_324])).
% 2.23/1.28  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_202, c_327])).
% 2.23/1.28  tff(c_333, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_188])).
% 2.23/1.28  tff(c_36, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.28  tff(c_360, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_333, c_36])).
% 2.23/1.28  tff(c_332, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_188])).
% 2.23/1.28  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.28  tff(c_411, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_333, c_360, c_332, c_34])).
% 2.23/1.28  tff(c_414, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_411])).
% 2.23/1.28  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_350, c_350, c_414])).
% 2.23/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  Inference rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Ref     : 0
% 2.23/1.28  #Sup     : 76
% 2.23/1.28  #Fact    : 0
% 2.23/1.28  #Define  : 0
% 2.23/1.28  #Split   : 6
% 2.23/1.28  #Chain   : 0
% 2.23/1.28  #Close   : 0
% 2.23/1.28  
% 2.23/1.28  Ordering : KBO
% 2.23/1.28  
% 2.23/1.28  Simplification rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Subsume      : 5
% 2.23/1.28  #Demod        : 44
% 2.23/1.28  #Tautology    : 61
% 2.23/1.28  #SimpNegUnit  : 6
% 2.23/1.28  #BackRed      : 0
% 2.23/1.28  
% 2.23/1.28  #Partial instantiations: 0
% 2.23/1.28  #Strategies tried      : 1
% 2.23/1.28  
% 2.23/1.28  Timing (in seconds)
% 2.23/1.28  ----------------------
% 2.23/1.28  Preprocessing        : 0.28
% 2.23/1.28  Parsing              : 0.14
% 2.23/1.28  CNF conversion       : 0.02
% 2.23/1.28  Main loop            : 0.23
% 2.23/1.28  Inferencing          : 0.09
% 2.23/1.28  Reduction            : 0.07
% 2.23/1.28  Demodulation         : 0.05
% 2.23/1.28  BG Simplification    : 0.01
% 2.23/1.28  Subsumption          : 0.04
% 2.23/1.28  Abstraction          : 0.01
% 2.23/1.28  MUC search           : 0.00
% 2.23/1.28  Cooper               : 0.00
% 2.23/1.28  Total                : 0.54
% 2.23/1.28  Index Insertion      : 0.00
% 2.23/1.28  Index Deletion       : 0.00
% 2.23/1.28  Index Matching       : 0.00
% 2.23/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
