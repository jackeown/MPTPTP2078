%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:57 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 179 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 328 expanded)
%              Number of equality atoms :   32 ( 138 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_354,plain,(
    ! [A_101,B_102] : r2_hidden(A_101,k2_tarski(A_101,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_6])).

tff(c_357,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_354])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [B_30,A_31] : r2_hidden(B_30,k2_tarski(A_31,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_83,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_80])).

tff(c_42,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_106,plain,(
    ! [A_42,C_43,B_44,D_45] :
      ( r2_hidden(A_42,C_43)
      | ~ r2_hidden(k4_tarski(A_42,B_44),k2_zfmisc_1(C_43,D_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_110,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_101,c_106])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_112,plain,(
    ! [E_46,C_47,B_48,A_49] :
      ( E_46 = C_47
      | E_46 = B_48
      | E_46 = A_49
      | ~ r2_hidden(E_46,k1_enumset1(A_49,B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_131,plain,(
    ! [E_50,B_51,A_52] :
      ( E_50 = B_51
      | E_50 = A_52
      | E_50 = A_52
      | ~ r2_hidden(E_50,k2_tarski(A_52,B_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_112])).

tff(c_145,plain,(
    ! [E_53,A_54] :
      ( E_53 = A_54
      | E_53 = A_54
      | E_53 = A_54
      | ~ r2_hidden(E_53,k1_tarski(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_131])).

tff(c_148,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_110,c_145])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_79,c_79,c_148])).

tff(c_157,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_163,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_46])).

tff(c_32,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17))
      | ~ r2_hidden(B_15,D_17)
      | ~ r2_hidden(A_14,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_156,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_218,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_44])).

tff(c_219,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_218])).

tff(c_222,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_163,c_222])).

tff(c_228,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_234,plain,(
    ! [A_72,B_73] : r2_hidden(A_72,k2_tarski(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8])).

tff(c_237,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_234])).

tff(c_227,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_233,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_258,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_48])).

tff(c_259,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_34,plain,(
    ! [B_15,D_17,A_14,C_16] :
      ( r2_hidden(B_15,D_17)
      | ~ r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_265,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_259,c_34])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_265])).

tff(c_273,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_278,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_46])).

tff(c_279,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_279])).

tff(c_281,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_272,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_339,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_272,c_44])).

tff(c_340,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_339])).

tff(c_343,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_340])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_281,c_343])).

tff(c_349,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_40,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_360,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_349,c_40])).

tff(c_348,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_38,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_429,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_349,c_348,c_38])).

tff(c_432,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_429])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_360,c_432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.33  
% 2.31/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.33  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 2.31/1.33  
% 2.31/1.33  %Foreground sorts:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Background operators:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Foreground operators:
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.33  tff('#skF_10', type, '#skF_10': $i).
% 2.31/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.31/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.33  tff('#skF_9', type, '#skF_9': $i).
% 2.31/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.31/1.33  
% 2.31/1.35  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.31/1.35  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.31/1.35  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.31/1.35  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.31/1.35  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.31/1.35  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.31/1.35  tff(c_61, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.31/1.35  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.35  tff(c_354, plain, (![A_101, B_102]: (r2_hidden(A_101, k2_tarski(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_6])).
% 2.31/1.35  tff(c_357, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_354])).
% 2.31/1.35  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.35  tff(c_80, plain, (![B_30, A_31]: (r2_hidden(B_30, k2_tarski(A_31, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 2.31/1.35  tff(c_83, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_80])).
% 2.31/1.35  tff(c_42, plain, ('#skF_5'='#skF_3' | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.35  tff(c_79, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_42])).
% 2.31/1.35  tff(c_48, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.35  tff(c_101, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.31/1.35  tff(c_106, plain, (![A_42, C_43, B_44, D_45]: (r2_hidden(A_42, C_43) | ~r2_hidden(k4_tarski(A_42, B_44), k2_zfmisc_1(C_43, D_45)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.35  tff(c_110, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_101, c_106])).
% 2.31/1.35  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.31/1.35  tff(c_112, plain, (![E_46, C_47, B_48, A_49]: (E_46=C_47 | E_46=B_48 | E_46=A_49 | ~r2_hidden(E_46, k1_enumset1(A_49, B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.35  tff(c_131, plain, (![E_50, B_51, A_52]: (E_50=B_51 | E_50=A_52 | E_50=A_52 | ~r2_hidden(E_50, k2_tarski(A_52, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_112])).
% 2.31/1.35  tff(c_145, plain, (![E_53, A_54]: (E_53=A_54 | E_53=A_54 | E_53=A_54 | ~r2_hidden(E_53, k1_tarski(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_131])).
% 2.31/1.35  tff(c_148, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_110, c_145])).
% 2.31/1.35  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_79, c_79, c_148])).
% 2.31/1.35  tff(c_157, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_48])).
% 2.31/1.35  tff(c_46, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.35  tff(c_163, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_157, c_46])).
% 2.31/1.35  tff(c_32, plain, (![A_14, B_15, C_16, D_17]: (r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)) | ~r2_hidden(B_15, D_17) | ~r2_hidden(A_14, C_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.35  tff(c_156, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 2.31/1.35  tff(c_44, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.35  tff(c_218, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_44])).
% 2.31/1.35  tff(c_219, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_157, c_218])).
% 2.31/1.35  tff(c_222, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_219])).
% 2.31/1.35  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_163, c_222])).
% 2.31/1.35  tff(c_228, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_42])).
% 2.31/1.35  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.35  tff(c_234, plain, (![A_72, B_73]: (r2_hidden(A_72, k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_8])).
% 2.31/1.35  tff(c_237, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_234])).
% 2.31/1.35  tff(c_227, plain, (~r2_hidden('#skF_8', '#skF_10') | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 2.31/1.35  tff(c_233, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_227])).
% 2.31/1.35  tff(c_258, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_48])).
% 2.31/1.35  tff(c_259, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_258])).
% 2.31/1.35  tff(c_34, plain, (![B_15, D_17, A_14, C_16]: (r2_hidden(B_15, D_17) | ~r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.35  tff(c_265, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_259, c_34])).
% 2.31/1.35  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_265])).
% 2.31/1.35  tff(c_273, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_258])).
% 2.31/1.35  tff(c_278, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_46])).
% 2.31/1.35  tff(c_279, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_278])).
% 2.31/1.35  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_279])).
% 2.31/1.35  tff(c_281, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_278])).
% 2.31/1.35  tff(c_272, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_258])).
% 2.31/1.35  tff(c_339, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_272, c_44])).
% 2.31/1.35  tff(c_340, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_273, c_339])).
% 2.31/1.35  tff(c_343, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_340])).
% 2.31/1.35  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237, c_281, c_343])).
% 2.31/1.35  tff(c_349, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_227])).
% 2.31/1.35  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.35  tff(c_360, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_349, c_40])).
% 2.31/1.35  tff(c_348, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_227])).
% 2.31/1.35  tff(c_38, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.35  tff(c_429, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_349, c_348, c_38])).
% 2.31/1.35  tff(c_432, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_429])).
% 2.31/1.35  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_360, c_432])).
% 2.31/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.35  
% 2.31/1.35  Inference rules
% 2.31/1.35  ----------------------
% 2.31/1.35  #Ref     : 0
% 2.31/1.35  #Sup     : 75
% 2.31/1.35  #Fact    : 0
% 2.31/1.35  #Define  : 0
% 2.31/1.35  #Split   : 6
% 2.31/1.35  #Chain   : 0
% 2.31/1.35  #Close   : 0
% 2.31/1.35  
% 2.31/1.35  Ordering : KBO
% 2.31/1.35  
% 2.31/1.35  Simplification rules
% 2.31/1.35  ----------------------
% 2.31/1.35  #Subsume      : 6
% 2.31/1.35  #Demod        : 33
% 2.31/1.35  #Tautology    : 57
% 2.31/1.35  #SimpNegUnit  : 6
% 2.31/1.35  #BackRed      : 0
% 2.31/1.35  
% 2.31/1.35  #Partial instantiations: 0
% 2.31/1.35  #Strategies tried      : 1
% 2.31/1.35  
% 2.31/1.35  Timing (in seconds)
% 2.31/1.35  ----------------------
% 2.31/1.35  Preprocessing        : 0.29
% 2.31/1.35  Parsing              : 0.14
% 2.31/1.35  CNF conversion       : 0.02
% 2.31/1.35  Main loop            : 0.24
% 2.31/1.35  Inferencing          : 0.09
% 2.31/1.35  Reduction            : 0.07
% 2.31/1.35  Demodulation         : 0.06
% 2.31/1.35  BG Simplification    : 0.02
% 2.31/1.35  Subsumption          : 0.04
% 2.31/1.35  Abstraction          : 0.01
% 2.31/1.35  MUC search           : 0.00
% 2.31/1.35  Cooper               : 0.00
% 2.31/1.35  Total                : 0.57
% 2.31/1.35  Index Insertion      : 0.00
% 2.31/1.35  Index Deletion       : 0.00
% 2.31/1.35  Index Matching       : 0.00
% 2.31/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
