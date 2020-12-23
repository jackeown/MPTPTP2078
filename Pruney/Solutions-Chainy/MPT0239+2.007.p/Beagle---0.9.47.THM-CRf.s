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
% DateTime   : Thu Dec  3 09:49:53 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 186 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 336 expanded)
%              Number of equality atoms :   45 ( 204 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [D_17,B_18] : r2_hidden(D_17,k2_tarski(D_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_26,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,D_13))
      | ~ r2_hidden(B_11,D_13)
      | ~ r2_hidden(A_10,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_144,plain,(
    ! [A_36,C_37,B_38,D_39] :
      ( r2_hidden(A_36,C_37)
      | ~ r2_hidden(k4_tarski(A_36,B_38),k2_zfmisc_1(C_37,D_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_148,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_82,c_144])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k1_tarski(A_14)
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | k4_xboole_0(k1_tarski(A_30),B_31) != k1_tarski(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_105])).

tff(c_151,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_148,c_109])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_151])).

tff(c_157,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_157])).

tff(c_227,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_226,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_156,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_309,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_156,c_42])).

tff(c_310,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_309])).

tff(c_313,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_310])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_313])).

tff(c_319,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_318,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_324,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_388,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_44])).

tff(c_389,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_405,plain,(
    ! [B_86,D_87,A_88,C_89] :
      ( r2_hidden(B_86,D_87)
      | ~ r2_hidden(k4_tarski(A_88,B_86),k2_zfmisc_1(C_89,D_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_409,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_389,c_405])).

tff(c_390,plain,(
    ! [A_82,B_83] :
      ( ~ r2_hidden(A_82,B_83)
      | k4_xboole_0(k1_tarski(A_82),B_83) != k1_tarski(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_398,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,k1_tarski(B_15))
      | B_15 = A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_390])).

tff(c_412,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_409,c_398])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_412])).

tff(c_418,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_438,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_46])).

tff(c_439,plain,(
    '#skF_5' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_438])).

tff(c_417,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_466,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_439,c_417,c_42])).

tff(c_467,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_466])).

tff(c_470,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_467])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_470])).

tff(c_476,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_40,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_478,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_10' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_40])).

tff(c_479,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_479])).

tff(c_490,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_475,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_36,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_595,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_476,c_490,c_475,c_36])).

tff(c_598,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_595])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.28  
% 2.31/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.28  %$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.31/1.28  
% 2.31/1.28  %Foreground sorts:
% 2.31/1.28  
% 2.31/1.28  
% 2.31/1.28  %Background operators:
% 2.31/1.28  
% 2.31/1.28  
% 2.31/1.28  %Foreground operators:
% 2.31/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.28  tff('#skF_10', type, '#skF_10': $i).
% 2.31/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.28  tff('#skF_9', type, '#skF_9': $i).
% 2.31/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.28  
% 2.31/1.30  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.31/1.30  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.31/1.30  tff(f_47, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.31/1.30  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.31/1.30  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.31/1.30  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.31/1.30  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.31/1.30  tff(c_56, plain, (![D_17, B_18]: (r2_hidden(D_17, k2_tarski(D_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.31/1.30  tff(c_59, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_56])).
% 2.31/1.30  tff(c_26, plain, (![A_10, B_11, C_12, D_13]: (r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, D_13)) | ~r2_hidden(B_11, D_13) | ~r2_hidden(A_10, C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.31/1.30  tff(c_46, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.30  tff(c_162, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_46])).
% 2.31/1.30  tff(c_38, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.30  tff(c_66, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_38])).
% 2.31/1.30  tff(c_44, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.30  tff(c_82, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_44])).
% 2.31/1.30  tff(c_144, plain, (![A_36, C_37, B_38, D_39]: (r2_hidden(A_36, C_37) | ~r2_hidden(k4_tarski(A_36, B_38), k2_zfmisc_1(C_37, D_39)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.31/1.30  tff(c_148, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_82, c_144])).
% 2.31/1.30  tff(c_34, plain, (![A_14, B_15]: (k4_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k1_tarski(A_14) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.30  tff(c_105, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | k4_xboole_0(k1_tarski(A_30), B_31)!=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.30  tff(c_109, plain, (![A_14, B_15]: (~r2_hidden(A_14, k1_tarski(B_15)) | B_15=A_14)), inference(superposition, [status(thm), theory('equality')], [c_34, c_105])).
% 2.31/1.30  tff(c_151, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_148, c_109])).
% 2.31/1.30  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_151])).
% 2.31/1.30  tff(c_157, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_44])).
% 2.31/1.30  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_157])).
% 2.31/1.30  tff(c_227, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_46])).
% 2.31/1.30  tff(c_226, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 2.31/1.30  tff(c_156, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 2.31/1.30  tff(c_42, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.30  tff(c_309, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_156, c_42])).
% 2.31/1.30  tff(c_310, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_227, c_309])).
% 2.31/1.30  tff(c_313, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_310])).
% 2.31/1.30  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_313])).
% 2.31/1.30  tff(c_319, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_38])).
% 2.31/1.30  tff(c_318, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 2.31/1.30  tff(c_324, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_318])).
% 2.31/1.30  tff(c_388, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_44])).
% 2.31/1.30  tff(c_389, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_388])).
% 2.31/1.30  tff(c_405, plain, (![B_86, D_87, A_88, C_89]: (r2_hidden(B_86, D_87) | ~r2_hidden(k4_tarski(A_88, B_86), k2_zfmisc_1(C_89, D_87)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.31/1.30  tff(c_409, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_389, c_405])).
% 2.31/1.30  tff(c_390, plain, (![A_82, B_83]: (~r2_hidden(A_82, B_83) | k4_xboole_0(k1_tarski(A_82), B_83)!=k1_tarski(A_82))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.30  tff(c_398, plain, (![A_14, B_15]: (~r2_hidden(A_14, k1_tarski(B_15)) | B_15=A_14)), inference(superposition, [status(thm), theory('equality')], [c_34, c_390])).
% 2.31/1.30  tff(c_412, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_409, c_398])).
% 2.31/1.30  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_324, c_412])).
% 2.31/1.30  tff(c_418, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_388])).
% 2.31/1.30  tff(c_438, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_46])).
% 2.31/1.30  tff(c_439, plain, ('#skF_5'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_418, c_438])).
% 2.31/1.30  tff(c_417, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_388])).
% 2.31/1.30  tff(c_466, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_439, c_417, c_42])).
% 2.31/1.30  tff(c_467, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_418, c_466])).
% 2.31/1.30  tff(c_470, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_467])).
% 2.31/1.30  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_470])).
% 2.31/1.30  tff(c_476, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_318])).
% 2.31/1.30  tff(c_40, plain, ('#skF_5'='#skF_3' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.30  tff(c_478, plain, ('#skF_5'='#skF_3' | '#skF_10'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_319, c_40])).
% 2.31/1.30  tff(c_479, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_478])).
% 2.31/1.30  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_476, c_479])).
% 2.31/1.30  tff(c_490, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_478])).
% 2.31/1.30  tff(c_475, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_318])).
% 2.31/1.30  tff(c_36, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.30  tff(c_595, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_476, c_490, c_475, c_36])).
% 2.31/1.30  tff(c_598, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_595])).
% 2.31/1.30  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_598])).
% 2.31/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.30  
% 2.31/1.30  Inference rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Ref     : 0
% 2.31/1.30  #Sup     : 111
% 2.31/1.30  #Fact    : 0
% 2.31/1.30  #Define  : 0
% 2.31/1.30  #Split   : 6
% 2.31/1.30  #Chain   : 0
% 2.31/1.30  #Close   : 0
% 2.31/1.30  
% 2.31/1.30  Ordering : KBO
% 2.31/1.30  
% 2.31/1.30  Simplification rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Subsume      : 11
% 2.31/1.30  #Demod        : 40
% 2.31/1.30  #Tautology    : 95
% 2.31/1.30  #SimpNegUnit  : 5
% 2.31/1.30  #BackRed      : 0
% 2.31/1.30  
% 2.31/1.30  #Partial instantiations: 0
% 2.31/1.30  #Strategies tried      : 1
% 2.31/1.30  
% 2.31/1.30  Timing (in seconds)
% 2.31/1.30  ----------------------
% 2.31/1.30  Preprocessing        : 0.29
% 2.31/1.30  Parsing              : 0.14
% 2.31/1.30  CNF conversion       : 0.02
% 2.31/1.30  Main loop            : 0.25
% 2.31/1.30  Inferencing          : 0.10
% 2.31/1.30  Reduction            : 0.07
% 2.31/1.30  Demodulation         : 0.05
% 2.31/1.30  BG Simplification    : 0.02
% 2.31/1.30  Subsumption          : 0.04
% 2.31/1.30  Abstraction          : 0.01
% 2.31/1.30  MUC search           : 0.00
% 2.31/1.30  Cooper               : 0.00
% 2.31/1.30  Total                : 0.57
% 2.31/1.30  Index Insertion      : 0.00
% 2.31/1.30  Index Deletion       : 0.00
% 2.31/1.30  Index Matching       : 0.00
% 2.31/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
