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
% DateTime   : Thu Dec  3 10:09:26 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 188 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 341 expanded)
%              Number of equality atoms :   78 ( 337 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
       => ( A = E
          & B = F
          & C = G
          & D = H ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k2_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

tff(c_22,plain,
    ( '#skF_8' != '#skF_12'
    | '#skF_11' != '#skF_7'
    | '#skF_10' != '#skF_6'
    | '#skF_5' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_25,plain,(
    '#skF_5' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [C_24,D_25,B_17,C_18] :
      ( k1_mcart_1(k4_tarski(C_24,D_25)) = C_24
      | k4_tarski(C_24,D_25) != k4_tarski(B_17,C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_129,plain,(
    ! [B_17,C_18] : k1_mcart_1(k4_tarski(B_17,C_18)) = B_17 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6])).

tff(c_18,plain,(
    ! [A_47,B_48,C_49] : k4_tarski(k4_tarski(A_47,B_48),C_49) = k3_mcart_1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    ! [B_98,C_99] : k1_mcart_1(k4_tarski(B_98,C_99)) = B_98 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6])).

tff(c_160,plain,(
    ! [A_47,B_48,C_49] : k1_mcart_1(k3_mcart_1(A_47,B_48,C_49)) = k4_tarski(A_47,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_148])).

tff(c_20,plain,(
    ! [A_50,B_51,C_52,D_53] : k4_tarski(k3_mcart_1(A_50,B_51,C_52),D_53) = k4_mcart_1(A_50,B_51,C_52,D_53) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_157,plain,(
    ! [A_50,B_51,C_52,D_53] : k1_mcart_1(k4_mcart_1(A_50,B_51,C_52,D_53)) = k3_mcart_1(A_50,B_51,C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_148])).

tff(c_24,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_180,plain,(
    ! [A_109,B_110,C_111,D_112] : k1_mcart_1(k4_mcart_1(A_109,B_110,C_111,D_112)) = k3_mcart_1(A_109,B_110,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_148])).

tff(c_189,plain,(
    k1_mcart_1(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12')) = k3_mcart_1('#skF_5','#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_180])).

tff(c_192,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_7') = k3_mcart_1('#skF_9','#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_189])).

tff(c_196,plain,(
    k1_mcart_1(k3_mcart_1('#skF_9','#skF_10','#skF_11')) = k4_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_160])).

tff(c_211,plain,(
    k4_tarski('#skF_5','#skF_6') = k4_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_196])).

tff(c_220,plain,(
    k1_mcart_1(k4_tarski('#skF_9','#skF_10')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_129])).

tff(c_240,plain,(
    '#skF_5' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_220])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_240])).

tff(c_243,plain,
    ( '#skF_10' != '#skF_6'
    | '#skF_11' != '#skF_7'
    | '#skF_8' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_249,plain,(
    '#skF_8' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_244,plain,(
    '#skF_5' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_287,plain,(
    k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12') = k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_24])).

tff(c_345,plain,(
    ! [A_155,B_156,C_157,D_158] : k4_tarski(k3_mcart_1(A_155,B_156,C_157),D_158) = k4_mcart_1(A_155,B_156,C_157,D_158) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [C_45,D_46,B_38,C_39] :
      ( k2_mcart_1(k4_tarski(C_45,D_46)) = D_46
      | k4_tarski(C_45,D_46) != k4_tarski(B_38,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_303,plain,(
    ! [B_38,C_39] : k2_mcart_1(k4_tarski(B_38,C_39)) = C_39 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12])).

tff(c_398,plain,(
    ! [A_161,B_162,C_163,D_164] : k2_mcart_1(k4_mcart_1(A_161,B_162,C_163,D_164)) = D_164 ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_303])).

tff(c_407,plain,(
    k2_mcart_1(k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_8')) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_398])).

tff(c_357,plain,(
    ! [A_155,B_156,C_157,D_158] : k2_mcart_1(k4_mcart_1(A_155,B_156,C_157,D_158)) = D_158 ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_303])).

tff(c_413,plain,(
    '#skF_8' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_357])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_413])).

tff(c_421,plain,
    ( '#skF_11' != '#skF_7'
    | '#skF_10' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_427,plain,(
    '#skF_10' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_481,plain,(
    ! [B_38,C_39] : k2_mcart_1(k4_tarski(B_38,C_39)) = C_39 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12])).

tff(c_588,plain,(
    ! [B_226,C_227] : k1_mcart_1(k4_tarski(B_226,C_227)) = B_226 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6])).

tff(c_600,plain,(
    ! [A_47,B_48,C_49] : k1_mcart_1(k3_mcart_1(A_47,B_48,C_49)) = k4_tarski(A_47,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_588])).

tff(c_597,plain,(
    ! [A_50,B_51,C_52,D_53] : k1_mcart_1(k4_mcart_1(A_50,B_51,C_52,D_53)) = k3_mcart_1(A_50,B_51,C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_588])).

tff(c_422,plain,(
    '#skF_8' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_465,plain,(
    k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12') = k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_244,c_24])).

tff(c_620,plain,(
    ! [A_234,B_235,C_236,D_237] : k1_mcart_1(k4_mcart_1(A_234,B_235,C_236,D_237)) = k3_mcart_1(A_234,B_235,C_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_588])).

tff(c_629,plain,(
    k1_mcart_1(k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12')) = k3_mcart_1('#skF_9','#skF_10','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_620])).

tff(c_632,plain,(
    k3_mcart_1('#skF_9','#skF_10','#skF_11') = k3_mcart_1('#skF_9','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_629])).

tff(c_636,plain,(
    k1_mcart_1(k3_mcart_1('#skF_9','#skF_6','#skF_7')) = k4_tarski('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_600])).

tff(c_657,plain,(
    k4_tarski('#skF_9','#skF_10') = k4_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_636])).

tff(c_681,plain,(
    k2_mcart_1(k4_tarski('#skF_9','#skF_6')) = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_481])).

tff(c_700,plain,(
    '#skF_10' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_681])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_700])).

tff(c_703,plain,(
    '#skF_11' != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_769,plain,(
    ! [B_265,C_266] : k2_mcart_1(k4_tarski(B_265,C_266)) = C_266 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12])).

tff(c_778,plain,(
    ! [A_47,B_48,C_49] : k2_mcart_1(k3_mcart_1(A_47,B_48,C_49)) = C_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_769])).

tff(c_833,plain,(
    ! [B_278,C_279] : k1_mcart_1(k4_tarski(B_278,C_279)) = B_278 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6])).

tff(c_842,plain,(
    ! [A_50,B_51,C_52,D_53] : k1_mcart_1(k4_mcart_1(A_50,B_51,C_52,D_53)) = k3_mcart_1(A_50,B_51,C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_833])).

tff(c_704,plain,(
    '#skF_10' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_750,plain,(
    k4_mcart_1('#skF_9','#skF_6','#skF_11','#skF_12') = k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_244,c_422,c_24])).

tff(c_888,plain,(
    ! [A_296,B_297,C_298,D_299] : k1_mcart_1(k4_mcart_1(A_296,B_297,C_298,D_299)) = k3_mcart_1(A_296,B_297,C_298) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_833])).

tff(c_897,plain,(
    k1_mcart_1(k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12')) = k3_mcart_1('#skF_9','#skF_6','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_888])).

tff(c_900,plain,(
    k3_mcart_1('#skF_9','#skF_6','#skF_11') = k3_mcart_1('#skF_9','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_897])).

tff(c_910,plain,(
    k2_mcart_1(k3_mcart_1('#skF_9','#skF_6','#skF_7')) = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_778])).

tff(c_924,plain,(
    '#skF_11' = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_910])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_924])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.53  
% 2.77/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.53  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12 > #skF_4
% 2.77/1.53  
% 2.77/1.53  %Foreground sorts:
% 2.77/1.53  
% 2.77/1.53  
% 2.77/1.53  %Background operators:
% 2.77/1.53  
% 2.77/1.53  
% 2.77/1.53  %Foreground operators:
% 2.77/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.53  tff('#skF_11', type, '#skF_11': $i).
% 2.77/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.53  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.77/1.53  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.53  tff('#skF_10', type, '#skF_10': $i).
% 2.77/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.53  tff('#skF_9', type, '#skF_9': $i).
% 2.77/1.53  tff('#skF_8', type, '#skF_8': $i).
% 2.77/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.53  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.77/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.53  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.77/1.53  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.77/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.53  tff('#skF_12', type, '#skF_12': $i).
% 2.77/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.77/1.53  
% 2.98/1.54  tff(f_68, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_mcart_1)).
% 2.98/1.54  tff(f_42, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k1_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_mcart_1)).
% 2.98/1.54  tff(f_55, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.98/1.54  tff(f_57, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.98/1.54  tff(f_53, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k2_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_mcart_1)).
% 2.98/1.54  tff(c_22, plain, ('#skF_8'!='#skF_12' | '#skF_11'!='#skF_7' | '#skF_10'!='#skF_6' | '#skF_5'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.54  tff(c_25, plain, ('#skF_5'!='#skF_9'), inference(splitLeft, [status(thm)], [c_22])).
% 2.98/1.54  tff(c_6, plain, (![C_24, D_25, B_17, C_18]: (k1_mcart_1(k4_tarski(C_24, D_25))=C_24 | k4_tarski(C_24, D_25)!=k4_tarski(B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.98/1.54  tff(c_129, plain, (![B_17, C_18]: (k1_mcart_1(k4_tarski(B_17, C_18))=B_17)), inference(reflexivity, [status(thm), theory('equality')], [c_6])).
% 2.98/1.54  tff(c_18, plain, (![A_47, B_48, C_49]: (k4_tarski(k4_tarski(A_47, B_48), C_49)=k3_mcart_1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.98/1.54  tff(c_148, plain, (![B_98, C_99]: (k1_mcart_1(k4_tarski(B_98, C_99))=B_98)), inference(reflexivity, [status(thm), theory('equality')], [c_6])).
% 2.98/1.54  tff(c_160, plain, (![A_47, B_48, C_49]: (k1_mcart_1(k3_mcart_1(A_47, B_48, C_49))=k4_tarski(A_47, B_48))), inference(superposition, [status(thm), theory('equality')], [c_18, c_148])).
% 2.98/1.54  tff(c_20, plain, (![A_50, B_51, C_52, D_53]: (k4_tarski(k3_mcart_1(A_50, B_51, C_52), D_53)=k4_mcart_1(A_50, B_51, C_52, D_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.98/1.54  tff(c_157, plain, (![A_50, B_51, C_52, D_53]: (k1_mcart_1(k4_mcart_1(A_50, B_51, C_52, D_53))=k3_mcart_1(A_50, B_51, C_52))), inference(superposition, [status(thm), theory('equality')], [c_20, c_148])).
% 2.98/1.54  tff(c_24, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.54  tff(c_180, plain, (![A_109, B_110, C_111, D_112]: (k1_mcart_1(k4_mcart_1(A_109, B_110, C_111, D_112))=k3_mcart_1(A_109, B_110, C_111))), inference(superposition, [status(thm), theory('equality')], [c_20, c_148])).
% 2.98/1.54  tff(c_189, plain, (k1_mcart_1(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'))=k3_mcart_1('#skF_5', '#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_24, c_180])).
% 2.98/1.54  tff(c_192, plain, (k3_mcart_1('#skF_5', '#skF_6', '#skF_7')=k3_mcart_1('#skF_9', '#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_189])).
% 2.98/1.54  tff(c_196, plain, (k1_mcart_1(k3_mcart_1('#skF_9', '#skF_10', '#skF_11'))=k4_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_192, c_160])).
% 2.98/1.54  tff(c_211, plain, (k4_tarski('#skF_5', '#skF_6')=k4_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_196])).
% 2.98/1.54  tff(c_220, plain, (k1_mcart_1(k4_tarski('#skF_9', '#skF_10'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_211, c_129])).
% 2.98/1.54  tff(c_240, plain, ('#skF_5'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_220])).
% 2.98/1.54  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_240])).
% 2.98/1.54  tff(c_243, plain, ('#skF_10'!='#skF_6' | '#skF_11'!='#skF_7' | '#skF_8'!='#skF_12'), inference(splitRight, [status(thm)], [c_22])).
% 2.98/1.54  tff(c_249, plain, ('#skF_8'!='#skF_12'), inference(splitLeft, [status(thm)], [c_243])).
% 2.98/1.54  tff(c_244, plain, ('#skF_5'='#skF_9'), inference(splitRight, [status(thm)], [c_22])).
% 2.98/1.54  tff(c_287, plain, (k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')=k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_24])).
% 2.98/1.54  tff(c_345, plain, (![A_155, B_156, C_157, D_158]: (k4_tarski(k3_mcart_1(A_155, B_156, C_157), D_158)=k4_mcart_1(A_155, B_156, C_157, D_158))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.98/1.54  tff(c_12, plain, (![C_45, D_46, B_38, C_39]: (k2_mcart_1(k4_tarski(C_45, D_46))=D_46 | k4_tarski(C_45, D_46)!=k4_tarski(B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.98/1.54  tff(c_303, plain, (![B_38, C_39]: (k2_mcart_1(k4_tarski(B_38, C_39))=C_39)), inference(reflexivity, [status(thm), theory('equality')], [c_12])).
% 2.98/1.54  tff(c_398, plain, (![A_161, B_162, C_163, D_164]: (k2_mcart_1(k4_mcart_1(A_161, B_162, C_163, D_164))=D_164)), inference(superposition, [status(thm), theory('equality')], [c_345, c_303])).
% 2.98/1.54  tff(c_407, plain, (k2_mcart_1(k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_8'))='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_287, c_398])).
% 2.98/1.54  tff(c_357, plain, (![A_155, B_156, C_157, D_158]: (k2_mcart_1(k4_mcart_1(A_155, B_156, C_157, D_158))=D_158)), inference(superposition, [status(thm), theory('equality')], [c_345, c_303])).
% 2.98/1.54  tff(c_413, plain, ('#skF_8'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_407, c_357])).
% 2.98/1.54  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_413])).
% 2.98/1.54  tff(c_421, plain, ('#skF_11'!='#skF_7' | '#skF_10'!='#skF_6'), inference(splitRight, [status(thm)], [c_243])).
% 2.98/1.54  tff(c_427, plain, ('#skF_10'!='#skF_6'), inference(splitLeft, [status(thm)], [c_421])).
% 2.98/1.54  tff(c_481, plain, (![B_38, C_39]: (k2_mcart_1(k4_tarski(B_38, C_39))=C_39)), inference(reflexivity, [status(thm), theory('equality')], [c_12])).
% 2.98/1.54  tff(c_588, plain, (![B_226, C_227]: (k1_mcart_1(k4_tarski(B_226, C_227))=B_226)), inference(reflexivity, [status(thm), theory('equality')], [c_6])).
% 2.98/1.54  tff(c_600, plain, (![A_47, B_48, C_49]: (k1_mcart_1(k3_mcart_1(A_47, B_48, C_49))=k4_tarski(A_47, B_48))), inference(superposition, [status(thm), theory('equality')], [c_18, c_588])).
% 2.98/1.54  tff(c_597, plain, (![A_50, B_51, C_52, D_53]: (k1_mcart_1(k4_mcart_1(A_50, B_51, C_52, D_53))=k3_mcart_1(A_50, B_51, C_52))), inference(superposition, [status(thm), theory('equality')], [c_20, c_588])).
% 2.98/1.54  tff(c_422, plain, ('#skF_8'='#skF_12'), inference(splitRight, [status(thm)], [c_243])).
% 2.98/1.54  tff(c_465, plain, (k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')=k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_244, c_24])).
% 2.98/1.54  tff(c_620, plain, (![A_234, B_235, C_236, D_237]: (k1_mcart_1(k4_mcart_1(A_234, B_235, C_236, D_237))=k3_mcart_1(A_234, B_235, C_236))), inference(superposition, [status(thm), theory('equality')], [c_20, c_588])).
% 2.98/1.54  tff(c_629, plain, (k1_mcart_1(k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12'))=k3_mcart_1('#skF_9', '#skF_10', '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_465, c_620])).
% 2.98/1.54  tff(c_632, plain, (k3_mcart_1('#skF_9', '#skF_10', '#skF_11')=k3_mcart_1('#skF_9', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_629])).
% 2.98/1.54  tff(c_636, plain, (k1_mcart_1(k3_mcart_1('#skF_9', '#skF_6', '#skF_7'))=k4_tarski('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_632, c_600])).
% 2.98/1.54  tff(c_657, plain, (k4_tarski('#skF_9', '#skF_10')=k4_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_636])).
% 2.98/1.54  tff(c_681, plain, (k2_mcart_1(k4_tarski('#skF_9', '#skF_6'))='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_657, c_481])).
% 2.98/1.54  tff(c_700, plain, ('#skF_10'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_681])).
% 2.98/1.54  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_700])).
% 2.98/1.54  tff(c_703, plain, ('#skF_11'!='#skF_7'), inference(splitRight, [status(thm)], [c_421])).
% 2.98/1.54  tff(c_769, plain, (![B_265, C_266]: (k2_mcart_1(k4_tarski(B_265, C_266))=C_266)), inference(reflexivity, [status(thm), theory('equality')], [c_12])).
% 2.98/1.54  tff(c_778, plain, (![A_47, B_48, C_49]: (k2_mcart_1(k3_mcart_1(A_47, B_48, C_49))=C_49)), inference(superposition, [status(thm), theory('equality')], [c_18, c_769])).
% 2.98/1.54  tff(c_833, plain, (![B_278, C_279]: (k1_mcart_1(k4_tarski(B_278, C_279))=B_278)), inference(reflexivity, [status(thm), theory('equality')], [c_6])).
% 2.98/1.54  tff(c_842, plain, (![A_50, B_51, C_52, D_53]: (k1_mcart_1(k4_mcart_1(A_50, B_51, C_52, D_53))=k3_mcart_1(A_50, B_51, C_52))), inference(superposition, [status(thm), theory('equality')], [c_20, c_833])).
% 2.98/1.54  tff(c_704, plain, ('#skF_10'='#skF_6'), inference(splitRight, [status(thm)], [c_421])).
% 2.98/1.54  tff(c_750, plain, (k4_mcart_1('#skF_9', '#skF_6', '#skF_11', '#skF_12')=k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_704, c_244, c_422, c_24])).
% 2.98/1.54  tff(c_888, plain, (![A_296, B_297, C_298, D_299]: (k1_mcart_1(k4_mcart_1(A_296, B_297, C_298, D_299))=k3_mcart_1(A_296, B_297, C_298))), inference(superposition, [status(thm), theory('equality')], [c_20, c_833])).
% 2.98/1.54  tff(c_897, plain, (k1_mcart_1(k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12'))=k3_mcart_1('#skF_9', '#skF_6', '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_750, c_888])).
% 2.98/1.54  tff(c_900, plain, (k3_mcart_1('#skF_9', '#skF_6', '#skF_11')=k3_mcart_1('#skF_9', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_842, c_897])).
% 2.98/1.54  tff(c_910, plain, (k2_mcart_1(k3_mcart_1('#skF_9', '#skF_6', '#skF_7'))='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_900, c_778])).
% 2.98/1.54  tff(c_924, plain, ('#skF_11'='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_910])).
% 2.98/1.54  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_703, c_924])).
% 2.98/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.54  
% 2.98/1.54  Inference rules
% 2.98/1.54  ----------------------
% 2.98/1.54  #Ref     : 19
% 2.98/1.54  #Sup     : 239
% 2.98/1.54  #Fact    : 0
% 2.98/1.54  #Define  : 0
% 2.98/1.54  #Split   : 3
% 2.98/1.54  #Chain   : 0
% 2.98/1.54  #Close   : 0
% 2.98/1.54  
% 2.98/1.54  Ordering : KBO
% 2.98/1.54  
% 2.98/1.54  Simplification rules
% 2.98/1.54  ----------------------
% 2.98/1.54  #Subsume      : 12
% 2.98/1.54  #Demod        : 52
% 2.98/1.54  #Tautology    : 101
% 2.98/1.54  #SimpNegUnit  : 4
% 2.98/1.54  #BackRed      : 4
% 2.98/1.54  
% 2.98/1.54  #Partial instantiations: 0
% 2.98/1.54  #Strategies tried      : 1
% 2.98/1.54  
% 2.98/1.54  Timing (in seconds)
% 2.98/1.54  ----------------------
% 2.98/1.55  Preprocessing        : 0.30
% 2.98/1.55  Parsing              : 0.15
% 2.98/1.55  CNF conversion       : 0.02
% 2.98/1.55  Main loop            : 0.43
% 2.98/1.55  Inferencing          : 0.16
% 2.98/1.55  Reduction            : 0.12
% 2.98/1.55  Demodulation         : 0.09
% 2.98/1.55  BG Simplification    : 0.02
% 2.98/1.55  Subsumption          : 0.08
% 2.98/1.55  Abstraction          : 0.03
% 2.98/1.55  MUC search           : 0.00
% 2.98/1.55  Cooper               : 0.00
% 2.98/1.55  Total                : 0.77
% 2.98/1.55  Index Insertion      : 0.00
% 2.98/1.55  Index Deletion       : 0.00
% 2.98/1.55  Index Matching       : 0.00
% 2.98/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
