%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:26 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 261 expanded)
%              Number of leaves         :   23 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :   89 ( 495 expanded)
%              Number of equality atoms :   85 ( 491 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
       => ( A = E
          & B = F
          & C = G
          & D = H ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k2_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

tff(c_16,plain,
    ( '#skF_8' != '#skF_12'
    | '#skF_11' != '#skF_7'
    | '#skF_10' != '#skF_6'
    | '#skF_5' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_19,plain,(
    '#skF_5' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_2,plain,(
    ! [C_20,D_21,B_13,C_14] :
      ( k1_mcart_1(k4_tarski(C_20,D_21)) = C_20
      | k4_tarski(C_20,D_21) != k4_tarski(B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_27,plain,(
    ! [B_13,C_14] : k1_mcart_1(k4_tarski(B_13,C_14)) = B_13 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_57,plain,(
    ! [A_68,B_69,C_70,D_71] : k4_tarski(k4_tarski(k4_tarski(A_68,B_69),C_70),D_71) = k4_mcart_1(A_68,B_69,C_70,D_71) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_213,plain,(
    ! [A_90,B_91,C_92,D_93] : k4_tarski(k4_tarski(A_90,B_91),C_92) = k1_mcart_1(k4_mcart_1(A_90,B_91,C_92,D_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_27])).

tff(c_256,plain,(
    ! [A_90,B_91,C_92,D_93] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_90,B_91,C_92,D_93))) = k4_tarski(A_90,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_27])).

tff(c_8,plain,(
    ! [C_41,D_42,B_34,C_35] :
      ( k2_mcart_1(k4_tarski(C_41,D_42)) = D_42
      | k4_tarski(C_41,D_42) != k4_tarski(B_34,C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) = C_35 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_75,plain,(
    ! [A_68,B_69,C_70,D_71] : k2_mcart_1(k4_mcart_1(A_68,B_69,C_70,D_71)) = D_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_31])).

tff(c_18,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    ! [A_72,B_73,C_74,D_75] : k2_mcart_1(k4_mcart_1(A_72,B_73,C_74,D_75)) = D_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_31])).

tff(c_99,plain,(
    k2_mcart_1(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_90])).

tff(c_102,plain,(
    '#skF_8' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_99])).

tff(c_103,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_12') = k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_409,plain,(
    ! [A_103,B_104,C_105,D_106] : k2_mcart_1(k1_mcart_1(k4_mcart_1(A_103,B_104,C_105,D_106))) = C_105 ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_31])).

tff(c_421,plain,(
    k2_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'))) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_409])).

tff(c_253,plain,(
    ! [A_90,B_91,C_92,D_93] : k2_mcart_1(k1_mcart_1(k4_mcart_1(A_90,B_91,C_92,D_93))) = C_92 ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_31])).

tff(c_428,plain,(
    '#skF_11' = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_253])).

tff(c_436,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_12') = k4_mcart_1('#skF_9','#skF_10','#skF_7','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_103])).

tff(c_524,plain,(
    k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9','#skF_10','#skF_7','#skF_12'))) = k4_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_256])).

tff(c_536,plain,(
    k4_tarski('#skF_5','#skF_6') = k4_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_524])).

tff(c_585,plain,(
    k1_mcart_1(k4_tarski('#skF_9','#skF_10')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_27])).

tff(c_594,plain,(
    '#skF_5' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_585])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_594])).

tff(c_597,plain,
    ( '#skF_10' != '#skF_6'
    | '#skF_11' != '#skF_7'
    | '#skF_8' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_603,plain,(
    '#skF_8' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_598,plain,(
    '#skF_5' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_604,plain,(
    k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12') = k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_18])).

tff(c_642,plain,(
    ! [A_142,B_143,C_144,D_145] : k4_tarski(k4_tarski(k4_tarski(A_142,B_143),C_144),D_145) = k4_mcart_1(A_142,B_143,C_144,D_145) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_628,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) = C_35 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_675,plain,(
    ! [A_146,B_147,C_148,D_149] : k2_mcart_1(k4_mcart_1(A_146,B_147,C_148,D_149)) = D_149 ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_628])).

tff(c_684,plain,(
    k2_mcart_1(k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_8')) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_675])).

tff(c_657,plain,(
    ! [A_142,B_143,C_144,D_145] : k2_mcart_1(k4_mcart_1(A_142,B_143,C_144,D_145)) = D_145 ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_628])).

tff(c_690,plain,(
    '#skF_8' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_657])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_603,c_690])).

tff(c_698,plain,
    ( '#skF_11' != '#skF_7'
    | '#skF_10' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_704,plain,(
    '#skF_10' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_698])).

tff(c_712,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) = C_35 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_742,plain,(
    ! [A_168,B_169,C_170,D_171] : k4_tarski(k4_tarski(k4_tarski(A_168,B_169),C_170),D_171) = k4_mcart_1(A_168,B_169,C_170,D_171) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_726,plain,(
    ! [B_13,C_14] : k1_mcart_1(k4_tarski(B_13,C_14)) = B_13 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_792,plain,(
    ! [A_181,B_182,C_183,D_184] : k4_tarski(k4_tarski(A_181,B_182),C_183) = k1_mcart_1(k4_mcart_1(A_181,B_182,C_183,D_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_726])).

tff(c_820,plain,(
    ! [A_181,B_182,C_183,D_184] : k1_mcart_1(k1_mcart_1(k4_mcart_1(A_181,B_182,C_183,D_184))) = k4_tarski(A_181,B_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_726])).

tff(c_823,plain,(
    ! [A_181,B_182,C_183,D_184] : k2_mcart_1(k1_mcart_1(k4_mcart_1(A_181,B_182,C_183,D_184))) = C_183 ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_712])).

tff(c_699,plain,(
    '#skF_8' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_705,plain,(
    k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12') = k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_598,c_18])).

tff(c_949,plain,(
    ! [A_194,B_195,C_196,D_197] : k2_mcart_1(k1_mcart_1(k4_mcart_1(A_194,B_195,C_196,D_197))) = C_196 ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_712])).

tff(c_961,plain,(
    k2_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12'))) = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_949])).

tff(c_965,plain,(
    '#skF_11' = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_961])).

tff(c_966,plain,(
    k4_mcart_1('#skF_9','#skF_10','#skF_7','#skF_12') = k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_705])).

tff(c_1137,plain,(
    k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12'))) = k4_tarski('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_820])).

tff(c_1149,plain,(
    k4_tarski('#skF_9','#skF_10') = k4_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_1137])).

tff(c_1195,plain,(
    k2_mcart_1(k4_tarski('#skF_9','#skF_6')) = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_712])).

tff(c_1204,plain,(
    '#skF_10' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_1195])).

tff(c_1206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_1204])).

tff(c_1207,plain,(
    '#skF_11' != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_14,plain,(
    ! [A_43,B_44,C_45,D_46] : k4_tarski(k4_tarski(k4_tarski(A_43,B_44),C_45),D_46) = k4_mcart_1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1275,plain,(
    ! [B_236,C_237] : k1_mcart_1(k4_tarski(B_236,C_237)) = B_236 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_1308,plain,(
    ! [A_250,B_251,C_252,D_253] : k4_tarski(k4_tarski(A_250,B_251),C_252) = k1_mcart_1(k4_mcart_1(A_250,B_251,C_252,D_253)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1275])).

tff(c_1220,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) = C_35 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_1339,plain,(
    ! [A_250,B_251,C_252,D_253] : k2_mcart_1(k1_mcart_1(k4_mcart_1(A_250,B_251,C_252,D_253))) = C_252 ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_1220])).

tff(c_1208,plain,(
    '#skF_10' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_1213,plain,(
    k4_mcart_1('#skF_9','#skF_6','#skF_11','#skF_12') = k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_598,c_699,c_18])).

tff(c_1465,plain,(
    ! [A_263,B_264,C_265,D_266] : k2_mcart_1(k1_mcart_1(k4_mcart_1(A_263,B_264,C_265,D_266))) = C_265 ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_1220])).

tff(c_1477,plain,(
    k2_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9','#skF_6','#skF_7','#skF_12'))) = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_1465])).

tff(c_1481,plain,(
    '#skF_11' = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_1477])).

tff(c_1483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1207,c_1481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.56  
% 3.24/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.56  %$ k4_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12 > #skF_4
% 3.24/1.56  
% 3.24/1.56  %Foreground sorts:
% 3.24/1.56  
% 3.24/1.56  
% 3.24/1.56  %Background operators:
% 3.24/1.56  
% 3.24/1.56  
% 3.24/1.56  %Foreground operators:
% 3.24/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.56  tff('#skF_11', type, '#skF_11': $i).
% 3.24/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.24/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.24/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.24/1.56  tff('#skF_10', type, '#skF_10': $i).
% 3.24/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.24/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.24/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.24/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.24/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.24/1.56  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.24/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.24/1.56  tff('#skF_12', type, '#skF_12': $i).
% 3.24/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.24/1.56  
% 3.24/1.58  tff(f_60, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_mcart_1)).
% 3.24/1.58  tff(f_36, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k1_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_mcart_1)).
% 3.24/1.58  tff(f_49, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 3.24/1.58  tff(f_47, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k2_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_mcart_1)).
% 3.24/1.58  tff(c_16, plain, ('#skF_8'!='#skF_12' | '#skF_11'!='#skF_7' | '#skF_10'!='#skF_6' | '#skF_5'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.24/1.58  tff(c_19, plain, ('#skF_5'!='#skF_9'), inference(splitLeft, [status(thm)], [c_16])).
% 3.24/1.58  tff(c_2, plain, (![C_20, D_21, B_13, C_14]: (k1_mcart_1(k4_tarski(C_20, D_21))=C_20 | k4_tarski(C_20, D_21)!=k4_tarski(B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.58  tff(c_27, plain, (![B_13, C_14]: (k1_mcart_1(k4_tarski(B_13, C_14))=B_13)), inference(reflexivity, [status(thm), theory('equality')], [c_2])).
% 3.24/1.58  tff(c_57, plain, (![A_68, B_69, C_70, D_71]: (k4_tarski(k4_tarski(k4_tarski(A_68, B_69), C_70), D_71)=k4_mcart_1(A_68, B_69, C_70, D_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.58  tff(c_213, plain, (![A_90, B_91, C_92, D_93]: (k4_tarski(k4_tarski(A_90, B_91), C_92)=k1_mcart_1(k4_mcart_1(A_90, B_91, C_92, D_93)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_27])).
% 3.24/1.58  tff(c_256, plain, (![A_90, B_91, C_92, D_93]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_90, B_91, C_92, D_93)))=k4_tarski(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_213, c_27])).
% 3.24/1.58  tff(c_8, plain, (![C_41, D_42, B_34, C_35]: (k2_mcart_1(k4_tarski(C_41, D_42))=D_42 | k4_tarski(C_41, D_42)!=k4_tarski(B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.24/1.58  tff(c_31, plain, (![B_34, C_35]: (k2_mcart_1(k4_tarski(B_34, C_35))=C_35)), inference(reflexivity, [status(thm), theory('equality')], [c_8])).
% 3.24/1.58  tff(c_75, plain, (![A_68, B_69, C_70, D_71]: (k2_mcart_1(k4_mcart_1(A_68, B_69, C_70, D_71))=D_71)), inference(superposition, [status(thm), theory('equality')], [c_57, c_31])).
% 3.24/1.58  tff(c_18, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.24/1.58  tff(c_90, plain, (![A_72, B_73, C_74, D_75]: (k2_mcart_1(k4_mcart_1(A_72, B_73, C_74, D_75))=D_75)), inference(superposition, [status(thm), theory('equality')], [c_57, c_31])).
% 3.24/1.58  tff(c_99, plain, (k2_mcart_1(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_18, c_90])).
% 3.24/1.58  tff(c_102, plain, ('#skF_8'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_99])).
% 3.24/1.58  tff(c_103, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_12')=k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_18])).
% 3.24/1.58  tff(c_409, plain, (![A_103, B_104, C_105, D_106]: (k2_mcart_1(k1_mcart_1(k4_mcart_1(A_103, B_104, C_105, D_106)))=C_105)), inference(superposition, [status(thm), theory('equality')], [c_213, c_31])).
% 3.24/1.58  tff(c_421, plain, (k2_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_103, c_409])).
% 3.24/1.58  tff(c_253, plain, (![A_90, B_91, C_92, D_93]: (k2_mcart_1(k1_mcart_1(k4_mcart_1(A_90, B_91, C_92, D_93)))=C_92)), inference(superposition, [status(thm), theory('equality')], [c_213, c_31])).
% 3.24/1.58  tff(c_428, plain, ('#skF_11'='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_421, c_253])).
% 3.24/1.58  tff(c_436, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_12')=k4_mcart_1('#skF_9', '#skF_10', '#skF_7', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_103])).
% 3.24/1.58  tff(c_524, plain, (k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9', '#skF_10', '#skF_7', '#skF_12')))=k4_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_436, c_256])).
% 3.24/1.58  tff(c_536, plain, (k4_tarski('#skF_5', '#skF_6')=k4_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_524])).
% 3.24/1.58  tff(c_585, plain, (k1_mcart_1(k4_tarski('#skF_9', '#skF_10'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_536, c_27])).
% 3.24/1.58  tff(c_594, plain, ('#skF_5'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_27, c_585])).
% 3.24/1.58  tff(c_596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_594])).
% 3.24/1.58  tff(c_597, plain, ('#skF_10'!='#skF_6' | '#skF_11'!='#skF_7' | '#skF_8'!='#skF_12'), inference(splitRight, [status(thm)], [c_16])).
% 3.24/1.58  tff(c_603, plain, ('#skF_8'!='#skF_12'), inference(splitLeft, [status(thm)], [c_597])).
% 3.24/1.58  tff(c_598, plain, ('#skF_5'='#skF_9'), inference(splitRight, [status(thm)], [c_16])).
% 3.24/1.58  tff(c_604, plain, (k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')=k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_598, c_18])).
% 3.24/1.58  tff(c_642, plain, (![A_142, B_143, C_144, D_145]: (k4_tarski(k4_tarski(k4_tarski(A_142, B_143), C_144), D_145)=k4_mcart_1(A_142, B_143, C_144, D_145))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.58  tff(c_628, plain, (![B_34, C_35]: (k2_mcart_1(k4_tarski(B_34, C_35))=C_35)), inference(reflexivity, [status(thm), theory('equality')], [c_8])).
% 3.24/1.58  tff(c_675, plain, (![A_146, B_147, C_148, D_149]: (k2_mcart_1(k4_mcart_1(A_146, B_147, C_148, D_149))=D_149)), inference(superposition, [status(thm), theory('equality')], [c_642, c_628])).
% 3.24/1.58  tff(c_684, plain, (k2_mcart_1(k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_8'))='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_604, c_675])).
% 3.24/1.58  tff(c_657, plain, (![A_142, B_143, C_144, D_145]: (k2_mcart_1(k4_mcart_1(A_142, B_143, C_144, D_145))=D_145)), inference(superposition, [status(thm), theory('equality')], [c_642, c_628])).
% 3.24/1.58  tff(c_690, plain, ('#skF_8'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_684, c_657])).
% 3.24/1.58  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_603, c_690])).
% 3.24/1.58  tff(c_698, plain, ('#skF_11'!='#skF_7' | '#skF_10'!='#skF_6'), inference(splitRight, [status(thm)], [c_597])).
% 3.24/1.58  tff(c_704, plain, ('#skF_10'!='#skF_6'), inference(splitLeft, [status(thm)], [c_698])).
% 3.24/1.58  tff(c_712, plain, (![B_34, C_35]: (k2_mcart_1(k4_tarski(B_34, C_35))=C_35)), inference(reflexivity, [status(thm), theory('equality')], [c_8])).
% 3.24/1.58  tff(c_742, plain, (![A_168, B_169, C_170, D_171]: (k4_tarski(k4_tarski(k4_tarski(A_168, B_169), C_170), D_171)=k4_mcart_1(A_168, B_169, C_170, D_171))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.58  tff(c_726, plain, (![B_13, C_14]: (k1_mcart_1(k4_tarski(B_13, C_14))=B_13)), inference(reflexivity, [status(thm), theory('equality')], [c_2])).
% 3.24/1.58  tff(c_792, plain, (![A_181, B_182, C_183, D_184]: (k4_tarski(k4_tarski(A_181, B_182), C_183)=k1_mcart_1(k4_mcart_1(A_181, B_182, C_183, D_184)))), inference(superposition, [status(thm), theory('equality')], [c_742, c_726])).
% 3.24/1.58  tff(c_820, plain, (![A_181, B_182, C_183, D_184]: (k1_mcart_1(k1_mcart_1(k4_mcart_1(A_181, B_182, C_183, D_184)))=k4_tarski(A_181, B_182))), inference(superposition, [status(thm), theory('equality')], [c_792, c_726])).
% 3.24/1.58  tff(c_823, plain, (![A_181, B_182, C_183, D_184]: (k2_mcart_1(k1_mcart_1(k4_mcart_1(A_181, B_182, C_183, D_184)))=C_183)), inference(superposition, [status(thm), theory('equality')], [c_792, c_712])).
% 3.24/1.58  tff(c_699, plain, ('#skF_8'='#skF_12'), inference(splitRight, [status(thm)], [c_597])).
% 3.24/1.58  tff(c_705, plain, (k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')=k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_598, c_18])).
% 3.24/1.58  tff(c_949, plain, (![A_194, B_195, C_196, D_197]: (k2_mcart_1(k1_mcart_1(k4_mcart_1(A_194, B_195, C_196, D_197)))=C_196)), inference(superposition, [status(thm), theory('equality')], [c_792, c_712])).
% 3.24/1.58  tff(c_961, plain, (k2_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12')))='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_705, c_949])).
% 3.24/1.58  tff(c_965, plain, ('#skF_11'='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_823, c_961])).
% 3.24/1.58  tff(c_966, plain, (k4_mcart_1('#skF_9', '#skF_10', '#skF_7', '#skF_12')=k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_965, c_705])).
% 3.24/1.58  tff(c_1137, plain, (k1_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12')))=k4_tarski('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_966, c_820])).
% 3.24/1.58  tff(c_1149, plain, (k4_tarski('#skF_9', '#skF_10')=k4_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_1137])).
% 3.24/1.58  tff(c_1195, plain, (k2_mcart_1(k4_tarski('#skF_9', '#skF_6'))='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_1149, c_712])).
% 3.24/1.58  tff(c_1204, plain, ('#skF_10'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_712, c_1195])).
% 3.24/1.58  tff(c_1206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_1204])).
% 3.24/1.58  tff(c_1207, plain, ('#skF_11'!='#skF_7'), inference(splitRight, [status(thm)], [c_698])).
% 3.24/1.58  tff(c_14, plain, (![A_43, B_44, C_45, D_46]: (k4_tarski(k4_tarski(k4_tarski(A_43, B_44), C_45), D_46)=k4_mcart_1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.58  tff(c_1275, plain, (![B_236, C_237]: (k1_mcart_1(k4_tarski(B_236, C_237))=B_236)), inference(reflexivity, [status(thm), theory('equality')], [c_2])).
% 3.24/1.58  tff(c_1308, plain, (![A_250, B_251, C_252, D_253]: (k4_tarski(k4_tarski(A_250, B_251), C_252)=k1_mcart_1(k4_mcart_1(A_250, B_251, C_252, D_253)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1275])).
% 3.24/1.58  tff(c_1220, plain, (![B_34, C_35]: (k2_mcart_1(k4_tarski(B_34, C_35))=C_35)), inference(reflexivity, [status(thm), theory('equality')], [c_8])).
% 3.24/1.58  tff(c_1339, plain, (![A_250, B_251, C_252, D_253]: (k2_mcart_1(k1_mcart_1(k4_mcart_1(A_250, B_251, C_252, D_253)))=C_252)), inference(superposition, [status(thm), theory('equality')], [c_1308, c_1220])).
% 3.24/1.58  tff(c_1208, plain, ('#skF_10'='#skF_6'), inference(splitRight, [status(thm)], [c_698])).
% 3.24/1.58  tff(c_1213, plain, (k4_mcart_1('#skF_9', '#skF_6', '#skF_11', '#skF_12')=k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_598, c_699, c_18])).
% 3.24/1.58  tff(c_1465, plain, (![A_263, B_264, C_265, D_266]: (k2_mcart_1(k1_mcart_1(k4_mcart_1(A_263, B_264, C_265, D_266)))=C_265)), inference(superposition, [status(thm), theory('equality')], [c_1308, c_1220])).
% 3.24/1.58  tff(c_1477, plain, (k2_mcart_1(k1_mcart_1(k4_mcart_1('#skF_9', '#skF_6', '#skF_7', '#skF_12')))='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_1213, c_1465])).
% 3.24/1.58  tff(c_1481, plain, ('#skF_11'='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_1477])).
% 3.24/1.58  tff(c_1483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1207, c_1481])).
% 3.24/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.58  
% 3.24/1.58  Inference rules
% 3.24/1.58  ----------------------
% 3.24/1.58  #Ref     : 8
% 3.24/1.58  #Sup     : 394
% 3.24/1.58  #Fact    : 0
% 3.24/1.58  #Define  : 0
% 3.24/1.58  #Split   : 3
% 3.24/1.58  #Chain   : 0
% 3.24/1.58  #Close   : 0
% 3.24/1.58  
% 3.24/1.58  Ordering : KBO
% 3.24/1.58  
% 3.24/1.58  Simplification rules
% 3.24/1.58  ----------------------
% 3.24/1.58  #Subsume      : 14
% 3.24/1.58  #Demod        : 121
% 3.24/1.58  #Tautology    : 149
% 3.24/1.58  #SimpNegUnit  : 4
% 3.24/1.58  #BackRed      : 7
% 3.24/1.58  
% 3.24/1.58  #Partial instantiations: 0
% 3.24/1.58  #Strategies tried      : 1
% 3.24/1.58  
% 3.24/1.58  Timing (in seconds)
% 3.24/1.58  ----------------------
% 3.24/1.58  Preprocessing        : 0.30
% 3.24/1.58  Parsing              : 0.16
% 3.24/1.58  CNF conversion       : 0.02
% 3.24/1.58  Main loop            : 0.46
% 3.24/1.58  Inferencing          : 0.20
% 3.24/1.58  Reduction            : 0.14
% 3.24/1.58  Demodulation         : 0.10
% 3.24/1.58  BG Simplification    : 0.04
% 3.24/1.58  Subsumption          : 0.05
% 3.24/1.58  Abstraction          : 0.04
% 3.24/1.58  MUC search           : 0.00
% 3.24/1.58  Cooper               : 0.00
% 3.24/1.58  Total                : 0.79
% 3.24/1.58  Index Insertion      : 0.00
% 3.24/1.58  Index Deletion       : 0.00
% 3.24/1.58  Index Matching       : 0.00
% 3.24/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
