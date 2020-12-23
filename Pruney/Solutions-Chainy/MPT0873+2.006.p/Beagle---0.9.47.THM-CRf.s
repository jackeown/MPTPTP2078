%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:27 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 229 expanded)
%              Number of leaves         :   20 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 338 expanded)
%              Number of equality atoms :   79 ( 334 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
       => ( A = E
          & B = F
          & C = G
          & D = H ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k3_mcart_1(k4_tarski(A,B),C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).

tff(c_10,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_6,plain,(
    ! [A_8,B_9] : k1_mcart_1(k4_tarski(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [A_14,B_15,C_16] : k4_tarski(k4_tarski(A_14,B_15),C_16) = k3_mcart_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_41,plain,(
    ! [A_14,B_15,C_16] : k1_mcart_1(k3_mcart_1(A_14,B_15,C_16)) = k4_tarski(A_14,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_mcart_1(k4_tarski(A_23,B_24),C_25,D_26) = k4_mcart_1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_23,B_24,C_25,D_26] : k4_tarski(k4_tarski(A_23,B_24),C_25) = k1_mcart_1(k4_mcart_1(A_23,B_24,C_25,D_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_41])).

tff(c_92,plain,(
    ! [A_23,B_24,C_25,D_26] : k1_mcart_1(k4_mcart_1(A_23,B_24,C_25,D_26)) = k3_mcart_1(A_23,B_24,C_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_81])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_mcart_1(k4_tarski(A_8,B_9)) = B_9 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [A_14,B_15,C_16] : k2_mcart_1(k3_mcart_1(A_14,B_15,C_16)) = C_16 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_84,plain,(
    ! [A_23,B_24,C_25,D_26] : k2_mcart_1(k4_mcart_1(A_23,B_24,C_25,D_26)) = D_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_44])).

tff(c_12,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_mcart_1(k4_mcart_1(A_27,B_28,C_29,D_30)) = D_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_44])).

tff(c_103,plain,(
    k2_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_94])).

tff(c_106,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_103])).

tff(c_107,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_12])).

tff(c_124,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_5','#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_92])).

tff(c_130,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_124])).

tff(c_136,plain,(
    k1_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = k4_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_41])).

tff(c_142,plain,(
    k4_tarski('#skF_5','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_136])).

tff(c_187,plain,(
    k1_mcart_1(k4_tarski('#skF_1','#skF_2')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_6])).

tff(c_195,plain,(
    '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_187])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_195])).

tff(c_198,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_204,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_249,plain,(
    ! [A_48,B_49,C_50,D_51] : k3_mcart_1(k4_tarski(A_48,B_49),C_50,D_51) = k4_mcart_1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_210,plain,(
    ! [A_39,B_40,C_41] : k4_tarski(k4_tarski(A_39,B_40),C_41) = k3_mcart_1(A_39,B_40,C_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_222,plain,(
    ! [A_39,B_40,C_41] : k2_mcart_1(k3_mcart_1(A_39,B_40,C_41)) = C_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_8])).

tff(c_258,plain,(
    ! [A_48,B_49,C_50,D_51] : k2_mcart_1(k4_mcart_1(A_48,B_49,C_50,D_51)) = D_51 ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_222])).

tff(c_199,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_205,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_12])).

tff(c_293,plain,(
    ! [A_56,B_57,C_58,D_59] : k2_mcart_1(k4_mcart_1(A_56,B_57,C_58,D_59)) = D_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_222])).

tff(c_302,plain,(
    k2_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_293])).

tff(c_305,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_302])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_305])).

tff(c_308,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_314,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_320,plain,(
    ! [A_60,B_61,C_62] : k4_tarski(k4_tarski(A_60,B_61),C_62) = k3_mcart_1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_329,plain,(
    ! [A_60,B_61,C_62] : k1_mcart_1(k3_mcart_1(A_60,B_61,C_62)) = k4_tarski(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_6])).

tff(c_359,plain,(
    ! [A_69,B_70,C_71,D_72] : k3_mcart_1(k4_tarski(A_69,B_70),C_71,D_72) = k4_mcart_1(A_69,B_70,C_71,D_72) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_365,plain,(
    ! [A_69,B_70,C_71,D_72] : k4_tarski(k4_tarski(A_69,B_70),C_71) = k1_mcart_1(k4_mcart_1(A_69,B_70,C_71,D_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_329])).

tff(c_376,plain,(
    ! [A_69,B_70,C_71,D_72] : k1_mcart_1(k4_mcart_1(A_69,B_70,C_71,D_72)) = k3_mcart_1(A_69,B_70,C_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_365])).

tff(c_309,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_315,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_199,c_12])).

tff(c_417,plain,(
    ! [A_81,B_82,C_83,D_84] : k1_mcart_1(k4_mcart_1(A_81,B_82,C_83,D_84)) = k3_mcart_1(A_81,B_82,C_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_365])).

tff(c_426,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_1','#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_417])).

tff(c_429,plain,(
    k3_mcart_1('#skF_1','#skF_6','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_426])).

tff(c_436,plain,(
    k1_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = k4_tarski('#skF_1','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_329])).

tff(c_443,plain,(
    k4_tarski('#skF_1','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_436])).

tff(c_464,plain,(
    k2_mcart_1(k4_tarski('#skF_1','#skF_2')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_8])).

tff(c_470,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_464])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_470])).

tff(c_473,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_479,plain,(
    ! [A_85,B_86,C_87] : k4_tarski(k4_tarski(A_85,B_86),C_87) = k3_mcart_1(A_85,B_86,C_87) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_491,plain,(
    ! [A_85,B_86,C_87] : k2_mcart_1(k3_mcart_1(A_85,B_86,C_87)) = C_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_8])).

tff(c_523,plain,(
    ! [A_94,B_95,C_96,D_97] : k3_mcart_1(k4_tarski(A_94,B_95),C_96,D_97) = k4_mcart_1(A_94,B_95,C_96,D_97) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_488,plain,(
    ! [A_85,B_86,C_87] : k1_mcart_1(k3_mcart_1(A_85,B_86,C_87)) = k4_tarski(A_85,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_6])).

tff(c_529,plain,(
    ! [A_94,B_95,C_96,D_97] : k4_tarski(k4_tarski(A_94,B_95),C_96) = k1_mcart_1(k4_mcart_1(A_94,B_95,C_96,D_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_488])).

tff(c_540,plain,(
    ! [A_94,B_95,C_96,D_97] : k1_mcart_1(k4_mcart_1(A_94,B_95,C_96,D_97)) = k3_mcart_1(A_94,B_95,C_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_529])).

tff(c_474,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_500,plain,(
    k4_mcart_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_199,c_309,c_12])).

tff(c_555,plain,(
    ! [A_102,B_103,C_104,D_105] : k1_mcart_1(k4_mcart_1(A_102,B_103,C_104,D_105)) = k3_mcart_1(A_102,B_103,C_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_529])).

tff(c_564,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_1','#skF_2','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_555])).

tff(c_567,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_564])).

tff(c_574,plain,(
    k2_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_491])).

tff(c_578,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_574])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.12/1.24  
% 2.12/1.24  %Foreground sorts:
% 2.12/1.24  
% 2.12/1.24  
% 2.12/1.24  %Background operators:
% 2.12/1.24  
% 2.12/1.24  
% 2.12/1.24  %Foreground operators:
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.24  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.12/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.12/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.24  tff('#skF_8', type, '#skF_8': $i).
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.24  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.12/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.24  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.12/1.24  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.12/1.24  
% 2.12/1.26  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 2.12/1.26  tff(f_33, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.12/1.26  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.12/1.26  tff(f_29, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k3_mcart_1(k4_tarski(A, B), C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_mcart_1)).
% 2.12/1.26  tff(c_10, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.26  tff(c_31, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_10])).
% 2.12/1.26  tff(c_6, plain, (![A_8, B_9]: (k1_mcart_1(k4_tarski(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.26  tff(c_32, plain, (![A_14, B_15, C_16]: (k4_tarski(k4_tarski(A_14, B_15), C_16)=k3_mcart_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.26  tff(c_41, plain, (![A_14, B_15, C_16]: (k1_mcart_1(k3_mcart_1(A_14, B_15, C_16))=k4_tarski(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6])).
% 2.12/1.26  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski(k4_tarski(A_1, B_2), C_3)=k3_mcart_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.26  tff(c_75, plain, (![A_23, B_24, C_25, D_26]: (k3_mcart_1(k4_tarski(A_23, B_24), C_25, D_26)=k4_mcart_1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.26  tff(c_81, plain, (![A_23, B_24, C_25, D_26]: (k4_tarski(k4_tarski(A_23, B_24), C_25)=k1_mcart_1(k4_mcart_1(A_23, B_24, C_25, D_26)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_41])).
% 2.12/1.26  tff(c_92, plain, (![A_23, B_24, C_25, D_26]: (k1_mcart_1(k4_mcart_1(A_23, B_24, C_25, D_26))=k3_mcart_1(A_23, B_24, C_25))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_81])).
% 2.12/1.26  tff(c_8, plain, (![A_8, B_9]: (k2_mcart_1(k4_tarski(A_8, B_9))=B_9)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.26  tff(c_44, plain, (![A_14, B_15, C_16]: (k2_mcart_1(k3_mcart_1(A_14, B_15, C_16))=C_16)), inference(superposition, [status(thm), theory('equality')], [c_32, c_8])).
% 2.12/1.26  tff(c_84, plain, (![A_23, B_24, C_25, D_26]: (k2_mcart_1(k4_mcart_1(A_23, B_24, C_25, D_26))=D_26)), inference(superposition, [status(thm), theory('equality')], [c_75, c_44])).
% 2.12/1.26  tff(c_12, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.26  tff(c_94, plain, (![A_27, B_28, C_29, D_30]: (k2_mcart_1(k4_mcart_1(A_27, B_28, C_29, D_30))=D_30)), inference(superposition, [status(thm), theory('equality')], [c_75, c_44])).
% 2.12/1.26  tff(c_103, plain, (k2_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_12, c_94])).
% 2.12/1.26  tff(c_106, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_103])).
% 2.12/1.26  tff(c_107, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_12])).
% 2.12/1.26  tff(c_124, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_5', '#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_107, c_92])).
% 2.12/1.26  tff(c_130, plain, (k3_mcart_1('#skF_5', '#skF_6', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_124])).
% 2.12/1.26  tff(c_136, plain, (k1_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))=k4_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_130, c_41])).
% 2.12/1.26  tff(c_142, plain, (k4_tarski('#skF_5', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_136])).
% 2.12/1.26  tff(c_187, plain, (k1_mcart_1(k4_tarski('#skF_1', '#skF_2'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_142, c_6])).
% 2.12/1.26  tff(c_195, plain, ('#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_187])).
% 2.12/1.26  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_195])).
% 2.12/1.26  tff(c_198, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_10])).
% 2.12/1.26  tff(c_204, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_198])).
% 2.12/1.26  tff(c_249, plain, (![A_48, B_49, C_50, D_51]: (k3_mcart_1(k4_tarski(A_48, B_49), C_50, D_51)=k4_mcart_1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.26  tff(c_210, plain, (![A_39, B_40, C_41]: (k4_tarski(k4_tarski(A_39, B_40), C_41)=k3_mcart_1(A_39, B_40, C_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.26  tff(c_222, plain, (![A_39, B_40, C_41]: (k2_mcart_1(k3_mcart_1(A_39, B_40, C_41))=C_41)), inference(superposition, [status(thm), theory('equality')], [c_210, c_8])).
% 2.12/1.26  tff(c_258, plain, (![A_48, B_49, C_50, D_51]: (k2_mcart_1(k4_mcart_1(A_48, B_49, C_50, D_51))=D_51)), inference(superposition, [status(thm), theory('equality')], [c_249, c_222])).
% 2.12/1.26  tff(c_199, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_10])).
% 2.12/1.26  tff(c_205, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_12])).
% 2.12/1.26  tff(c_293, plain, (![A_56, B_57, C_58, D_59]: (k2_mcart_1(k4_mcart_1(A_56, B_57, C_58, D_59))=D_59)), inference(superposition, [status(thm), theory('equality')], [c_249, c_222])).
% 2.12/1.26  tff(c_302, plain, (k2_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_205, c_293])).
% 2.12/1.26  tff(c_305, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_258, c_302])).
% 2.12/1.26  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_305])).
% 2.12/1.26  tff(c_308, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_198])).
% 2.12/1.26  tff(c_314, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_308])).
% 2.12/1.26  tff(c_320, plain, (![A_60, B_61, C_62]: (k4_tarski(k4_tarski(A_60, B_61), C_62)=k3_mcart_1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.26  tff(c_329, plain, (![A_60, B_61, C_62]: (k1_mcart_1(k3_mcart_1(A_60, B_61, C_62))=k4_tarski(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_320, c_6])).
% 2.12/1.26  tff(c_359, plain, (![A_69, B_70, C_71, D_72]: (k3_mcart_1(k4_tarski(A_69, B_70), C_71, D_72)=k4_mcart_1(A_69, B_70, C_71, D_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.26  tff(c_365, plain, (![A_69, B_70, C_71, D_72]: (k4_tarski(k4_tarski(A_69, B_70), C_71)=k1_mcart_1(k4_mcart_1(A_69, B_70, C_71, D_72)))), inference(superposition, [status(thm), theory('equality')], [c_359, c_329])).
% 2.12/1.26  tff(c_376, plain, (![A_69, B_70, C_71, D_72]: (k1_mcart_1(k4_mcart_1(A_69, B_70, C_71, D_72))=k3_mcart_1(A_69, B_70, C_71))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_365])).
% 2.12/1.26  tff(c_309, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_198])).
% 2.12/1.26  tff(c_315, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_199, c_12])).
% 2.12/1.26  tff(c_417, plain, (![A_81, B_82, C_83, D_84]: (k1_mcart_1(k4_mcart_1(A_81, B_82, C_83, D_84))=k3_mcart_1(A_81, B_82, C_83))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_365])).
% 2.12/1.26  tff(c_426, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_1', '#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_315, c_417])).
% 2.12/1.26  tff(c_429, plain, (k3_mcart_1('#skF_1', '#skF_6', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_426])).
% 2.12/1.26  tff(c_436, plain, (k1_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))=k4_tarski('#skF_1', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_429, c_329])).
% 2.12/1.26  tff(c_443, plain, (k4_tarski('#skF_1', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_436])).
% 2.12/1.26  tff(c_464, plain, (k2_mcart_1(k4_tarski('#skF_1', '#skF_2'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_443, c_8])).
% 2.12/1.26  tff(c_470, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_464])).
% 2.12/1.26  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_470])).
% 2.12/1.26  tff(c_473, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_308])).
% 2.12/1.26  tff(c_479, plain, (![A_85, B_86, C_87]: (k4_tarski(k4_tarski(A_85, B_86), C_87)=k3_mcart_1(A_85, B_86, C_87))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.26  tff(c_491, plain, (![A_85, B_86, C_87]: (k2_mcart_1(k3_mcart_1(A_85, B_86, C_87))=C_87)), inference(superposition, [status(thm), theory('equality')], [c_479, c_8])).
% 2.12/1.26  tff(c_523, plain, (![A_94, B_95, C_96, D_97]: (k3_mcart_1(k4_tarski(A_94, B_95), C_96, D_97)=k4_mcart_1(A_94, B_95, C_96, D_97))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.26  tff(c_488, plain, (![A_85, B_86, C_87]: (k1_mcart_1(k3_mcart_1(A_85, B_86, C_87))=k4_tarski(A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_479, c_6])).
% 2.12/1.26  tff(c_529, plain, (![A_94, B_95, C_96, D_97]: (k4_tarski(k4_tarski(A_94, B_95), C_96)=k1_mcart_1(k4_mcart_1(A_94, B_95, C_96, D_97)))), inference(superposition, [status(thm), theory('equality')], [c_523, c_488])).
% 2.12/1.26  tff(c_540, plain, (![A_94, B_95, C_96, D_97]: (k1_mcart_1(k4_mcart_1(A_94, B_95, C_96, D_97))=k3_mcart_1(A_94, B_95, C_96))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_529])).
% 2.12/1.26  tff(c_474, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_308])).
% 2.12/1.26  tff(c_500, plain, (k4_mcart_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_199, c_309, c_12])).
% 2.12/1.26  tff(c_555, plain, (![A_102, B_103, C_104, D_105]: (k1_mcart_1(k4_mcart_1(A_102, B_103, C_104, D_105))=k3_mcart_1(A_102, B_103, C_104))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_529])).
% 2.12/1.26  tff(c_564, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_1', '#skF_2', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_500, c_555])).
% 2.12/1.26  tff(c_567, plain, (k3_mcart_1('#skF_1', '#skF_2', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_564])).
% 2.12/1.26  tff(c_574, plain, (k2_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_567, c_491])).
% 2.12/1.26  tff(c_578, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_491, c_574])).
% 2.12/1.26  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_473, c_578])).
% 2.12/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.26  
% 2.12/1.26  Inference rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Ref     : 0
% 2.12/1.26  #Sup     : 154
% 2.12/1.26  #Fact    : 0
% 2.12/1.26  #Define  : 0
% 2.12/1.26  #Split   : 3
% 2.12/1.26  #Chain   : 0
% 2.12/1.26  #Close   : 0
% 2.12/1.26  
% 2.12/1.26  Ordering : KBO
% 2.12/1.26  
% 2.12/1.26  Simplification rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Subsume      : 0
% 2.12/1.26  #Demod        : 43
% 2.12/1.26  #Tautology    : 93
% 2.12/1.26  #SimpNegUnit  : 4
% 2.12/1.26  #BackRed      : 5
% 2.12/1.26  
% 2.12/1.26  #Partial instantiations: 0
% 2.12/1.26  #Strategies tried      : 1
% 2.12/1.26  
% 2.12/1.26  Timing (in seconds)
% 2.12/1.26  ----------------------
% 2.12/1.26  Preprocessing        : 0.25
% 2.12/1.26  Parsing              : 0.14
% 2.12/1.26  CNF conversion       : 0.02
% 2.12/1.26  Main loop            : 0.24
% 2.12/1.26  Inferencing          : 0.10
% 2.12/1.26  Reduction            : 0.08
% 2.12/1.26  Demodulation         : 0.06
% 2.12/1.26  BG Simplification    : 0.02
% 2.12/1.26  Subsumption          : 0.02
% 2.12/1.26  Abstraction          : 0.02
% 2.12/1.26  MUC search           : 0.00
% 2.12/1.26  Cooper               : 0.00
% 2.12/1.26  Total                : 0.53
% 2.12/1.26  Index Insertion      : 0.00
% 2.12/1.26  Index Deletion       : 0.00
% 2.12/1.26  Index Matching       : 0.00
% 2.12/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
