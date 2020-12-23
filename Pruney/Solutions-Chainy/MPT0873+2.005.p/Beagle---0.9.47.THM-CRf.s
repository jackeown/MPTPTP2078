%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:27 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 182 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 291 expanded)
%              Number of equality atoms :   72 ( 287 expanded)
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
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

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

tff(c_75,plain,(
    ! [A_23,B_24,C_25,D_26] : k4_tarski(k3_mcart_1(A_23,B_24,C_25),D_26) = k4_mcart_1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ! [A_23,B_24,C_25,D_26] : k1_mcart_1(k4_mcart_1(A_23,B_24,C_25,D_26)) = k3_mcart_1(A_23,B_24,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_6])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_mcart_1(k4_tarski(A_8,B_9)) = B_9 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_23,B_24,C_25,D_26] : k2_mcart_1(k4_mcart_1(A_23,B_24,C_25,D_26)) = D_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_8])).

tff(c_12,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_mcart_1(k4_mcart_1(A_27,B_28,C_29,D_30)) = D_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_8])).

tff(c_102,plain,(
    k2_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_93])).

tff(c_105,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_102])).

tff(c_106,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_12])).

tff(c_123,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_5','#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_84])).

tff(c_129,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_123])).

tff(c_138,plain,(
    k1_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = k4_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_41])).

tff(c_145,plain,(
    k4_tarski('#skF_5','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_138])).

tff(c_190,plain,(
    k1_mcart_1(k4_tarski('#skF_1','#skF_2')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_6])).

tff(c_198,plain,(
    '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_190])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_198])).

tff(c_201,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_207,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_252,plain,(
    ! [A_48,B_49,C_50,D_51] : k4_tarski(k3_mcart_1(A_48,B_49,C_50),D_51) = k4_mcart_1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_264,plain,(
    ! [A_48,B_49,C_50,D_51] : k2_mcart_1(k4_mcart_1(A_48,B_49,C_50,D_51)) = D_51 ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_8])).

tff(c_202,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_208,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_12])).

tff(c_270,plain,(
    ! [A_52,B_53,C_54,D_55] : k2_mcart_1(k4_mcart_1(A_52,B_53,C_54,D_55)) = D_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_8])).

tff(c_279,plain,(
    k2_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_270])).

tff(c_282,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_279])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_282])).

tff(c_285,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_291,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_297,plain,(
    ! [A_56,B_57,C_58] : k4_tarski(k4_tarski(A_56,B_57),C_58) = k3_mcart_1(A_56,B_57,C_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_306,plain,(
    ! [A_56,B_57,C_58] : k1_mcart_1(k3_mcart_1(A_56,B_57,C_58)) = k4_tarski(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_6])).

tff(c_336,plain,(
    ! [A_65,B_66,C_67,D_68] : k4_tarski(k3_mcart_1(A_65,B_66,C_67),D_68) = k4_mcart_1(A_65,B_66,C_67,D_68) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_345,plain,(
    ! [A_65,B_66,C_67,D_68] : k1_mcart_1(k4_mcart_1(A_65,B_66,C_67,D_68)) = k3_mcart_1(A_65,B_66,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_6])).

tff(c_286,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_292,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_202,c_12])).

tff(c_367,plain,(
    ! [A_73,B_74,C_75,D_76] : k1_mcart_1(k4_mcart_1(A_73,B_74,C_75,D_76)) = k3_mcart_1(A_73,B_74,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_6])).

tff(c_376,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_1','#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_367])).

tff(c_379,plain,(
    k3_mcart_1('#skF_1','#skF_6','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_376])).

tff(c_386,plain,(
    k1_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = k4_tarski('#skF_1','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_306])).

tff(c_393,plain,(
    k4_tarski('#skF_1','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_386])).

tff(c_411,plain,(
    k2_mcart_1(k4_tarski('#skF_1','#skF_2')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_8])).

tff(c_416,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_411])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_416])).

tff(c_419,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_431,plain,(
    ! [A_77,B_78,C_79] : k4_tarski(k4_tarski(A_77,B_78),C_79) = k3_mcart_1(A_77,B_78,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_443,plain,(
    ! [A_77,B_78,C_79] : k2_mcart_1(k3_mcart_1(A_77,B_78,C_79)) = C_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_8])).

tff(c_474,plain,(
    ! [A_86,B_87,C_88,D_89] : k4_tarski(k3_mcart_1(A_86,B_87,C_88),D_89) = k4_mcart_1(A_86,B_87,C_88,D_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_483,plain,(
    ! [A_86,B_87,C_88,D_89] : k1_mcart_1(k4_mcart_1(A_86,B_87,C_88,D_89)) = k3_mcart_1(A_86,B_87,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_6])).

tff(c_420,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_421,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_286,c_12])).

tff(c_426,plain,(
    k4_mcart_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_421])).

tff(c_505,plain,(
    ! [A_94,B_95,C_96,D_97] : k1_mcart_1(k4_mcart_1(A_94,B_95,C_96,D_97)) = k3_mcart_1(A_94,B_95,C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_6])).

tff(c_514,plain,(
    k1_mcart_1(k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_mcart_1('#skF_1','#skF_2','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_505])).

tff(c_517,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_514])).

tff(c_527,plain,(
    k2_mcart_1(k3_mcart_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_443])).

tff(c_532,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_527])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.31  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.07/1.31  
% 2.07/1.31  %Foreground sorts:
% 2.07/1.31  
% 2.07/1.31  
% 2.07/1.31  %Background operators:
% 2.07/1.31  
% 2.07/1.31  
% 2.07/1.31  %Foreground operators:
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.31  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.07/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.07/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.07/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.07/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.07/1.31  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.07/1.31  
% 2.07/1.32  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 2.07/1.32  tff(f_33, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.07/1.32  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.07/1.32  tff(f_29, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.07/1.32  tff(c_10, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.32  tff(c_31, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_10])).
% 2.07/1.32  tff(c_6, plain, (![A_8, B_9]: (k1_mcart_1(k4_tarski(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.32  tff(c_32, plain, (![A_14, B_15, C_16]: (k4_tarski(k4_tarski(A_14, B_15), C_16)=k3_mcart_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.32  tff(c_41, plain, (![A_14, B_15, C_16]: (k1_mcart_1(k3_mcart_1(A_14, B_15, C_16))=k4_tarski(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6])).
% 2.07/1.32  tff(c_75, plain, (![A_23, B_24, C_25, D_26]: (k4_tarski(k3_mcart_1(A_23, B_24, C_25), D_26)=k4_mcart_1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.32  tff(c_84, plain, (![A_23, B_24, C_25, D_26]: (k1_mcart_1(k4_mcart_1(A_23, B_24, C_25, D_26))=k3_mcart_1(A_23, B_24, C_25))), inference(superposition, [status(thm), theory('equality')], [c_75, c_6])).
% 2.07/1.32  tff(c_8, plain, (![A_8, B_9]: (k2_mcart_1(k4_tarski(A_8, B_9))=B_9)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.32  tff(c_87, plain, (![A_23, B_24, C_25, D_26]: (k2_mcart_1(k4_mcart_1(A_23, B_24, C_25, D_26))=D_26)), inference(superposition, [status(thm), theory('equality')], [c_75, c_8])).
% 2.07/1.32  tff(c_12, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.32  tff(c_93, plain, (![A_27, B_28, C_29, D_30]: (k2_mcart_1(k4_mcart_1(A_27, B_28, C_29, D_30))=D_30)), inference(superposition, [status(thm), theory('equality')], [c_75, c_8])).
% 2.07/1.32  tff(c_102, plain, (k2_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_12, c_93])).
% 2.07/1.32  tff(c_105, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_102])).
% 2.07/1.32  tff(c_106, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_12])).
% 2.07/1.32  tff(c_123, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_5', '#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_106, c_84])).
% 2.07/1.32  tff(c_129, plain, (k3_mcart_1('#skF_5', '#skF_6', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_123])).
% 2.07/1.32  tff(c_138, plain, (k1_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))=k4_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_129, c_41])).
% 2.07/1.32  tff(c_145, plain, (k4_tarski('#skF_5', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_138])).
% 2.07/1.32  tff(c_190, plain, (k1_mcart_1(k4_tarski('#skF_1', '#skF_2'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_145, c_6])).
% 2.07/1.32  tff(c_198, plain, ('#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_190])).
% 2.07/1.32  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_198])).
% 2.07/1.32  tff(c_201, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_10])).
% 2.07/1.32  tff(c_207, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_201])).
% 2.07/1.32  tff(c_252, plain, (![A_48, B_49, C_50, D_51]: (k4_tarski(k3_mcart_1(A_48, B_49, C_50), D_51)=k4_mcart_1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.32  tff(c_264, plain, (![A_48, B_49, C_50, D_51]: (k2_mcart_1(k4_mcart_1(A_48, B_49, C_50, D_51))=D_51)), inference(superposition, [status(thm), theory('equality')], [c_252, c_8])).
% 2.07/1.32  tff(c_202, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_10])).
% 2.07/1.32  tff(c_208, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_12])).
% 2.07/1.32  tff(c_270, plain, (![A_52, B_53, C_54, D_55]: (k2_mcart_1(k4_mcart_1(A_52, B_53, C_54, D_55))=D_55)), inference(superposition, [status(thm), theory('equality')], [c_252, c_8])).
% 2.07/1.32  tff(c_279, plain, (k2_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_208, c_270])).
% 2.07/1.32  tff(c_282, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_279])).
% 2.07/1.32  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_282])).
% 2.07/1.32  tff(c_285, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_201])).
% 2.07/1.32  tff(c_291, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_285])).
% 2.07/1.32  tff(c_297, plain, (![A_56, B_57, C_58]: (k4_tarski(k4_tarski(A_56, B_57), C_58)=k3_mcart_1(A_56, B_57, C_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.32  tff(c_306, plain, (![A_56, B_57, C_58]: (k1_mcart_1(k3_mcart_1(A_56, B_57, C_58))=k4_tarski(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_297, c_6])).
% 2.07/1.32  tff(c_336, plain, (![A_65, B_66, C_67, D_68]: (k4_tarski(k3_mcart_1(A_65, B_66, C_67), D_68)=k4_mcart_1(A_65, B_66, C_67, D_68))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.32  tff(c_345, plain, (![A_65, B_66, C_67, D_68]: (k1_mcart_1(k4_mcart_1(A_65, B_66, C_67, D_68))=k3_mcart_1(A_65, B_66, C_67))), inference(superposition, [status(thm), theory('equality')], [c_336, c_6])).
% 2.07/1.32  tff(c_286, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_201])).
% 2.07/1.32  tff(c_292, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_202, c_12])).
% 2.07/1.32  tff(c_367, plain, (![A_73, B_74, C_75, D_76]: (k1_mcart_1(k4_mcart_1(A_73, B_74, C_75, D_76))=k3_mcart_1(A_73, B_74, C_75))), inference(superposition, [status(thm), theory('equality')], [c_336, c_6])).
% 2.07/1.32  tff(c_376, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_1', '#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_292, c_367])).
% 2.07/1.32  tff(c_379, plain, (k3_mcart_1('#skF_1', '#skF_6', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_376])).
% 2.07/1.32  tff(c_386, plain, (k1_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))=k4_tarski('#skF_1', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_379, c_306])).
% 2.07/1.32  tff(c_393, plain, (k4_tarski('#skF_1', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_386])).
% 2.07/1.32  tff(c_411, plain, (k2_mcart_1(k4_tarski('#skF_1', '#skF_2'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_393, c_8])).
% 2.07/1.32  tff(c_416, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_411])).
% 2.07/1.32  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_416])).
% 2.07/1.32  tff(c_419, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_285])).
% 2.07/1.32  tff(c_431, plain, (![A_77, B_78, C_79]: (k4_tarski(k4_tarski(A_77, B_78), C_79)=k3_mcart_1(A_77, B_78, C_79))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.32  tff(c_443, plain, (![A_77, B_78, C_79]: (k2_mcart_1(k3_mcart_1(A_77, B_78, C_79))=C_79)), inference(superposition, [status(thm), theory('equality')], [c_431, c_8])).
% 2.07/1.32  tff(c_474, plain, (![A_86, B_87, C_88, D_89]: (k4_tarski(k3_mcart_1(A_86, B_87, C_88), D_89)=k4_mcart_1(A_86, B_87, C_88, D_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.32  tff(c_483, plain, (![A_86, B_87, C_88, D_89]: (k1_mcart_1(k4_mcart_1(A_86, B_87, C_88, D_89))=k3_mcart_1(A_86, B_87, C_88))), inference(superposition, [status(thm), theory('equality')], [c_474, c_6])).
% 2.07/1.32  tff(c_420, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_285])).
% 2.07/1.32  tff(c_421, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_286, c_12])).
% 2.07/1.32  tff(c_426, plain, (k4_mcart_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_420, c_421])).
% 2.07/1.32  tff(c_505, plain, (![A_94, B_95, C_96, D_97]: (k1_mcart_1(k4_mcart_1(A_94, B_95, C_96, D_97))=k3_mcart_1(A_94, B_95, C_96))), inference(superposition, [status(thm), theory('equality')], [c_474, c_6])).
% 2.07/1.32  tff(c_514, plain, (k1_mcart_1(k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_mcart_1('#skF_1', '#skF_2', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_426, c_505])).
% 2.07/1.32  tff(c_517, plain, (k3_mcart_1('#skF_1', '#skF_2', '#skF_7')=k3_mcart_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_514])).
% 2.07/1.32  tff(c_527, plain, (k2_mcart_1(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_517, c_443])).
% 2.07/1.32  tff(c_532, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_527])).
% 2.07/1.32  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_532])).
% 2.07/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.32  
% 2.07/1.32  Inference rules
% 2.07/1.32  ----------------------
% 2.07/1.32  #Ref     : 0
% 2.07/1.32  #Sup     : 143
% 2.07/1.32  #Fact    : 0
% 2.07/1.32  #Define  : 0
% 2.07/1.32  #Split   : 3
% 2.07/1.32  #Chain   : 0
% 2.07/1.32  #Close   : 0
% 2.07/1.32  
% 2.07/1.32  Ordering : KBO
% 2.07/1.32  
% 2.07/1.32  Simplification rules
% 2.07/1.32  ----------------------
% 2.07/1.32  #Subsume      : 0
% 2.07/1.32  #Demod        : 38
% 2.07/1.32  #Tautology    : 90
% 2.07/1.32  #SimpNegUnit  : 4
% 2.07/1.32  #BackRed      : 6
% 2.07/1.32  
% 2.07/1.32  #Partial instantiations: 0
% 2.07/1.32  #Strategies tried      : 1
% 2.07/1.32  
% 2.07/1.32  Timing (in seconds)
% 2.07/1.32  ----------------------
% 2.07/1.33  Preprocessing        : 0.28
% 2.07/1.33  Parsing              : 0.15
% 2.07/1.33  CNF conversion       : 0.02
% 2.07/1.33  Main loop            : 0.26
% 2.07/1.33  Inferencing          : 0.11
% 2.07/1.33  Reduction            : 0.09
% 2.07/1.33  Demodulation         : 0.06
% 2.07/1.33  BG Simplification    : 0.02
% 2.07/1.33  Subsumption          : 0.02
% 2.07/1.33  Abstraction          : 0.02
% 2.07/1.33  MUC search           : 0.00
% 2.07/1.33  Cooper               : 0.00
% 2.07/1.33  Total                : 0.58
% 2.07/1.33  Index Insertion      : 0.00
% 2.07/1.33  Index Deletion       : 0.00
% 2.07/1.33  Index Matching       : 0.00
% 2.07/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
