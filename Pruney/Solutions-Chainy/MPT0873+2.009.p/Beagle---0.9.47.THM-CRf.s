%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:27 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 143 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :   93 ( 285 expanded)
%              Number of equality atoms :   89 ( 281 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k4_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_8,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_11,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] : k4_tarski(k4_tarski(k4_tarski(A_5,B_6),C_7),D_8) = k4_mcart_1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19,D_20] : k4_tarski(k4_tarski(k4_tarski(A_17,B_18),C_19),D_20) = k4_mcart_1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [D_4,B_2,C_3,A_1] :
      ( D_4 = B_2
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [D_24,B_25,A_26,C_21,A_22,B_23] :
      ( D_24 = B_25
      | k4_tarski(A_26,B_25) != k4_mcart_1(A_22,B_23,C_21,D_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_66,plain,(
    ! [B_27,A_28] :
      ( B_27 = '#skF_8'
      | k4_tarski(A_28,B_27) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_69,plain,(
    ! [D_8,A_5,B_6,C_7] :
      ( D_8 = '#skF_8'
      | k4_mcart_1(A_5,B_6,C_7,D_8) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_72,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_69])).

tff(c_81,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10])).

tff(c_4,plain,(
    ! [C_3,A_1,D_4,B_2] :
      ( C_3 = A_1
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [C_46,A_47,D_49,B_50,A_51,B_48] :
      ( k4_tarski(k4_tarski(A_47,B_48),C_46) = A_51
      | k4_tarski(A_51,B_50) != k4_mcart_1(A_47,B_48,C_46,D_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_135,plain,(
    ! [A_52,B_53] :
      ( k4_tarski(k4_tarski('#skF_5','#skF_6'),'#skF_7') = A_52
      | k4_tarski(A_52,B_53) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_126])).

tff(c_137,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( k4_tarski(k4_tarski(A_5,B_6),C_7) = k4_tarski(k4_tarski('#skF_5','#skF_6'),'#skF_7')
      | k4_mcart_1(A_5,B_6,C_7,D_8) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_140,plain,(
    k4_tarski(k4_tarski('#skF_5','#skF_6'),'#skF_7') = k4_tarski(k4_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_137])).

tff(c_174,plain,(
    ! [A_1,B_2] :
      ( k4_tarski('#skF_5','#skF_6') = A_1
      | k4_tarski(k4_tarski('#skF_1','#skF_2'),'#skF_3') != k4_tarski(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_4])).

tff(c_342,plain,(
    k4_tarski('#skF_5','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_174])).

tff(c_372,plain,(
    ! [A_1,B_2] :
      ( A_1 = '#skF_5'
      | k4_tarski(A_1,B_2) != k4_tarski('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_4])).

tff(c_433,plain,(
    '#skF_5' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_372])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11,c_433])).

tff(c_436,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_447,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_437,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_442,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_10])).

tff(c_458,plain,(
    ! [A_84,B_85,C_86,D_87] : k4_tarski(k4_tarski(k4_tarski(A_84,B_85),C_86),D_87) = k4_mcart_1(A_84,B_85,C_86,D_87) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_491,plain,(
    ! [D_92,A_89,B_91,B_90,A_93,C_88] :
      ( D_92 = B_91
      | k4_tarski(A_93,B_91) != k4_mcart_1(A_89,B_90,C_88,D_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_2])).

tff(c_506,plain,(
    ! [C_99,B_98,A_102,D_96,D_103,A_101,B_97,C_100] :
      ( D_96 = D_103
      | k4_mcart_1(A_102,B_97,C_99,D_103) != k4_mcart_1(A_101,B_98,C_100,D_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_491])).

tff(c_509,plain,(
    ! [D_96,A_101,B_98,C_100] :
      ( D_96 = '#skF_8'
      | k4_mcart_1(A_101,B_98,C_100,D_96) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_506])).

tff(c_515,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_509])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_515])).

tff(c_518,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_525,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_518])).

tff(c_519,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_520,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_442])).

tff(c_540,plain,(
    ! [A_112,B_113,C_114,D_115] : k4_tarski(k4_tarski(k4_tarski(A_112,B_113),C_114),D_115) = k4_mcart_1(A_112,B_113,C_114,D_115) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_613,plain,(
    ! [D_138,C_136,A_137,B_135,B_139,A_140] :
      ( k4_tarski(k4_tarski(A_140,B_139),C_136) = A_137
      | k4_tarski(A_137,B_135) != k4_mcart_1(A_140,B_139,C_136,D_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_4])).

tff(c_622,plain,(
    ! [A_141,B_142] :
      ( k4_tarski(k4_tarski('#skF_1','#skF_6'),'#skF_7') = A_141
      | k4_tarski(A_141,B_142) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_613])).

tff(c_624,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( k4_tarski(k4_tarski(A_5,B_6),C_7) = k4_tarski(k4_tarski('#skF_1','#skF_6'),'#skF_7')
      | k4_mcart_1(A_5,B_6,C_7,D_8) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_622])).

tff(c_687,plain,(
    k4_tarski(k4_tarski('#skF_1','#skF_6'),'#skF_7') = k4_tarski(k4_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_624])).

tff(c_730,plain,(
    ! [A_1,B_2] :
      ( k4_tarski('#skF_1','#skF_6') = A_1
      | k4_tarski(k4_tarski('#skF_1','#skF_2'),'#skF_3') != k4_tarski(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_4])).

tff(c_873,plain,(
    k4_tarski('#skF_1','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_730])).

tff(c_897,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_6'
      | k4_tarski(A_1,B_2) != k4_tarski('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_2])).

tff(c_915,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_897])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_915])).

tff(c_918,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_518])).

tff(c_919,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_518])).

tff(c_934,plain,(
    k4_mcart_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_520])).

tff(c_939,plain,(
    ! [A_179,B_180,C_181,D_182] : k4_tarski(k4_tarski(k4_tarski(A_179,B_180),C_181),D_182) = k4_mcart_1(A_179,B_180,C_181,D_182) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1012,plain,(
    ! [A_207,D_205,C_204,A_203,B_206,B_202] :
      ( k4_tarski(k4_tarski(A_203,B_202),C_204) = A_207
      | k4_tarski(A_207,B_206) != k4_mcart_1(A_203,B_202,C_204,D_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_939,c_4])).

tff(c_1067,plain,(
    ! [D_217,C_221,B_220,D_219,A_216,C_218,A_222,B_223] :
      ( k4_tarski(k4_tarski(A_222,B_220),C_221) = k4_tarski(k4_tarski(A_216,B_223),C_218)
      | k4_mcart_1(A_222,B_220,C_221,D_217) != k4_mcart_1(A_216,B_223,C_218,D_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1012])).

tff(c_1079,plain,(
    ! [A_222,B_220,C_221,D_217] :
      ( k4_tarski(k4_tarski(A_222,B_220),C_221) = k4_tarski(k4_tarski('#skF_1','#skF_2'),'#skF_7')
      | k4_mcart_1(A_222,B_220,C_221,D_217) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_1067])).

tff(c_1086,plain,(
    k4_tarski(k4_tarski('#skF_1','#skF_2'),'#skF_7') = k4_tarski(k4_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1079])).

tff(c_1123,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_7'
      | k4_tarski(k4_tarski('#skF_1','#skF_2'),'#skF_3') != k4_tarski(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_2])).

tff(c_1171,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1123])).

tff(c_1173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_918,c_1171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.53  
% 3.06/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.53  %$ k4_mcart_1 > k4_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.06/1.53  
% 3.06/1.53  %Foreground sorts:
% 3.06/1.53  
% 3.06/1.53  
% 3.06/1.53  %Background operators:
% 3.06/1.53  
% 3.06/1.53  
% 3.06/1.53  %Foreground operators:
% 3.06/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.06/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.06/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.06/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.06/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.53  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.06/1.53  
% 3.10/1.55  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 3.10/1.55  tff(f_33, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 3.10/1.55  tff(f_31, axiom, (![A, B, C, D]: ((k4_tarski(A, B) = k4_tarski(C, D)) => ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 3.10/1.55  tff(c_8, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.10/1.55  tff(c_11, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_8])).
% 3.10/1.55  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k4_tarski(k4_tarski(k4_tarski(A_5, B_6), C_7), D_8)=k4_mcart_1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.55  tff(c_10, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.10/1.55  tff(c_26, plain, (![A_17, B_18, C_19, D_20]: (k4_tarski(k4_tarski(k4_tarski(A_17, B_18), C_19), D_20)=k4_mcart_1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.55  tff(c_2, plain, (![D_4, B_2, C_3, A_1]: (D_4=B_2 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.55  tff(c_59, plain, (![D_24, B_25, A_26, C_21, A_22, B_23]: (D_24=B_25 | k4_tarski(A_26, B_25)!=k4_mcart_1(A_22, B_23, C_21, D_24))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2])).
% 3.10/1.55  tff(c_66, plain, (![B_27, A_28]: (B_27='#skF_8' | k4_tarski(A_28, B_27)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_59])).
% 3.10/1.55  tff(c_69, plain, (![D_8, A_5, B_6, C_7]: (D_8='#skF_8' | k4_mcart_1(A_5, B_6, C_7, D_8)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 3.10/1.55  tff(c_72, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_69])).
% 3.10/1.55  tff(c_81, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10])).
% 3.10/1.55  tff(c_4, plain, (![C_3, A_1, D_4, B_2]: (C_3=A_1 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.55  tff(c_126, plain, (![C_46, A_47, D_49, B_50, A_51, B_48]: (k4_tarski(k4_tarski(A_47, B_48), C_46)=A_51 | k4_tarski(A_51, B_50)!=k4_mcart_1(A_47, B_48, C_46, D_49))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 3.10/1.55  tff(c_135, plain, (![A_52, B_53]: (k4_tarski(k4_tarski('#skF_5', '#skF_6'), '#skF_7')=A_52 | k4_tarski(A_52, B_53)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_126])).
% 3.10/1.55  tff(c_137, plain, (![A_5, B_6, C_7, D_8]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k4_tarski(k4_tarski('#skF_5', '#skF_6'), '#skF_7') | k4_mcart_1(A_5, B_6, C_7, D_8)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_135])).
% 3.10/1.55  tff(c_140, plain, (k4_tarski(k4_tarski('#skF_5', '#skF_6'), '#skF_7')=k4_tarski(k4_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_137])).
% 3.10/1.55  tff(c_174, plain, (![A_1, B_2]: (k4_tarski('#skF_5', '#skF_6')=A_1 | k4_tarski(k4_tarski('#skF_1', '#skF_2'), '#skF_3')!=k4_tarski(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_140, c_4])).
% 3.10/1.55  tff(c_342, plain, (k4_tarski('#skF_5', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_174])).
% 3.10/1.55  tff(c_372, plain, (![A_1, B_2]: (A_1='#skF_5' | k4_tarski(A_1, B_2)!=k4_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_4])).
% 3.10/1.55  tff(c_433, plain, ('#skF_5'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_372])).
% 3.10/1.55  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11, c_433])).
% 3.10/1.55  tff(c_436, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_8])).
% 3.10/1.55  tff(c_447, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_436])).
% 3.10/1.55  tff(c_437, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_8])).
% 3.10/1.55  tff(c_442, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_437, c_10])).
% 3.10/1.55  tff(c_458, plain, (![A_84, B_85, C_86, D_87]: (k4_tarski(k4_tarski(k4_tarski(A_84, B_85), C_86), D_87)=k4_mcart_1(A_84, B_85, C_86, D_87))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.55  tff(c_491, plain, (![D_92, A_89, B_91, B_90, A_93, C_88]: (D_92=B_91 | k4_tarski(A_93, B_91)!=k4_mcart_1(A_89, B_90, C_88, D_92))), inference(superposition, [status(thm), theory('equality')], [c_458, c_2])).
% 3.10/1.55  tff(c_506, plain, (![C_99, B_98, A_102, D_96, D_103, A_101, B_97, C_100]: (D_96=D_103 | k4_mcart_1(A_102, B_97, C_99, D_103)!=k4_mcart_1(A_101, B_98, C_100, D_96))), inference(superposition, [status(thm), theory('equality')], [c_6, c_491])).
% 3.10/1.55  tff(c_509, plain, (![D_96, A_101, B_98, C_100]: (D_96='#skF_8' | k4_mcart_1(A_101, B_98, C_100, D_96)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_506])).
% 3.10/1.55  tff(c_515, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_509])).
% 3.10/1.55  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_447, c_515])).
% 3.10/1.55  tff(c_518, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_436])).
% 3.10/1.55  tff(c_525, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_518])).
% 3.10/1.55  tff(c_519, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_436])).
% 3.10/1.55  tff(c_520, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_442])).
% 3.10/1.55  tff(c_540, plain, (![A_112, B_113, C_114, D_115]: (k4_tarski(k4_tarski(k4_tarski(A_112, B_113), C_114), D_115)=k4_mcart_1(A_112, B_113, C_114, D_115))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.55  tff(c_613, plain, (![D_138, C_136, A_137, B_135, B_139, A_140]: (k4_tarski(k4_tarski(A_140, B_139), C_136)=A_137 | k4_tarski(A_137, B_135)!=k4_mcart_1(A_140, B_139, C_136, D_138))), inference(superposition, [status(thm), theory('equality')], [c_540, c_4])).
% 3.10/1.55  tff(c_622, plain, (![A_141, B_142]: (k4_tarski(k4_tarski('#skF_1', '#skF_6'), '#skF_7')=A_141 | k4_tarski(A_141, B_142)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_520, c_613])).
% 3.10/1.55  tff(c_624, plain, (![A_5, B_6, C_7, D_8]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k4_tarski(k4_tarski('#skF_1', '#skF_6'), '#skF_7') | k4_mcart_1(A_5, B_6, C_7, D_8)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_622])).
% 3.10/1.55  tff(c_687, plain, (k4_tarski(k4_tarski('#skF_1', '#skF_6'), '#skF_7')=k4_tarski(k4_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_624])).
% 3.10/1.55  tff(c_730, plain, (![A_1, B_2]: (k4_tarski('#skF_1', '#skF_6')=A_1 | k4_tarski(k4_tarski('#skF_1', '#skF_2'), '#skF_3')!=k4_tarski(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_687, c_4])).
% 3.10/1.55  tff(c_873, plain, (k4_tarski('#skF_1', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_730])).
% 3.10/1.55  tff(c_897, plain, (![B_2, A_1]: (B_2='#skF_6' | k4_tarski(A_1, B_2)!=k4_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_873, c_2])).
% 3.10/1.55  tff(c_915, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_897])).
% 3.10/1.55  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_915])).
% 3.10/1.55  tff(c_918, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_518])).
% 3.10/1.55  tff(c_919, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_518])).
% 3.10/1.55  tff(c_934, plain, (k4_mcart_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_919, c_520])).
% 3.10/1.55  tff(c_939, plain, (![A_179, B_180, C_181, D_182]: (k4_tarski(k4_tarski(k4_tarski(A_179, B_180), C_181), D_182)=k4_mcart_1(A_179, B_180, C_181, D_182))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.55  tff(c_1012, plain, (![A_207, D_205, C_204, A_203, B_206, B_202]: (k4_tarski(k4_tarski(A_203, B_202), C_204)=A_207 | k4_tarski(A_207, B_206)!=k4_mcart_1(A_203, B_202, C_204, D_205))), inference(superposition, [status(thm), theory('equality')], [c_939, c_4])).
% 3.10/1.55  tff(c_1067, plain, (![D_217, C_221, B_220, D_219, A_216, C_218, A_222, B_223]: (k4_tarski(k4_tarski(A_222, B_220), C_221)=k4_tarski(k4_tarski(A_216, B_223), C_218) | k4_mcart_1(A_222, B_220, C_221, D_217)!=k4_mcart_1(A_216, B_223, C_218, D_219))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1012])).
% 3.10/1.55  tff(c_1079, plain, (![A_222, B_220, C_221, D_217]: (k4_tarski(k4_tarski(A_222, B_220), C_221)=k4_tarski(k4_tarski('#skF_1', '#skF_2'), '#skF_7') | k4_mcart_1(A_222, B_220, C_221, D_217)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_934, c_1067])).
% 3.10/1.55  tff(c_1086, plain, (k4_tarski(k4_tarski('#skF_1', '#skF_2'), '#skF_7')=k4_tarski(k4_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_1079])).
% 3.10/1.55  tff(c_1123, plain, (![B_2, A_1]: (B_2='#skF_7' | k4_tarski(k4_tarski('#skF_1', '#skF_2'), '#skF_3')!=k4_tarski(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_1086, c_2])).
% 3.10/1.55  tff(c_1171, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_1123])).
% 3.10/1.55  tff(c_1173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_918, c_1171])).
% 3.10/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.55  
% 3.10/1.55  Inference rules
% 3.10/1.55  ----------------------
% 3.10/1.55  #Ref     : 29
% 3.10/1.55  #Sup     : 306
% 3.10/1.55  #Fact    : 0
% 3.10/1.55  #Define  : 0
% 3.10/1.55  #Split   : 3
% 3.10/1.55  #Chain   : 0
% 3.10/1.55  #Close   : 0
% 3.10/1.55  
% 3.10/1.55  Ordering : KBO
% 3.10/1.55  
% 3.10/1.55  Simplification rules
% 3.10/1.55  ----------------------
% 3.10/1.55  #Subsume      : 108
% 3.10/1.55  #Demod        : 167
% 3.10/1.55  #Tautology    : 133
% 3.10/1.55  #SimpNegUnit  : 4
% 3.10/1.55  #BackRed      : 22
% 3.10/1.55  
% 3.10/1.55  #Partial instantiations: 0
% 3.10/1.55  #Strategies tried      : 1
% 3.10/1.55  
% 3.10/1.55  Timing (in seconds)
% 3.10/1.55  ----------------------
% 3.10/1.55  Preprocessing        : 0.28
% 3.10/1.55  Parsing              : 0.14
% 3.10/1.55  CNF conversion       : 0.02
% 3.10/1.55  Main loop            : 0.45
% 3.10/1.55  Inferencing          : 0.17
% 3.10/1.55  Reduction            : 0.14
% 3.10/1.55  Demodulation         : 0.10
% 3.10/1.55  BG Simplification    : 0.02
% 3.10/1.55  Subsumption          : 0.08
% 3.10/1.55  Abstraction          : 0.03
% 3.10/1.55  MUC search           : 0.00
% 3.10/1.55  Cooper               : 0.00
% 3.10/1.55  Total                : 0.76
% 3.10/1.55  Index Insertion      : 0.00
% 3.10/1.55  Index Deletion       : 0.00
% 3.10/1.55  Index Matching       : 0.00
% 3.10/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
