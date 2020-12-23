%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:27 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 242 expanded)
%              Number of equality atoms :   82 ( 238 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
       => ( A = E
          & B = F
          & C = G
          & D = H ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k3_mcart_1(k4_tarski(A,B),C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
     => ( A = D
        & B = E
        & C = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_14,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_mcart_1(k4_tarski(A_11,B_12),C_13,D_14) = k4_mcart_1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_mcart_1(k4_tarski(A_41,B_42),C_43,D_44) = k4_mcart_1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( D_8 = A_5
      | k3_mcart_1(D_8,E_9,F_10) != k3_mcart_1(A_5,B_6,C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [B_70,C_68,A_67,F_66,D_65,E_71,D_69] :
      ( k4_tarski(A_67,B_70) = D_65
      | k4_mcart_1(A_67,B_70,C_68,D_69) != k3_mcart_1(D_65,E_71,F_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_210,plain,(
    ! [D_96,E_97,F_98] :
      ( k4_tarski('#skF_5','#skF_6') = D_96
      | k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_mcart_1(D_96,E_97,F_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_213,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k4_tarski(A_11,B_12) = k4_tarski('#skF_5','#skF_6')
      | k4_mcart_1(A_11,B_12,C_13,D_14) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_210])).

tff(c_229,plain,(
    k4_tarski('#skF_5','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_213])).

tff(c_4,plain,(
    ! [C_3,A_1,D_4,B_2] :
      ( C_3 = A_1
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [A_1,B_2] :
      ( A_1 = '#skF_5'
      | k4_tarski(A_1,B_2) != k4_tarski('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_4])).

tff(c_260,plain,(
    '#skF_5' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_244])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17,c_260])).

tff(c_263,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_274,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_264,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_269,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_16])).

tff(c_300,plain,(
    ! [A_137,B_138,C_139,D_140] : k3_mcart_1(k4_tarski(A_137,B_138),C_139,D_140) = k4_mcart_1(A_137,B_138,C_139,D_140) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( F_10 = C_7
      | k3_mcart_1(D_8,E_9,F_10) != k3_mcart_1(A_5,B_6,C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_327,plain,(
    ! [C_143,D_142,A_144,C_145,B_141,B_146,A_147] :
      ( D_142 = C_143
      | k4_mcart_1(A_147,B_146,C_145,D_142) != k3_mcart_1(A_144,B_141,C_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_6])).

tff(c_334,plain,(
    ! [C_148,A_149,B_150] :
      ( C_148 = '#skF_8'
      | k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_mcart_1(A_149,B_150,C_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_327])).

tff(c_337,plain,(
    ! [D_14,A_11,B_12,C_13] :
      ( D_14 = '#skF_8'
      | k4_mcart_1(A_11,B_12,C_13,D_14) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_334])).

tff(c_380,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_337])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_380])).

tff(c_383,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_390,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_384,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_385,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_269])).

tff(c_420,plain,(
    ! [A_210,B_211,C_212,D_213] : k3_mcart_1(k4_tarski(A_210,B_211),C_212,D_213) = k4_mcart_1(A_210,B_211,C_212,D_213) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_487,plain,(
    ! [A_252,B_250,C_249,E_253,D_247,D_251,F_248] :
      ( k4_tarski(A_252,B_250) = D_247
      | k4_mcart_1(A_252,B_250,C_249,D_251) != k3_mcart_1(D_247,E_253,F_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_10])).

tff(c_537,plain,(
    ! [D_258,E_259,F_260] :
      ( k4_tarski('#skF_1','#skF_6') = D_258
      | k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_mcart_1(D_258,E_259,F_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_487])).

tff(c_540,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k4_tarski(A_11,B_12) = k4_tarski('#skF_1','#skF_6')
      | k4_mcart_1(A_11,B_12,C_13,D_14) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_537])).

tff(c_554,plain,(
    k4_tarski('#skF_1','#skF_6') = k4_tarski('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_540])).

tff(c_2,plain,(
    ! [D_4,B_2,C_3,A_1] :
      ( D_4 = B_2
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_569,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_6'
      | k4_tarski(A_1,B_2) != k4_tarski('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_2])).

tff(c_585,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_569])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_585])).

tff(c_588,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_589,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_594,plain,(
    k4_mcart_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_385])).

tff(c_628,plain,(
    ! [A_299,B_300,C_301,D_302] : k3_mcart_1(k4_tarski(A_299,B_300),C_301,D_302) = k4_mcart_1(A_299,B_300,C_301,D_302) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( E_9 = B_6
      | k3_mcart_1(D_8,E_9,F_10) != k3_mcart_1(A_5,B_6,C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_662,plain,(
    ! [C_315,F_312,A_311,D_314,E_316,D_310,B_313] :
      ( E_316 = C_315
      | k4_mcart_1(A_311,B_313,C_315,D_314) != k3_mcart_1(D_310,E_316,F_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_8])).

tff(c_669,plain,(
    ! [E_317,D_318,F_319] :
      ( E_317 = '#skF_7'
      | k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_mcart_1(D_318,E_317,F_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_662])).

tff(c_672,plain,(
    ! [C_13,A_11,B_12,D_14] :
      ( C_13 = '#skF_7'
      | k4_mcart_1(A_11,B_12,C_13,D_14) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_669])).

tff(c_704,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_672])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:04:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.35  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.58/1.35  
% 2.58/1.35  %Foreground sorts:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Background operators:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Foreground operators:
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.35  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.58/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.58/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.35  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.58/1.35  
% 2.74/1.37  tff(f_52, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 2.74/1.37  tff(f_41, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k3_mcart_1(k4_tarski(A, B), C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_mcart_1)).
% 2.74/1.37  tff(f_39, axiom, (![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_mcart_1)).
% 2.74/1.37  tff(f_31, axiom, (![A, B, C, D]: ((k4_tarski(A, B) = k4_tarski(C, D)) => ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 2.74/1.37  tff(c_14, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.74/1.37  tff(c_17, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_14])).
% 2.74/1.37  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k3_mcart_1(k4_tarski(A_11, B_12), C_13, D_14)=k4_mcart_1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.37  tff(c_16, plain, (k4_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.74/1.37  tff(c_47, plain, (![A_41, B_42, C_43, D_44]: (k3_mcart_1(k4_tarski(A_41, B_42), C_43, D_44)=k4_mcart_1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.37  tff(c_10, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (D_8=A_5 | k3_mcart_1(D_8, E_9, F_10)!=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.37  tff(c_96, plain, (![B_70, C_68, A_67, F_66, D_65, E_71, D_69]: (k4_tarski(A_67, B_70)=D_65 | k4_mcart_1(A_67, B_70, C_68, D_69)!=k3_mcart_1(D_65, E_71, F_66))), inference(superposition, [status(thm), theory('equality')], [c_47, c_10])).
% 2.74/1.37  tff(c_210, plain, (![D_96, E_97, F_98]: (k4_tarski('#skF_5', '#skF_6')=D_96 | k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_mcart_1(D_96, E_97, F_98))), inference(superposition, [status(thm), theory('equality')], [c_16, c_96])).
% 2.74/1.37  tff(c_213, plain, (![A_11, B_12, C_13, D_14]: (k4_tarski(A_11, B_12)=k4_tarski('#skF_5', '#skF_6') | k4_mcart_1(A_11, B_12, C_13, D_14)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_210])).
% 2.74/1.37  tff(c_229, plain, (k4_tarski('#skF_5', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_213])).
% 2.74/1.37  tff(c_4, plain, (![C_3, A_1, D_4, B_2]: (C_3=A_1 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.37  tff(c_244, plain, (![A_1, B_2]: (A_1='#skF_5' | k4_tarski(A_1, B_2)!=k4_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_4])).
% 2.74/1.37  tff(c_260, plain, ('#skF_5'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_244])).
% 2.74/1.37  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17, c_260])).
% 2.74/1.37  tff(c_263, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_14])).
% 2.74/1.37  tff(c_274, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_263])).
% 2.74/1.37  tff(c_264, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_14])).
% 2.74/1.37  tff(c_269, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_16])).
% 2.74/1.37  tff(c_300, plain, (![A_137, B_138, C_139, D_140]: (k3_mcart_1(k4_tarski(A_137, B_138), C_139, D_140)=k4_mcart_1(A_137, B_138, C_139, D_140))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.37  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (F_10=C_7 | k3_mcart_1(D_8, E_9, F_10)!=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.37  tff(c_327, plain, (![C_143, D_142, A_144, C_145, B_141, B_146, A_147]: (D_142=C_143 | k4_mcart_1(A_147, B_146, C_145, D_142)!=k3_mcart_1(A_144, B_141, C_143))), inference(superposition, [status(thm), theory('equality')], [c_300, c_6])).
% 2.74/1.37  tff(c_334, plain, (![C_148, A_149, B_150]: (C_148='#skF_8' | k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_mcart_1(A_149, B_150, C_148))), inference(superposition, [status(thm), theory('equality')], [c_269, c_327])).
% 2.74/1.37  tff(c_337, plain, (![D_14, A_11, B_12, C_13]: (D_14='#skF_8' | k4_mcart_1(A_11, B_12, C_13, D_14)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_334])).
% 2.74/1.37  tff(c_380, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_337])).
% 2.74/1.37  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_380])).
% 2.74/1.37  tff(c_383, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_263])).
% 2.74/1.37  tff(c_390, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_383])).
% 2.74/1.37  tff(c_384, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_263])).
% 2.74/1.37  tff(c_385, plain, (k4_mcart_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_269])).
% 2.74/1.37  tff(c_420, plain, (![A_210, B_211, C_212, D_213]: (k3_mcart_1(k4_tarski(A_210, B_211), C_212, D_213)=k4_mcart_1(A_210, B_211, C_212, D_213))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.37  tff(c_487, plain, (![A_252, B_250, C_249, E_253, D_247, D_251, F_248]: (k4_tarski(A_252, B_250)=D_247 | k4_mcart_1(A_252, B_250, C_249, D_251)!=k3_mcart_1(D_247, E_253, F_248))), inference(superposition, [status(thm), theory('equality')], [c_420, c_10])).
% 2.74/1.37  tff(c_537, plain, (![D_258, E_259, F_260]: (k4_tarski('#skF_1', '#skF_6')=D_258 | k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_mcart_1(D_258, E_259, F_260))), inference(superposition, [status(thm), theory('equality')], [c_385, c_487])).
% 2.74/1.37  tff(c_540, plain, (![A_11, B_12, C_13, D_14]: (k4_tarski(A_11, B_12)=k4_tarski('#skF_1', '#skF_6') | k4_mcart_1(A_11, B_12, C_13, D_14)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_537])).
% 2.74/1.37  tff(c_554, plain, (k4_tarski('#skF_1', '#skF_6')=k4_tarski('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_540])).
% 2.74/1.37  tff(c_2, plain, (![D_4, B_2, C_3, A_1]: (D_4=B_2 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.37  tff(c_569, plain, (![B_2, A_1]: (B_2='#skF_6' | k4_tarski(A_1, B_2)!=k4_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_554, c_2])).
% 2.74/1.37  tff(c_585, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_569])).
% 2.74/1.37  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_585])).
% 2.74/1.37  tff(c_588, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_383])).
% 2.74/1.37  tff(c_589, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_383])).
% 2.74/1.37  tff(c_594, plain, (k4_mcart_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_385])).
% 2.74/1.37  tff(c_628, plain, (![A_299, B_300, C_301, D_302]: (k3_mcart_1(k4_tarski(A_299, B_300), C_301, D_302)=k4_mcart_1(A_299, B_300, C_301, D_302))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.37  tff(c_8, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (E_9=B_6 | k3_mcart_1(D_8, E_9, F_10)!=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.37  tff(c_662, plain, (![C_315, F_312, A_311, D_314, E_316, D_310, B_313]: (E_316=C_315 | k4_mcart_1(A_311, B_313, C_315, D_314)!=k3_mcart_1(D_310, E_316, F_312))), inference(superposition, [status(thm), theory('equality')], [c_628, c_8])).
% 2.74/1.37  tff(c_669, plain, (![E_317, D_318, F_319]: (E_317='#skF_7' | k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_mcart_1(D_318, E_317, F_319))), inference(superposition, [status(thm), theory('equality')], [c_594, c_662])).
% 2.74/1.37  tff(c_672, plain, (![C_13, A_11, B_12, D_14]: (C_13='#skF_7' | k4_mcart_1(A_11, B_12, C_13, D_14)!=k4_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_669])).
% 2.74/1.37  tff(c_704, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_672])).
% 2.74/1.37  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_588, c_704])).
% 2.74/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.37  
% 2.74/1.37  Inference rules
% 2.74/1.37  ----------------------
% 2.74/1.37  #Ref     : 39
% 2.74/1.37  #Sup     : 152
% 2.74/1.37  #Fact    : 0
% 2.74/1.37  #Define  : 0
% 2.74/1.37  #Split   : 3
% 2.74/1.37  #Chain   : 0
% 2.74/1.37  #Close   : 0
% 2.74/1.37  
% 2.74/1.37  Ordering : KBO
% 2.74/1.37  
% 2.74/1.37  Simplification rules
% 2.74/1.37  ----------------------
% 2.74/1.37  #Subsume      : 56
% 2.74/1.37  #Demod        : 25
% 2.74/1.37  #Tautology    : 75
% 2.74/1.37  #SimpNegUnit  : 4
% 2.74/1.37  #BackRed      : 15
% 2.74/1.37  
% 2.74/1.37  #Partial instantiations: 0
% 2.74/1.37  #Strategies tried      : 1
% 2.74/1.37  
% 2.74/1.37  Timing (in seconds)
% 2.74/1.37  ----------------------
% 2.74/1.37  Preprocessing        : 0.27
% 2.74/1.37  Parsing              : 0.14
% 2.74/1.37  CNF conversion       : 0.02
% 2.74/1.37  Main loop            : 0.34
% 2.74/1.37  Inferencing          : 0.13
% 2.74/1.37  Reduction            : 0.08
% 2.74/1.37  Demodulation         : 0.05
% 2.74/1.37  BG Simplification    : 0.02
% 2.74/1.37  Subsumption          : 0.09
% 2.74/1.37  Abstraction          : 0.02
% 2.74/1.37  MUC search           : 0.00
% 2.74/1.37  Cooper               : 0.00
% 2.74/1.37  Total                : 0.64
% 2.74/1.37  Index Insertion      : 0.00
% 2.74/1.37  Index Deletion       : 0.00
% 2.74/1.37  Index Matching       : 0.00
% 2.74/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
