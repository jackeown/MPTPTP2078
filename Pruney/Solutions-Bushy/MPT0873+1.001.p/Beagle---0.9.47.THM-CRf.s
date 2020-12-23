%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0873+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:59 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 134 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 270 expanded)
%              Number of equality atoms :   94 ( 266 expanded)
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

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
       => ( A = E
          & B = F
          & C = G
          & D = H ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
     => ( A = D
        & B = E
        & C = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

tff(c_14,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k4_tarski(k3_mcart_1(A_1,B_2,C_3),D_4) = k4_mcart_1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47,plain,(
    ! [A_41,B_42,C_43,D_44] : k4_tarski(k3_mcart_1(A_41,B_42,C_43),D_44) = k4_mcart_1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [D_14,B_12,C_13,A_11] :
      ( D_14 = B_12
      | k4_tarski(C_13,D_14) != k4_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_68,plain,(
    ! [C_46,B_49,A_45,A_48,B_50,D_47] :
      ( D_47 = B_49
      | k4_tarski(A_48,B_49) != k4_mcart_1(A_45,B_50,C_46,D_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_75,plain,(
    ! [B_51,A_52] :
      ( B_51 = '#skF_8'
      | k4_tarski(A_52,B_51) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_68])).

tff(c_78,plain,(
    ! [D_4,A_1,B_2,C_3] :
      ( D_4 = '#skF_8'
      | k4_mcart_1(A_1,B_2,C_3,D_4) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_92,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_78])).

tff(c_101,plain,(
    k4_mcart_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_16])).

tff(c_12,plain,(
    ! [C_13,A_11,D_14,B_12] :
      ( C_13 = A_11
      | k4_tarski(C_13,D_14) != k4_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [B_70,A_65,C_67,D_68,C_66,D_69] :
      ( k3_mcart_1(A_65,B_70,C_67) = C_66
      | k4_tarski(C_66,D_69) != k4_mcart_1(A_65,B_70,C_67,D_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_12])).

tff(c_136,plain,(
    ! [D_74,B_78,B_73,A_77,C_75,C_79,A_80,D_76] :
      ( k3_mcart_1(A_80,B_78,C_79) = k3_mcart_1(A_77,B_73,C_75)
      | k4_mcart_1(A_80,B_78,C_79,D_76) != k4_mcart_1(A_77,B_73,C_75,D_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_139,plain,(
    ! [A_77,B_73,C_75,D_74] :
      ( k3_mcart_1(A_77,B_73,C_75) = k3_mcart_1('#skF_5','#skF_6','#skF_7')
      | k4_mcart_1(A_77,B_73,C_75,D_74) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_136])).

tff(c_145,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_139])).

tff(c_8,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( D_8 = A_5
      | k3_mcart_1(D_8,E_9,F_10) != k3_mcart_1(A_5,B_6,C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_166,plain,(
    ! [A_5,B_6,C_7] :
      ( A_5 = '#skF_5'
      | k3_mcart_1(A_5,B_6,C_7) != k3_mcart_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_8])).

tff(c_257,plain,(
    '#skF_5' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_166])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17,c_257])).

tff(c_260,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_266,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_261,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_292,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_16])).

tff(c_297,plain,(
    ! [A_115,B_116,C_117,D_118] : k4_tarski(k3_mcart_1(A_115,B_116,C_117),D_118) = k4_mcart_1(A_115,B_116,C_117,D_118) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_318,plain,(
    ! [B_122,A_119,B_121,A_123,D_124,C_120] :
      ( D_124 = B_121
      | k4_tarski(A_119,B_121) != k4_mcart_1(A_123,B_122,C_120,D_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_10])).

tff(c_325,plain,(
    ! [B_125,A_126] :
      ( B_125 = '#skF_8'
      | k4_tarski(A_126,B_125) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_318])).

tff(c_328,plain,(
    ! [D_4,A_1,B_2,C_3] :
      ( D_4 = '#skF_8'
      | k4_mcart_1(A_1,B_2,C_3,D_4) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_325])).

tff(c_349,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_328])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_349])).

tff(c_352,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_358,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_353,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_359,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_261,c_16])).

tff(c_389,plain,(
    ! [A_167,B_168,C_169,D_170] : k4_tarski(k3_mcart_1(A_167,B_168,C_169),D_170) = k4_mcart_1(A_167,B_168,C_169,D_170) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_428,plain,(
    ! [B_188,C_185,A_187,D_189,D_190,C_186] :
      ( k3_mcart_1(A_187,B_188,C_186) = C_185
      | k4_tarski(C_185,D_189) != k4_mcart_1(A_187,B_188,C_186,D_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_12])).

tff(c_435,plain,(
    ! [C_191,D_192] :
      ( k3_mcart_1('#skF_1','#skF_6','#skF_7') = C_191
      | k4_tarski(C_191,D_192) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_428])).

tff(c_438,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k3_mcart_1(A_1,B_2,C_3) = k3_mcart_1('#skF_1','#skF_6','#skF_7')
      | k4_mcart_1(A_1,B_2,C_3,D_4) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_435])).

tff(c_452,plain,(
    k3_mcart_1('#skF_1','#skF_6','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_438])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( E_9 = B_6
      | k3_mcart_1(D_8,E_9,F_10) != k3_mcart_1(A_5,B_6,C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_482,plain,(
    ! [E_9,D_8,F_10] :
      ( E_9 = '#skF_6'
      | k3_mcart_1(D_8,E_9,F_10) != k3_mcart_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_6])).

tff(c_520,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_482])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_520])).

tff(c_523,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_524,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_525,plain,(
    k4_mcart_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_353,c_16])).

tff(c_530,plain,(
    k4_mcart_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_525])).

tff(c_564,plain,(
    ! [A_232,B_233,C_234,D_235] : k4_tarski(k3_mcart_1(A_232,B_233,C_234),D_235) = k4_mcart_1(A_232,B_233,C_234,D_235) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_603,plain,(
    ! [B_250,C_253,A_254,D_255,C_251,D_252] :
      ( k3_mcart_1(A_254,B_250,C_253) = C_251
      | k4_tarski(C_251,D_255) != k4_mcart_1(A_254,B_250,C_253,D_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_12])).

tff(c_610,plain,(
    ! [C_256,D_257] :
      ( k3_mcart_1('#skF_1','#skF_2','#skF_7') = C_256
      | k4_tarski(C_256,D_257) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_603])).

tff(c_613,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k3_mcart_1(A_1,B_2,C_3) = k3_mcart_1('#skF_1','#skF_2','#skF_7')
      | k4_mcart_1(A_1,B_2,C_3,D_4) != k4_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_610])).

tff(c_627,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_7') = k3_mcart_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_613])).

tff(c_4,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( F_10 = C_7
      | k3_mcart_1(D_8,E_9,F_10) != k3_mcart_1(A_5,B_6,C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_657,plain,(
    ! [F_10,D_8,E_9] :
      ( F_10 = '#skF_7'
      | k3_mcart_1(D_8,E_9,F_10) != k3_mcart_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_4])).

tff(c_696,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_657])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_696])).

%------------------------------------------------------------------------------
