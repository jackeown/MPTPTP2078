%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:44 EST 2020

% Result     : Theorem 5.63s
% Output     : CNFRefutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :   85 (1019 expanded)
%              Number of leaves         :   23 ( 345 expanded)
%              Depth                    :   19
%              Number of atoms          :  144 (2259 expanded)
%              Number of equality atoms :  124 (2076 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k7_enumset1 > k6_enumset1 > k4_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_enumset1(A,B,C),k4_enumset1(D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E,F,G,H,I,J] :
      ( J = k7_enumset1(A,B,C,D,E,F,G,H,I)
    <=> ! [K] :
          ( r2_hidden(K,J)
        <=> ~ ( K != A
              & K != B
              & K != C
              & K != D
              & K != E
              & K != F
              & K != G
              & K != H
              & K != I ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

tff(f_68,axiom,(
    ! [A] : k6_enumset1(A,A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).

tff(c_72,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_115,plain,(
    ! [A_127,F_121,H_126,E_123,D_125,B_124,G_122,C_120] : k2_xboole_0(k2_tarski(A_127,B_124),k4_enumset1(C_120,D_125,E_123,F_121,G_122,H_126)) = k6_enumset1(A_127,B_124,C_120,D_125,E_123,F_121,G_122,H_126) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,(
    ! [A_31,F_121,H_126,E_123,D_125,G_122,C_120] : k6_enumset1(A_31,A_31,C_120,D_125,E_123,F_121,G_122,H_126) = k2_xboole_0(k1_tarski(A_31),k4_enumset1(C_120,D_125,E_123,F_121,G_122,H_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_115])).

tff(c_74,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_186,plain,(
    ! [D_149,F_150,H_147,G_145,E_148,C_146] : k2_xboole_0(k1_tarski('#skF_3'),k4_enumset1(C_146,D_149,E_148,F_150,G_145,H_147)) = k6_enumset1('#skF_4','#skF_5',C_146,D_149,E_148,F_150,G_145,H_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_115])).

tff(c_196,plain,(
    ! [D_149,F_150,H_147,G_145,E_148,C_146] : k6_enumset1('#skF_3','#skF_3',C_146,D_149,E_148,F_150,G_145,H_147) = k6_enumset1('#skF_4','#skF_5',C_146,D_149,E_148,F_150,G_145,H_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_124])).

tff(c_64,plain,(
    ! [A_23,B_24,F_28,D_26,G_29,C_25,H_30,E_27] : k2_xboole_0(k2_tarski(A_23,B_24),k4_enumset1(C_25,D_26,E_27,F_28,G_29,H_30)) = k6_enumset1(A_23,B_24,C_25,D_26,E_27,F_28,G_29,H_30) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,(
    ! [I_128,G_133,E_130,F_131,D_132,H_129,C_134,B_135,A_136] : k2_xboole_0(k1_enumset1(A_136,B_135,C_134),k4_enumset1(D_132,E_130,F_131,G_133,H_129,I_128)) = k7_enumset1(A_136,B_135,C_134,D_132,E_130,F_131,G_133,H_129,I_128) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_139,plain,(
    ! [I_128,B_33,G_133,E_130,F_131,D_132,H_129,A_32] : k7_enumset1(A_32,A_32,B_33,D_132,E_130,F_131,G_133,H_129,I_128) = k2_xboole_0(k2_tarski(A_32,B_33),k4_enumset1(D_132,E_130,F_131,G_133,H_129,I_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_130])).

tff(c_235,plain,(
    ! [A_159,G_161,I_164,B_157,E_158,D_163,F_160,H_162] : k7_enumset1(A_159,A_159,B_157,D_163,E_158,F_160,G_161,H_162,I_164) = k6_enumset1(A_159,B_157,D_163,E_158,F_160,G_161,H_162,I_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_139])).

tff(c_16,plain,(
    ! [B_2,A_1,H_8,E_5,D_4,I_9,K_13,G_7,F_6] : r2_hidden(K_13,k7_enumset1(A_1,B_2,K_13,D_4,E_5,F_6,G_7,H_8,I_9)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_337,plain,(
    ! [H_197,D_195,E_200,I_194,F_201,G_196,B_198,A_199] : r2_hidden(B_198,k6_enumset1(A_199,B_198,D_195,E_200,F_201,G_196,H_197,I_194)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_16])).

tff(c_340,plain,(
    ! [D_149,F_150,H_147,G_145,E_148,C_146] : r2_hidden('#skF_3',k6_enumset1('#skF_4','#skF_5',C_146,D_149,E_148,F_150,G_145,H_147)) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_337])).

tff(c_142,plain,(
    ! [I_128,B_33,G_133,E_130,F_131,D_132,H_129,A_32] : k7_enumset1(A_32,A_32,B_33,D_132,E_130,F_131,G_133,H_129,I_128) = k6_enumset1(A_32,B_33,D_132,E_130,F_131,G_133,H_129,I_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_139])).

tff(c_271,plain,(
    ! [K_172,C_170,I_173,D_168,A_171,G_166,E_167,F_165,H_174,B_169] :
      ( K_172 = I_173
      | K_172 = H_174
      | K_172 = G_166
      | K_172 = F_165
      | K_172 = E_167
      | K_172 = D_168
      | K_172 = C_170
      | K_172 = B_169
      | K_172 = A_171
      | ~ r2_hidden(K_172,k7_enumset1(A_171,B_169,C_170,D_168,E_167,F_165,G_166,H_174,I_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_546,plain,(
    ! [A_337,G_339,K_343,D_341,E_336,I_342,H_340,F_338,B_335] :
      ( K_343 = I_342
      | K_343 = H_340
      | K_343 = G_339
      | K_343 = F_338
      | K_343 = E_336
      | K_343 = D_341
      | K_343 = B_335
      | K_343 = A_337
      | K_343 = A_337
      | ~ r2_hidden(K_343,k6_enumset1(A_337,B_335,D_341,E_336,F_338,G_339,H_340,I_342)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_271])).

tff(c_590,plain,(
    ! [D_149,F_150,H_147,G_145,E_148,C_146] :
      ( H_147 = '#skF_3'
      | G_145 = '#skF_3'
      | F_150 = '#skF_3'
      | E_148 = '#skF_3'
      | D_149 = '#skF_3'
      | C_146 = '#skF_3'
      | '#skF_5' = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_340,c_546])).

tff(c_603,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_127,plain,(
    ! [F_121,H_126,E_123,D_125,G_122,C_120] : k2_xboole_0(k1_tarski('#skF_3'),k4_enumset1(C_120,D_125,E_123,F_121,G_122,H_126)) = k6_enumset1('#skF_4','#skF_5',C_120,D_125,E_123,F_121,G_122,H_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_115])).

tff(c_610,plain,(
    ! [F_121,H_126,E_123,D_125,G_122,C_120] : k2_xboole_0(k1_tarski('#skF_4'),k4_enumset1(C_120,D_125,E_123,F_121,G_122,H_126)) = k6_enumset1('#skF_4','#skF_5',C_120,D_125,E_123,F_121,G_122,H_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_127])).

tff(c_666,plain,(
    ! [F_359,E_357,H_356,G_354,C_355,D_358] : k6_enumset1('#skF_4','#skF_5',C_355,D_358,E_357,F_359,G_354,H_356) = k6_enumset1('#skF_4','#skF_4',C_355,D_358,E_357,F_359,G_354,H_356) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_610])).

tff(c_262,plain,(
    ! [A_159,G_161,I_164,B_157,E_158,D_163,F_160,H_162] : r2_hidden(B_157,k6_enumset1(A_159,B_157,D_163,E_158,F_160,G_161,H_162,I_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_16])).

tff(c_717,plain,(
    ! [C_364,D_361,H_362,E_360,F_365,G_363] : r2_hidden('#skF_5',k6_enumset1('#skF_4','#skF_4',C_364,D_361,E_360,F_365,G_363,H_362)) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_262])).

tff(c_274,plain,(
    ! [I_128,B_33,K_172,G_133,E_130,F_131,D_132,H_129,A_32] :
      ( K_172 = I_128
      | K_172 = H_129
      | K_172 = G_133
      | K_172 = F_131
      | K_172 = E_130
      | K_172 = D_132
      | K_172 = B_33
      | K_172 = A_32
      | K_172 = A_32
      | ~ r2_hidden(K_172,k6_enumset1(A_32,B_33,D_132,E_130,F_131,G_133,H_129,I_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_271])).

tff(c_720,plain,(
    ! [C_364,D_361,H_362,E_360,F_365,G_363] :
      ( H_362 = '#skF_5'
      | G_363 = '#skF_5'
      | F_365 = '#skF_5'
      | E_360 = '#skF_5'
      | D_361 = '#skF_5'
      | C_364 = '#skF_5'
      | '#skF_5' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_717,c_274])).

tff(c_727,plain,(
    ! [C_364,D_361,H_362,E_360,F_365,G_363] :
      ( H_362 = '#skF_5'
      | G_363 = '#skF_5'
      | F_365 = '#skF_5'
      | E_360 = '#skF_5'
      | D_361 = '#skF_5'
      | C_364 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_72,c_720])).

tff(c_730,plain,(
    ! [C_366] : C_366 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_727])).

tff(c_903,plain,(
    ! [C_366] : C_366 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_72])).

tff(c_1085,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_903])).

tff(c_1086,plain,(
    ! [D_361,H_362,E_360,F_365,G_363] :
      ( E_360 = '#skF_5'
      | G_363 = '#skF_5'
      | H_362 = '#skF_5'
      | F_365 = '#skF_5'
      | D_361 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_727])).

tff(c_1088,plain,(
    ! [D_5591] : D_5591 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1086])).

tff(c_1261,plain,(
    ! [D_5591] : D_5591 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_72])).

tff(c_1279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1261,c_603])).

tff(c_1280,plain,(
    ! [H_362,E_360,G_363,F_365] :
      ( H_362 = '#skF_5'
      | E_360 = '#skF_5'
      | G_363 = '#skF_5'
      | F_365 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_1282,plain,(
    ! [F_8091] : F_8091 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1280])).

tff(c_1455,plain,(
    ! [F_8091] : F_8091 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_72])).

tff(c_1632,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1455])).

tff(c_1633,plain,(
    ! [E_360,H_362,G_363] :
      ( E_360 = '#skF_5'
      | H_362 = '#skF_5'
      | G_363 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_1280])).

tff(c_1637,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1633])).

tff(c_1634,plain,(
    ! [G_363] : G_363 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1633])).

tff(c_1828,plain,(
    ! [G_15703] : G_15703 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1637,c_1634])).

tff(c_1987,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1828,c_72])).

tff(c_1988,plain,(
    ! [E_360,H_362] :
      ( E_360 = '#skF_5'
      | H_362 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_1633])).

tff(c_1991,plain,(
    ! [H_18305] : H_18305 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1988])).

tff(c_2164,plain,(
    ! [H_18305] : H_18305 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1991,c_72])).

tff(c_2341,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2164])).

tff(c_2343,plain,(
    ! [E_23356] : E_23356 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1988])).

tff(c_2516,plain,(
    ! [E_23356] : E_23356 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2343,c_72])).

tff(c_2698,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2516])).

tff(c_2700,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_143,plain,(
    ! [H_140,G_137,A_138,D_142,F_143,E_141,C_139] : k6_enumset1(A_138,A_138,C_139,D_142,E_141,F_143,G_137,H_140) = k2_xboole_0(k1_tarski(A_138),k4_enumset1(C_139,D_142,E_141,F_143,G_137,H_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_115])).

tff(c_70,plain,(
    ! [A_34] : k6_enumset1(A_34,A_34,A_34,A_34,A_34,A_34,A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_153,plain,(
    ! [H_140] : k2_xboole_0(k1_tarski(H_140),k4_enumset1(H_140,H_140,H_140,H_140,H_140,H_140)) = k1_tarski(H_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_70])).

tff(c_193,plain,(
    k6_enumset1('#skF_4','#skF_5','#skF_3','#skF_3','#skF_3','#skF_3','#skF_3','#skF_3') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_153])).

tff(c_20,plain,(
    ! [B_2,C_3,H_8,E_5,D_4,I_9,K_13,G_7,F_6] : r2_hidden(K_13,k7_enumset1(K_13,B_2,C_3,D_4,E_5,F_6,G_7,H_8,I_9)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_400,plain,(
    ! [H_239,A_241,B_240,E_242,F_243,D_237,G_238,I_236] : r2_hidden(A_241,k6_enumset1(A_241,B_240,D_237,E_242,F_243,G_238,H_239,I_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_20])).

tff(c_406,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_400])).

tff(c_2897,plain,(
    ! [K_28542,A_28543] :
      ( K_28542 = A_28543
      | K_28542 = A_28543
      | K_28542 = A_28543
      | K_28542 = A_28543
      | K_28542 = A_28543
      | K_28542 = A_28543
      | K_28542 = A_28543
      | K_28542 = A_28543
      | K_28542 = A_28543
      | ~ r2_hidden(K_28542,k1_tarski(A_28543)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_546])).

tff(c_2900,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_406,c_2897])).

tff(c_2907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2700,c_2700,c_2700,c_2700,c_2700,c_2700,c_2700,c_2700,c_2700,c_2900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:27:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.63/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.63/2.05  
% 5.63/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.63/2.05  %$ r2_hidden > k7_enumset1 > k6_enumset1 > k4_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 5.63/2.05  
% 5.63/2.05  %Foreground sorts:
% 5.63/2.05  
% 5.63/2.05  
% 5.63/2.05  %Background operators:
% 5.63/2.05  
% 5.63/2.05  
% 5.63/2.05  %Foreground operators:
% 5.63/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.63/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.63/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.63/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.63/2.05  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.63/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.63/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.63/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.63/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.63/2.05  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.63/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.63/2.05  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.63/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.63/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.63/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.63/2.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.63/2.05  
% 6.03/2.07  tff(f_73, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 6.03/2.07  tff(f_64, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.03/2.07  tff(f_62, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 6.03/2.07  tff(f_66, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.03/2.07  tff(f_60, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_enumset1(A, B, C), k4_enumset1(D, E, F, G, H, I)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 6.03/2.07  tff(f_58, axiom, (![A, B, C, D, E, F, G, H, I, J]: ((J = k7_enumset1(A, B, C, D, E, F, G, H, I)) <=> (![K]: (r2_hidden(K, J) <=> ~((((((((~(K = A) & ~(K = B)) & ~(K = C)) & ~(K = D)) & ~(K = E)) & ~(K = F)) & ~(K = G)) & ~(K = H)) & ~(K = I)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 6.03/2.07  tff(f_68, axiom, (![A]: (k6_enumset1(A, A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_enumset1)).
% 6.03/2.07  tff(c_72, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.03/2.07  tff(c_66, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.03/2.07  tff(c_115, plain, (![A_127, F_121, H_126, E_123, D_125, B_124, G_122, C_120]: (k2_xboole_0(k2_tarski(A_127, B_124), k4_enumset1(C_120, D_125, E_123, F_121, G_122, H_126))=k6_enumset1(A_127, B_124, C_120, D_125, E_123, F_121, G_122, H_126))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.03/2.07  tff(c_124, plain, (![A_31, F_121, H_126, E_123, D_125, G_122, C_120]: (k6_enumset1(A_31, A_31, C_120, D_125, E_123, F_121, G_122, H_126)=k2_xboole_0(k1_tarski(A_31), k4_enumset1(C_120, D_125, E_123, F_121, G_122, H_126)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_115])).
% 6.03/2.07  tff(c_74, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.03/2.07  tff(c_186, plain, (![D_149, F_150, H_147, G_145, E_148, C_146]: (k2_xboole_0(k1_tarski('#skF_3'), k4_enumset1(C_146, D_149, E_148, F_150, G_145, H_147))=k6_enumset1('#skF_4', '#skF_5', C_146, D_149, E_148, F_150, G_145, H_147))), inference(superposition, [status(thm), theory('equality')], [c_74, c_115])).
% 6.03/2.07  tff(c_196, plain, (![D_149, F_150, H_147, G_145, E_148, C_146]: (k6_enumset1('#skF_3', '#skF_3', C_146, D_149, E_148, F_150, G_145, H_147)=k6_enumset1('#skF_4', '#skF_5', C_146, D_149, E_148, F_150, G_145, H_147))), inference(superposition, [status(thm), theory('equality')], [c_186, c_124])).
% 6.03/2.07  tff(c_64, plain, (![A_23, B_24, F_28, D_26, G_29, C_25, H_30, E_27]: (k2_xboole_0(k2_tarski(A_23, B_24), k4_enumset1(C_25, D_26, E_27, F_28, G_29, H_30))=k6_enumset1(A_23, B_24, C_25, D_26, E_27, F_28, G_29, H_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.03/2.07  tff(c_68, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.03/2.07  tff(c_130, plain, (![I_128, G_133, E_130, F_131, D_132, H_129, C_134, B_135, A_136]: (k2_xboole_0(k1_enumset1(A_136, B_135, C_134), k4_enumset1(D_132, E_130, F_131, G_133, H_129, I_128))=k7_enumset1(A_136, B_135, C_134, D_132, E_130, F_131, G_133, H_129, I_128))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.03/2.07  tff(c_139, plain, (![I_128, B_33, G_133, E_130, F_131, D_132, H_129, A_32]: (k7_enumset1(A_32, A_32, B_33, D_132, E_130, F_131, G_133, H_129, I_128)=k2_xboole_0(k2_tarski(A_32, B_33), k4_enumset1(D_132, E_130, F_131, G_133, H_129, I_128)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_130])).
% 6.03/2.07  tff(c_235, plain, (![A_159, G_161, I_164, B_157, E_158, D_163, F_160, H_162]: (k7_enumset1(A_159, A_159, B_157, D_163, E_158, F_160, G_161, H_162, I_164)=k6_enumset1(A_159, B_157, D_163, E_158, F_160, G_161, H_162, I_164))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_139])).
% 6.03/2.07  tff(c_16, plain, (![B_2, A_1, H_8, E_5, D_4, I_9, K_13, G_7, F_6]: (r2_hidden(K_13, k7_enumset1(A_1, B_2, K_13, D_4, E_5, F_6, G_7, H_8, I_9)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.03/2.07  tff(c_337, plain, (![H_197, D_195, E_200, I_194, F_201, G_196, B_198, A_199]: (r2_hidden(B_198, k6_enumset1(A_199, B_198, D_195, E_200, F_201, G_196, H_197, I_194)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_16])).
% 6.03/2.07  tff(c_340, plain, (![D_149, F_150, H_147, G_145, E_148, C_146]: (r2_hidden('#skF_3', k6_enumset1('#skF_4', '#skF_5', C_146, D_149, E_148, F_150, G_145, H_147)))), inference(superposition, [status(thm), theory('equality')], [c_196, c_337])).
% 6.03/2.07  tff(c_142, plain, (![I_128, B_33, G_133, E_130, F_131, D_132, H_129, A_32]: (k7_enumset1(A_32, A_32, B_33, D_132, E_130, F_131, G_133, H_129, I_128)=k6_enumset1(A_32, B_33, D_132, E_130, F_131, G_133, H_129, I_128))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_139])).
% 6.03/2.07  tff(c_271, plain, (![K_172, C_170, I_173, D_168, A_171, G_166, E_167, F_165, H_174, B_169]: (K_172=I_173 | K_172=H_174 | K_172=G_166 | K_172=F_165 | K_172=E_167 | K_172=D_168 | K_172=C_170 | K_172=B_169 | K_172=A_171 | ~r2_hidden(K_172, k7_enumset1(A_171, B_169, C_170, D_168, E_167, F_165, G_166, H_174, I_173)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.03/2.07  tff(c_546, plain, (![A_337, G_339, K_343, D_341, E_336, I_342, H_340, F_338, B_335]: (K_343=I_342 | K_343=H_340 | K_343=G_339 | K_343=F_338 | K_343=E_336 | K_343=D_341 | K_343=B_335 | K_343=A_337 | K_343=A_337 | ~r2_hidden(K_343, k6_enumset1(A_337, B_335, D_341, E_336, F_338, G_339, H_340, I_342)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_271])).
% 6.03/2.07  tff(c_590, plain, (![D_149, F_150, H_147, G_145, E_148, C_146]: (H_147='#skF_3' | G_145='#skF_3' | F_150='#skF_3' | E_148='#skF_3' | D_149='#skF_3' | C_146='#skF_3' | '#skF_5'='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_340, c_546])).
% 6.03/2.07  tff(c_603, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_590])).
% 6.03/2.07  tff(c_127, plain, (![F_121, H_126, E_123, D_125, G_122, C_120]: (k2_xboole_0(k1_tarski('#skF_3'), k4_enumset1(C_120, D_125, E_123, F_121, G_122, H_126))=k6_enumset1('#skF_4', '#skF_5', C_120, D_125, E_123, F_121, G_122, H_126))), inference(superposition, [status(thm), theory('equality')], [c_74, c_115])).
% 6.03/2.07  tff(c_610, plain, (![F_121, H_126, E_123, D_125, G_122, C_120]: (k2_xboole_0(k1_tarski('#skF_4'), k4_enumset1(C_120, D_125, E_123, F_121, G_122, H_126))=k6_enumset1('#skF_4', '#skF_5', C_120, D_125, E_123, F_121, G_122, H_126))), inference(demodulation, [status(thm), theory('equality')], [c_603, c_127])).
% 6.03/2.07  tff(c_666, plain, (![F_359, E_357, H_356, G_354, C_355, D_358]: (k6_enumset1('#skF_4', '#skF_5', C_355, D_358, E_357, F_359, G_354, H_356)=k6_enumset1('#skF_4', '#skF_4', C_355, D_358, E_357, F_359, G_354, H_356))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_610])).
% 6.03/2.07  tff(c_262, plain, (![A_159, G_161, I_164, B_157, E_158, D_163, F_160, H_162]: (r2_hidden(B_157, k6_enumset1(A_159, B_157, D_163, E_158, F_160, G_161, H_162, I_164)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_16])).
% 6.03/2.07  tff(c_717, plain, (![C_364, D_361, H_362, E_360, F_365, G_363]: (r2_hidden('#skF_5', k6_enumset1('#skF_4', '#skF_4', C_364, D_361, E_360, F_365, G_363, H_362)))), inference(superposition, [status(thm), theory('equality')], [c_666, c_262])).
% 6.03/2.07  tff(c_274, plain, (![I_128, B_33, K_172, G_133, E_130, F_131, D_132, H_129, A_32]: (K_172=I_128 | K_172=H_129 | K_172=G_133 | K_172=F_131 | K_172=E_130 | K_172=D_132 | K_172=B_33 | K_172=A_32 | K_172=A_32 | ~r2_hidden(K_172, k6_enumset1(A_32, B_33, D_132, E_130, F_131, G_133, H_129, I_128)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_271])).
% 6.03/2.07  tff(c_720, plain, (![C_364, D_361, H_362, E_360, F_365, G_363]: (H_362='#skF_5' | G_363='#skF_5' | F_365='#skF_5' | E_360='#skF_5' | D_361='#skF_5' | C_364='#skF_5' | '#skF_5'='#skF_4')), inference(resolution, [status(thm)], [c_717, c_274])).
% 6.03/2.07  tff(c_727, plain, (![C_364, D_361, H_362, E_360, F_365, G_363]: (H_362='#skF_5' | G_363='#skF_5' | F_365='#skF_5' | E_360='#skF_5' | D_361='#skF_5' | C_364='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_72, c_720])).
% 6.03/2.07  tff(c_730, plain, (![C_366]: (C_366='#skF_5')), inference(splitLeft, [status(thm)], [c_727])).
% 6.03/2.07  tff(c_903, plain, (![C_366]: (C_366!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_730, c_72])).
% 6.03/2.07  tff(c_1085, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_903])).
% 6.03/2.07  tff(c_1086, plain, (![D_361, H_362, E_360, F_365, G_363]: (E_360='#skF_5' | G_363='#skF_5' | H_362='#skF_5' | F_365='#skF_5' | D_361='#skF_5')), inference(splitRight, [status(thm)], [c_727])).
% 6.03/2.07  tff(c_1088, plain, (![D_5591]: (D_5591='#skF_5')), inference(splitLeft, [status(thm)], [c_1086])).
% 6.03/2.07  tff(c_1261, plain, (![D_5591]: (D_5591!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1088, c_72])).
% 6.03/2.07  tff(c_1279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1261, c_603])).
% 6.03/2.07  tff(c_1280, plain, (![H_362, E_360, G_363, F_365]: (H_362='#skF_5' | E_360='#skF_5' | G_363='#skF_5' | F_365='#skF_5')), inference(splitRight, [status(thm)], [c_1086])).
% 6.03/2.07  tff(c_1282, plain, (![F_8091]: (F_8091='#skF_5')), inference(splitLeft, [status(thm)], [c_1280])).
% 6.03/2.07  tff(c_1455, plain, (![F_8091]: (F_8091!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1282, c_72])).
% 6.03/2.07  tff(c_1632, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1455])).
% 6.03/2.07  tff(c_1633, plain, (![E_360, H_362, G_363]: (E_360='#skF_5' | H_362='#skF_5' | G_363='#skF_5')), inference(splitRight, [status(thm)], [c_1280])).
% 6.03/2.07  tff(c_1637, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1633])).
% 6.03/2.07  tff(c_1634, plain, (![G_363]: (G_363='#skF_5')), inference(splitLeft, [status(thm)], [c_1633])).
% 6.03/2.07  tff(c_1828, plain, (![G_15703]: (G_15703='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1637, c_1634])).
% 6.03/2.07  tff(c_1987, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1828, c_72])).
% 6.03/2.07  tff(c_1988, plain, (![E_360, H_362]: (E_360='#skF_5' | H_362='#skF_5')), inference(splitRight, [status(thm)], [c_1633])).
% 6.03/2.07  tff(c_1991, plain, (![H_18305]: (H_18305='#skF_5')), inference(splitLeft, [status(thm)], [c_1988])).
% 6.03/2.07  tff(c_2164, plain, (![H_18305]: (H_18305!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1991, c_72])).
% 6.03/2.07  tff(c_2341, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_2164])).
% 6.03/2.07  tff(c_2343, plain, (![E_23356]: (E_23356='#skF_5')), inference(splitRight, [status(thm)], [c_1988])).
% 6.03/2.07  tff(c_2516, plain, (![E_23356]: (E_23356!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2343, c_72])).
% 6.03/2.07  tff(c_2698, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_2516])).
% 6.03/2.07  tff(c_2700, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_590])).
% 6.03/2.07  tff(c_143, plain, (![H_140, G_137, A_138, D_142, F_143, E_141, C_139]: (k6_enumset1(A_138, A_138, C_139, D_142, E_141, F_143, G_137, H_140)=k2_xboole_0(k1_tarski(A_138), k4_enumset1(C_139, D_142, E_141, F_143, G_137, H_140)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_115])).
% 6.03/2.07  tff(c_70, plain, (![A_34]: (k6_enumset1(A_34, A_34, A_34, A_34, A_34, A_34, A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.03/2.07  tff(c_153, plain, (![H_140]: (k2_xboole_0(k1_tarski(H_140), k4_enumset1(H_140, H_140, H_140, H_140, H_140, H_140))=k1_tarski(H_140))), inference(superposition, [status(thm), theory('equality')], [c_143, c_70])).
% 6.03/2.07  tff(c_193, plain, (k6_enumset1('#skF_4', '#skF_5', '#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_186, c_153])).
% 6.03/2.07  tff(c_20, plain, (![B_2, C_3, H_8, E_5, D_4, I_9, K_13, G_7, F_6]: (r2_hidden(K_13, k7_enumset1(K_13, B_2, C_3, D_4, E_5, F_6, G_7, H_8, I_9)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.03/2.07  tff(c_400, plain, (![H_239, A_241, B_240, E_242, F_243, D_237, G_238, I_236]: (r2_hidden(A_241, k6_enumset1(A_241, B_240, D_237, E_242, F_243, G_238, H_239, I_236)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_20])).
% 6.03/2.07  tff(c_406, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_400])).
% 6.03/2.07  tff(c_2897, plain, (![K_28542, A_28543]: (K_28542=A_28543 | K_28542=A_28543 | K_28542=A_28543 | K_28542=A_28543 | K_28542=A_28543 | K_28542=A_28543 | K_28542=A_28543 | K_28542=A_28543 | K_28542=A_28543 | ~r2_hidden(K_28542, k1_tarski(A_28543)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_546])).
% 6.03/2.07  tff(c_2900, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_406, c_2897])).
% 6.03/2.07  tff(c_2907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2700, c_2700, c_2700, c_2700, c_2700, c_2700, c_2700, c_2700, c_2700, c_2900])).
% 6.03/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.07  
% 6.03/2.07  Inference rules
% 6.03/2.07  ----------------------
% 6.03/2.07  #Ref     : 4
% 6.03/2.07  #Sup     : 1090
% 6.03/2.07  #Fact    : 0
% 6.03/2.07  #Define  : 0
% 6.03/2.07  #Split   : 7
% 6.03/2.07  #Chain   : 0
% 6.03/2.07  #Close   : 0
% 6.03/2.07  
% 6.03/2.07  Ordering : KBO
% 6.03/2.07  
% 6.03/2.07  Simplification rules
% 6.03/2.07  ----------------------
% 6.03/2.07  #Subsume      : 148
% 6.03/2.07  #Demod        : 211
% 6.03/2.08  #Tautology    : 233
% 6.03/2.08  #SimpNegUnit  : 6
% 6.03/2.08  #BackRed      : 16
% 6.03/2.08  
% 6.03/2.08  #Partial instantiations: 802
% 6.03/2.08  #Strategies tried      : 1
% 6.03/2.08  
% 6.03/2.08  Timing (in seconds)
% 6.03/2.08  ----------------------
% 6.03/2.08  Preprocessing        : 0.36
% 6.03/2.08  Parsing              : 0.17
% 6.03/2.08  CNF conversion       : 0.03
% 6.03/2.08  Main loop            : 0.93
% 6.03/2.08  Inferencing          : 0.39
% 6.03/2.08  Reduction            : 0.28
% 6.03/2.08  Demodulation         : 0.22
% 6.03/2.08  BG Simplification    : 0.05
% 6.03/2.08  Subsumption          : 0.17
% 6.03/2.08  Abstraction          : 0.06
% 6.03/2.08  MUC search           : 0.00
% 6.03/2.08  Cooper               : 0.00
% 6.03/2.08  Total                : 1.33
% 6.03/2.08  Index Insertion      : 0.00
% 6.03/2.08  Index Deletion       : 0.00
% 6.03/2.08  Index Matching       : 0.00
% 6.03/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
