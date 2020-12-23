%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:57 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 8.17s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 538 expanded)
%              Number of leaves         :   29 ( 190 expanded)
%              Depth                    :   16
%              Number of atoms          :  195 ( 768 expanded)
%              Number of equality atoms :   81 ( 401 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_40,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_114,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_119,plain,(
    ! [A_37] : k3_xboole_0(k1_xboole_0,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_37] : k3_xboole_0(A_37,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_2])).

tff(c_227,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_236,plain,(
    ! [A_37] : k5_xboole_0(A_37,k1_xboole_0) = k4_xboole_0(A_37,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_227])).

tff(c_248,plain,(
    ! [A_37] : k5_xboole_0(A_37,k1_xboole_0) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_236])).

tff(c_118,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_239,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_227])).

tff(c_259,plain,(
    ! [A_56] : k4_xboole_0(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_239])).

tff(c_50,plain,(
    ! [B_29,A_28] :
      ( ~ r2_hidden(B_29,A_28)
      | k4_xboole_0(A_28,k1_tarski(B_29)) != A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_285,plain,(
    ! [B_29] : ~ r2_hidden(B_29,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_50])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_581,plain,(
    ! [A_106,B_107,C_108] :
      ( r2_hidden('#skF_1'(A_106,B_107,C_108),A_106)
      | r2_hidden('#skF_2'(A_106,B_107,C_108),C_108)
      | k3_xboole_0(A_106,B_107) = C_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5177,plain,(
    ! [A_254,B_255,A_256,B_257] :
      ( r2_hidden('#skF_2'(A_254,B_255,k3_xboole_0(A_256,B_257)),A_256)
      | r2_hidden('#skF_1'(A_254,B_255,k3_xboole_0(A_256,B_257)),A_254)
      | k3_xboole_0(A_256,B_257) = k3_xboole_0(A_254,B_255) ) ),
    inference(resolution,[status(thm)],[c_581,c_8])).

tff(c_5308,plain,(
    ! [A_254,B_255,A_16] :
      ( r2_hidden('#skF_2'(A_254,B_255,k3_xboole_0(k1_xboole_0,A_16)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_254,B_255,k1_xboole_0),A_254)
      | k3_xboole_0(k1_xboole_0,A_16) = k3_xboole_0(A_254,B_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_5177])).

tff(c_5356,plain,(
    ! [A_254,B_255] :
      ( r2_hidden('#skF_2'(A_254,B_255,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_254,B_255,k1_xboole_0),A_254)
      | k3_xboole_0(A_254,B_255) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_118,c_5308])).

tff(c_5358,plain,(
    ! [A_258,B_259] :
      ( r2_hidden('#skF_1'(A_258,B_259,k1_xboole_0),A_258)
      | k3_xboole_0(A_258,B_259) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_5356])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k3_xboole_0(A_3,B_4))
      | ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,k1_tarski(B_29)) = A_28
      | r2_hidden(B_29,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_409,plain,(
    ! [A_79,C_80,B_81] :
      ( ~ r2_hidden(A_79,C_80)
      | ~ r2_hidden(A_79,B_81)
      | ~ r2_hidden(A_79,k5_xboole_0(B_81,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_480,plain,(
    ! [A_91,A_92,B_93] :
      ( ~ r2_hidden(A_91,k3_xboole_0(A_92,B_93))
      | ~ r2_hidden(A_91,A_92)
      | ~ r2_hidden(A_91,k4_xboole_0(A_92,B_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_409])).

tff(c_1804,plain,(
    ! [A_156,A_157,B_158] :
      ( ~ r2_hidden(A_156,k3_xboole_0(A_157,k1_tarski(B_158)))
      | ~ r2_hidden(A_156,A_157)
      | ~ r2_hidden(A_156,A_157)
      | r2_hidden(B_158,A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_480])).

tff(c_1901,plain,(
    ! [B_158,A_3,D_8] :
      ( r2_hidden(B_158,A_3)
      | ~ r2_hidden(D_8,k1_tarski(B_158))
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_1804])).

tff(c_5839,plain,(
    ! [B_272,A_273,B_274] :
      ( r2_hidden(B_272,A_273)
      | ~ r2_hidden('#skF_1'(k1_tarski(B_272),B_274,k1_xboole_0),A_273)
      | k3_xboole_0(k1_tarski(B_272),B_274) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5358,c_1901])).

tff(c_5863,plain,(
    ! [B_272,B_4] :
      ( r2_hidden(B_272,B_4)
      | r2_hidden('#skF_2'(k1_tarski(B_272),B_4,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k1_tarski(B_272),B_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_5839])).

tff(c_5909,plain,(
    ! [B_275,B_276] :
      ( r2_hidden(B_275,B_276)
      | k3_xboole_0(k1_tarski(B_275),B_276) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_5863])).

tff(c_6054,plain,(
    ! [B_275,B_276] :
      ( k5_xboole_0(k1_tarski(B_275),k1_xboole_0) = k4_xboole_0(k1_tarski(B_275),B_276)
      | r2_hidden(B_275,B_276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5909,c_34])).

tff(c_7976,plain,(
    ! [B_303,B_304] :
      ( k4_xboole_0(k1_tarski(B_303),B_304) = k1_tarski(B_303)
      | r2_hidden(B_303,B_304) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_6054])).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_226,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_8008,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7976,c_226])).

tff(c_8045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8008])).

tff(c_8046,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8052,plain,(
    ! [A_305,B_306] : k5_xboole_0(A_305,k3_xboole_0(A_305,B_306)) = k4_xboole_0(A_305,B_306) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8061,plain,(
    ! [A_37] : k5_xboole_0(A_37,k1_xboole_0) = k4_xboole_0(A_37,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8052])).

tff(c_8073,plain,(
    ! [A_37] : k5_xboole_0(A_37,k1_xboole_0) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8061])).

tff(c_8878,plain,(
    ! [A_377,B_378,C_379] :
      ( r2_hidden('#skF_1'(A_377,B_378,C_379),A_377)
      | r2_hidden('#skF_2'(A_377,B_378,C_379),C_379)
      | k3_xboole_0(A_377,B_378) = C_379 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8064,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_8052])).

tff(c_8084,plain,(
    ! [A_308] : k4_xboole_0(k1_xboole_0,A_308) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8073,c_8064])).

tff(c_8110,plain,(
    ! [B_29] : ~ r2_hidden(B_29,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8084,c_50])).

tff(c_8932,plain,(
    ! [B_378,C_379] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_378,C_379),C_379)
      | k3_xboole_0(k1_xboole_0,B_378) = C_379 ) ),
    inference(resolution,[status(thm)],[c_8878,c_8110])).

tff(c_9028,plain,(
    ! [B_380,C_381] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_380,C_381),C_381)
      | k1_xboole_0 = C_381 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_8932])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9330,plain,(
    ! [B_393,A_394,B_395] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_393,k3_xboole_0(A_394,B_395)),B_395)
      | k3_xboole_0(A_394,B_395) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9028,c_6])).

tff(c_8483,plain,(
    ! [A_364,B_365,C_366] :
      ( r2_hidden('#skF_1'(A_364,B_365,C_366),B_365)
      | r2_hidden('#skF_2'(A_364,B_365,C_366),C_366)
      | k3_xboole_0(A_364,B_365) = C_366 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8533,plain,(
    ! [A_364,C_366] :
      ( r2_hidden('#skF_2'(A_364,k1_xboole_0,C_366),C_366)
      | k3_xboole_0(A_364,k1_xboole_0) = C_366 ) ),
    inference(resolution,[status(thm)],[c_8483,c_8110])).

tff(c_8634,plain,(
    ! [A_368,C_369] :
      ( r2_hidden('#skF_2'(A_368,k1_xboole_0,C_369),C_369)
      | k1_xboole_0 = C_369 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_8533])).

tff(c_8047,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8117,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8047,c_58])).

tff(c_8067,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8052])).

tff(c_8168,plain,(
    ! [A_315,C_316,B_317] :
      ( ~ r2_hidden(A_315,C_316)
      | ~ r2_hidden(A_315,B_317)
      | ~ r2_hidden(A_315,k5_xboole_0(B_317,C_316)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8384,plain,(
    ! [A_349,B_350,A_351] :
      ( ~ r2_hidden(A_349,k3_xboole_0(B_350,A_351))
      | ~ r2_hidden(A_349,A_351)
      | ~ r2_hidden(A_349,k4_xboole_0(A_351,B_350)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8067,c_8168])).

tff(c_8393,plain,(
    ! [A_349] :
      ( ~ r2_hidden(A_349,k3_xboole_0('#skF_6',k1_tarski('#skF_5')))
      | ~ r2_hidden(A_349,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_349,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8117,c_8384])).

tff(c_8698,plain,(
    ! [A_368] :
      ( ~ r2_hidden('#skF_2'(A_368,k1_xboole_0,k3_xboole_0('#skF_6',k1_tarski('#skF_5'))),k1_tarski('#skF_5'))
      | k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8634,c_8393])).

tff(c_9179,plain,(
    ! [A_368] : ~ r2_hidden('#skF_2'(A_368,k1_xboole_0,k3_xboole_0('#skF_6',k1_tarski('#skF_5'))),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8698])).

tff(c_9411,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9330,c_9179])).

tff(c_9455,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9411,c_34])).

tff(c_9473,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8073,c_9455])).

tff(c_9496,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9473,c_50])).

tff(c_9518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8046,c_9496])).

tff(c_9519,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8698])).

tff(c_9538,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9519,c_34])).

tff(c_9554,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8073,c_9538])).

tff(c_9577,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9554,c_50])).

tff(c_9599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8046,c_9577])).

tff(c_9600,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_9644,plain,(
    ! [A_400,B_401] :
      ( k3_xboole_0(A_400,B_401) = A_400
      | ~ r1_tarski(A_400,B_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9649,plain,(
    ! [A_402] : k3_xboole_0(k1_xboole_0,A_402) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_9644])).

tff(c_9654,plain,(
    ! [A_402] : k3_xboole_0(A_402,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9649,c_2])).

tff(c_9712,plain,(
    ! [A_404,B_405] : k5_xboole_0(A_404,k3_xboole_0(A_404,B_405)) = k4_xboole_0(A_404,B_405) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9721,plain,(
    ! [A_402] : k5_xboole_0(A_402,k1_xboole_0) = k4_xboole_0(A_402,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9654,c_9712])).

tff(c_9733,plain,(
    ! [A_402] : k5_xboole_0(A_402,k1_xboole_0) = A_402 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9721])).

tff(c_10154,plain,(
    ! [A_472,B_473,C_474] :
      ( r2_hidden('#skF_1'(A_472,B_473,C_474),B_473)
      | r2_hidden('#skF_2'(A_472,B_473,C_474),C_474)
      | k3_xboole_0(A_472,B_473) = C_474 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9648,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_9644])).

tff(c_9724,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_9648,c_9712])).

tff(c_9752,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9733,c_9724])).

tff(c_9780,plain,(
    ! [B_410,A_411] :
      ( ~ r2_hidden(B_410,A_411)
      | k4_xboole_0(A_411,k1_tarski(B_410)) != A_411 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9788,plain,(
    ! [B_410] : ~ r2_hidden(B_410,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9752,c_9780])).

tff(c_10208,plain,(
    ! [A_472,C_474] :
      ( r2_hidden('#skF_2'(A_472,k1_xboole_0,C_474),C_474)
      | k3_xboole_0(A_472,k1_xboole_0) = C_474 ) ),
    inference(resolution,[status(thm)],[c_10154,c_9788])).

tff(c_10284,plain,(
    ! [A_475,C_476] :
      ( r2_hidden('#skF_2'(A_475,k1_xboole_0,C_476),C_476)
      | k1_xboole_0 = C_476 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9654,c_10208])).

tff(c_10418,plain,(
    ! [A_481,A_482,B_483] :
      ( r2_hidden('#skF_2'(A_481,k1_xboole_0,k3_xboole_0(A_482,B_483)),B_483)
      | k3_xboole_0(A_482,B_483) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10284,c_6])).

tff(c_9601,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9704,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9601,c_60])).

tff(c_9876,plain,(
    ! [A_427,C_428,B_429] :
      ( ~ r2_hidden(A_427,C_428)
      | ~ r2_hidden(A_427,B_429)
      | ~ r2_hidden(A_427,k5_xboole_0(B_429,C_428)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9956,plain,(
    ! [A_443,A_444,B_445] :
      ( ~ r2_hidden(A_443,k3_xboole_0(A_444,B_445))
      | ~ r2_hidden(A_443,A_444)
      | ~ r2_hidden(A_443,k4_xboole_0(A_444,B_445)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9876])).

tff(c_9965,plain,(
    ! [A_443] :
      ( ~ r2_hidden(A_443,k3_xboole_0(k1_tarski('#skF_5'),'#skF_6'))
      | ~ r2_hidden(A_443,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_443,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9704,c_9956])).

tff(c_9970,plain,(
    ! [A_443] :
      ( ~ r2_hidden(A_443,k3_xboole_0('#skF_6',k1_tarski('#skF_5')))
      | ~ r2_hidden(A_443,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_443,k1_tarski('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_9965])).

tff(c_10339,plain,(
    ! [A_475] :
      ( ~ r2_hidden('#skF_2'(A_475,k1_xboole_0,k3_xboole_0('#skF_6',k1_tarski('#skF_5'))),k1_tarski('#skF_5'))
      | k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10284,c_9970])).

tff(c_10415,plain,(
    ! [A_475] : ~ r2_hidden('#skF_2'(A_475,k1_xboole_0,k3_xboole_0('#skF_6',k1_tarski('#skF_5'))),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10339])).

tff(c_10485,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10418,c_10415])).

tff(c_10527,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10485,c_34])).

tff(c_10537,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9733,c_10527])).

tff(c_10560,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10537,c_50])).

tff(c_10582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9600,c_10560])).

tff(c_10583,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10339])).

tff(c_10734,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10583,c_34])).

tff(c_10743,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9733,c_10734])).

tff(c_10766,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10743,c_50])).

tff(c_10788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9600,c_10766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.85/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/2.80  
% 7.85/2.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/2.81  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 7.85/2.81  
% 7.85/2.81  %Foreground sorts:
% 7.85/2.81  
% 7.85/2.81  
% 7.85/2.81  %Background operators:
% 7.85/2.81  
% 7.85/2.81  
% 7.85/2.81  %Foreground operators:
% 7.85/2.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.85/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.85/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.85/2.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.85/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.85/2.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.85/2.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.85/2.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.85/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.85/2.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.85/2.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.85/2.81  tff('#skF_5', type, '#skF_5': $i).
% 7.85/2.81  tff('#skF_6', type, '#skF_6': $i).
% 7.85/2.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.85/2.81  tff('#skF_3', type, '#skF_3': $i).
% 7.85/2.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.85/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.85/2.81  tff('#skF_4', type, '#skF_4': $i).
% 7.85/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.85/2.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.85/2.81  
% 8.17/2.83  tff(f_72, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 8.17/2.83  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.17/2.83  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.17/2.83  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.17/2.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.17/2.83  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.17/2.83  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 8.17/2.83  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.17/2.83  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.17/2.83  tff(c_56, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.17/2.83  tff(c_80, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 8.17/2.83  tff(c_40, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.17/2.83  tff(c_38, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.17/2.83  tff(c_114, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.17/2.83  tff(c_119, plain, (![A_37]: (k3_xboole_0(k1_xboole_0, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_114])).
% 8.17/2.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.17/2.83  tff(c_124, plain, (![A_37]: (k3_xboole_0(A_37, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_119, c_2])).
% 8.17/2.83  tff(c_227, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.17/2.83  tff(c_236, plain, (![A_37]: (k5_xboole_0(A_37, k1_xboole_0)=k4_xboole_0(A_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_227])).
% 8.17/2.83  tff(c_248, plain, (![A_37]: (k5_xboole_0(A_37, k1_xboole_0)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_236])).
% 8.17/2.83  tff(c_118, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_114])).
% 8.17/2.83  tff(c_239, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_118, c_227])).
% 8.17/2.83  tff(c_259, plain, (![A_56]: (k4_xboole_0(k1_xboole_0, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_248, c_239])).
% 8.17/2.83  tff(c_50, plain, (![B_29, A_28]: (~r2_hidden(B_29, A_28) | k4_xboole_0(A_28, k1_tarski(B_29))!=A_28)), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.17/2.83  tff(c_285, plain, (![B_29]: (~r2_hidden(B_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_259, c_50])).
% 8.17/2.83  tff(c_18, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.17/2.83  tff(c_581, plain, (![A_106, B_107, C_108]: (r2_hidden('#skF_1'(A_106, B_107, C_108), A_106) | r2_hidden('#skF_2'(A_106, B_107, C_108), C_108) | k3_xboole_0(A_106, B_107)=C_108)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.17/2.83  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.17/2.83  tff(c_5177, plain, (![A_254, B_255, A_256, B_257]: (r2_hidden('#skF_2'(A_254, B_255, k3_xboole_0(A_256, B_257)), A_256) | r2_hidden('#skF_1'(A_254, B_255, k3_xboole_0(A_256, B_257)), A_254) | k3_xboole_0(A_256, B_257)=k3_xboole_0(A_254, B_255))), inference(resolution, [status(thm)], [c_581, c_8])).
% 8.17/2.83  tff(c_5308, plain, (![A_254, B_255, A_16]: (r2_hidden('#skF_2'(A_254, B_255, k3_xboole_0(k1_xboole_0, A_16)), k1_xboole_0) | r2_hidden('#skF_1'(A_254, B_255, k1_xboole_0), A_254) | k3_xboole_0(k1_xboole_0, A_16)=k3_xboole_0(A_254, B_255))), inference(superposition, [status(thm), theory('equality')], [c_118, c_5177])).
% 8.17/2.83  tff(c_5356, plain, (![A_254, B_255]: (r2_hidden('#skF_2'(A_254, B_255, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_254, B_255, k1_xboole_0), A_254) | k3_xboole_0(A_254, B_255)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_118, c_5308])).
% 8.17/2.83  tff(c_5358, plain, (![A_258, B_259]: (r2_hidden('#skF_1'(A_258, B_259, k1_xboole_0), A_258) | k3_xboole_0(A_258, B_259)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_285, c_5356])).
% 8.17/2.83  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k3_xboole_0(A_3, B_4)) | ~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.17/2.83  tff(c_52, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k1_tarski(B_29))=A_28 | r2_hidden(B_29, A_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.17/2.83  tff(c_34, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.17/2.83  tff(c_409, plain, (![A_79, C_80, B_81]: (~r2_hidden(A_79, C_80) | ~r2_hidden(A_79, B_81) | ~r2_hidden(A_79, k5_xboole_0(B_81, C_80)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.17/2.83  tff(c_480, plain, (![A_91, A_92, B_93]: (~r2_hidden(A_91, k3_xboole_0(A_92, B_93)) | ~r2_hidden(A_91, A_92) | ~r2_hidden(A_91, k4_xboole_0(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_409])).
% 8.17/2.83  tff(c_1804, plain, (![A_156, A_157, B_158]: (~r2_hidden(A_156, k3_xboole_0(A_157, k1_tarski(B_158))) | ~r2_hidden(A_156, A_157) | ~r2_hidden(A_156, A_157) | r2_hidden(B_158, A_157))), inference(superposition, [status(thm), theory('equality')], [c_52, c_480])).
% 8.17/2.83  tff(c_1901, plain, (![B_158, A_3, D_8]: (r2_hidden(B_158, A_3) | ~r2_hidden(D_8, k1_tarski(B_158)) | ~r2_hidden(D_8, A_3))), inference(resolution, [status(thm)], [c_4, c_1804])).
% 8.17/2.83  tff(c_5839, plain, (![B_272, A_273, B_274]: (r2_hidden(B_272, A_273) | ~r2_hidden('#skF_1'(k1_tarski(B_272), B_274, k1_xboole_0), A_273) | k3_xboole_0(k1_tarski(B_272), B_274)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5358, c_1901])).
% 8.17/2.83  tff(c_5863, plain, (![B_272, B_4]: (r2_hidden(B_272, B_4) | r2_hidden('#skF_2'(k1_tarski(B_272), B_4, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k1_tarski(B_272), B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_5839])).
% 8.17/2.83  tff(c_5909, plain, (![B_275, B_276]: (r2_hidden(B_275, B_276) | k3_xboole_0(k1_tarski(B_275), B_276)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_285, c_5863])).
% 8.17/2.83  tff(c_6054, plain, (![B_275, B_276]: (k5_xboole_0(k1_tarski(B_275), k1_xboole_0)=k4_xboole_0(k1_tarski(B_275), B_276) | r2_hidden(B_275, B_276))), inference(superposition, [status(thm), theory('equality')], [c_5909, c_34])).
% 8.17/2.83  tff(c_7976, plain, (![B_303, B_304]: (k4_xboole_0(k1_tarski(B_303), B_304)=k1_tarski(B_303) | r2_hidden(B_303, B_304))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_6054])).
% 8.17/2.83  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.17/2.83  tff(c_226, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 8.17/2.83  tff(c_8008, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7976, c_226])).
% 8.17/2.83  tff(c_8045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_8008])).
% 8.17/2.83  tff(c_8046, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_54])).
% 8.17/2.83  tff(c_8052, plain, (![A_305, B_306]: (k5_xboole_0(A_305, k3_xboole_0(A_305, B_306))=k4_xboole_0(A_305, B_306))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.17/2.83  tff(c_8061, plain, (![A_37]: (k5_xboole_0(A_37, k1_xboole_0)=k4_xboole_0(A_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_8052])).
% 8.17/2.83  tff(c_8073, plain, (![A_37]: (k5_xboole_0(A_37, k1_xboole_0)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8061])).
% 8.17/2.83  tff(c_8878, plain, (![A_377, B_378, C_379]: (r2_hidden('#skF_1'(A_377, B_378, C_379), A_377) | r2_hidden('#skF_2'(A_377, B_378, C_379), C_379) | k3_xboole_0(A_377, B_378)=C_379)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.17/2.83  tff(c_8064, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_118, c_8052])).
% 8.17/2.83  tff(c_8084, plain, (![A_308]: (k4_xboole_0(k1_xboole_0, A_308)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8073, c_8064])).
% 8.17/2.83  tff(c_8110, plain, (![B_29]: (~r2_hidden(B_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8084, c_50])).
% 8.17/2.83  tff(c_8932, plain, (![B_378, C_379]: (r2_hidden('#skF_2'(k1_xboole_0, B_378, C_379), C_379) | k3_xboole_0(k1_xboole_0, B_378)=C_379)), inference(resolution, [status(thm)], [c_8878, c_8110])).
% 8.17/2.83  tff(c_9028, plain, (![B_380, C_381]: (r2_hidden('#skF_2'(k1_xboole_0, B_380, C_381), C_381) | k1_xboole_0=C_381)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_8932])).
% 8.17/2.83  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.17/2.83  tff(c_9330, plain, (![B_393, A_394, B_395]: (r2_hidden('#skF_2'(k1_xboole_0, B_393, k3_xboole_0(A_394, B_395)), B_395) | k3_xboole_0(A_394, B_395)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9028, c_6])).
% 8.17/2.83  tff(c_8483, plain, (![A_364, B_365, C_366]: (r2_hidden('#skF_1'(A_364, B_365, C_366), B_365) | r2_hidden('#skF_2'(A_364, B_365, C_366), C_366) | k3_xboole_0(A_364, B_365)=C_366)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.17/2.83  tff(c_8533, plain, (![A_364, C_366]: (r2_hidden('#skF_2'(A_364, k1_xboole_0, C_366), C_366) | k3_xboole_0(A_364, k1_xboole_0)=C_366)), inference(resolution, [status(thm)], [c_8483, c_8110])).
% 8.17/2.83  tff(c_8634, plain, (![A_368, C_369]: (r2_hidden('#skF_2'(A_368, k1_xboole_0, C_369), C_369) | k1_xboole_0=C_369)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_8533])).
% 8.17/2.83  tff(c_8047, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 8.17/2.83  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.17/2.83  tff(c_8117, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8047, c_58])).
% 8.17/2.83  tff(c_8067, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8052])).
% 8.17/2.83  tff(c_8168, plain, (![A_315, C_316, B_317]: (~r2_hidden(A_315, C_316) | ~r2_hidden(A_315, B_317) | ~r2_hidden(A_315, k5_xboole_0(B_317, C_316)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.17/2.83  tff(c_8384, plain, (![A_349, B_350, A_351]: (~r2_hidden(A_349, k3_xboole_0(B_350, A_351)) | ~r2_hidden(A_349, A_351) | ~r2_hidden(A_349, k4_xboole_0(A_351, B_350)))), inference(superposition, [status(thm), theory('equality')], [c_8067, c_8168])).
% 8.17/2.83  tff(c_8393, plain, (![A_349]: (~r2_hidden(A_349, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))) | ~r2_hidden(A_349, k1_tarski('#skF_5')) | ~r2_hidden(A_349, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_8117, c_8384])).
% 8.17/2.83  tff(c_8698, plain, (![A_368]: (~r2_hidden('#skF_2'(A_368, k1_xboole_0, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), k1_tarski('#skF_5')) | k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8634, c_8393])).
% 8.17/2.83  tff(c_9179, plain, (![A_368]: (~r2_hidden('#skF_2'(A_368, k1_xboole_0, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), k1_tarski('#skF_5')))), inference(splitLeft, [status(thm)], [c_8698])).
% 8.17/2.83  tff(c_9411, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_9330, c_9179])).
% 8.17/2.83  tff(c_9455, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9411, c_34])).
% 8.17/2.83  tff(c_9473, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8073, c_9455])).
% 8.17/2.83  tff(c_9496, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9473, c_50])).
% 8.17/2.83  tff(c_9518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8046, c_9496])).
% 8.17/2.83  tff(c_9519, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_8698])).
% 8.17/2.83  tff(c_9538, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9519, c_34])).
% 8.17/2.83  tff(c_9554, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8073, c_9538])).
% 8.17/2.83  tff(c_9577, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9554, c_50])).
% 8.17/2.83  tff(c_9599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8046, c_9577])).
% 8.17/2.83  tff(c_9600, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 8.17/2.83  tff(c_9644, plain, (![A_400, B_401]: (k3_xboole_0(A_400, B_401)=A_400 | ~r1_tarski(A_400, B_401))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.17/2.83  tff(c_9649, plain, (![A_402]: (k3_xboole_0(k1_xboole_0, A_402)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_9644])).
% 8.17/2.83  tff(c_9654, plain, (![A_402]: (k3_xboole_0(A_402, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9649, c_2])).
% 8.17/2.83  tff(c_9712, plain, (![A_404, B_405]: (k5_xboole_0(A_404, k3_xboole_0(A_404, B_405))=k4_xboole_0(A_404, B_405))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.17/2.83  tff(c_9721, plain, (![A_402]: (k5_xboole_0(A_402, k1_xboole_0)=k4_xboole_0(A_402, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9654, c_9712])).
% 8.17/2.83  tff(c_9733, plain, (![A_402]: (k5_xboole_0(A_402, k1_xboole_0)=A_402)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_9721])).
% 8.17/2.83  tff(c_10154, plain, (![A_472, B_473, C_474]: (r2_hidden('#skF_1'(A_472, B_473, C_474), B_473) | r2_hidden('#skF_2'(A_472, B_473, C_474), C_474) | k3_xboole_0(A_472, B_473)=C_474)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.17/2.83  tff(c_9648, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_9644])).
% 8.17/2.83  tff(c_9724, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_9648, c_9712])).
% 8.17/2.83  tff(c_9752, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9733, c_9724])).
% 8.17/2.83  tff(c_9780, plain, (![B_410, A_411]: (~r2_hidden(B_410, A_411) | k4_xboole_0(A_411, k1_tarski(B_410))!=A_411)), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.17/2.83  tff(c_9788, plain, (![B_410]: (~r2_hidden(B_410, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9752, c_9780])).
% 8.17/2.83  tff(c_10208, plain, (![A_472, C_474]: (r2_hidden('#skF_2'(A_472, k1_xboole_0, C_474), C_474) | k3_xboole_0(A_472, k1_xboole_0)=C_474)), inference(resolution, [status(thm)], [c_10154, c_9788])).
% 8.17/2.83  tff(c_10284, plain, (![A_475, C_476]: (r2_hidden('#skF_2'(A_475, k1_xboole_0, C_476), C_476) | k1_xboole_0=C_476)), inference(demodulation, [status(thm), theory('equality')], [c_9654, c_10208])).
% 8.17/2.83  tff(c_10418, plain, (![A_481, A_482, B_483]: (r2_hidden('#skF_2'(A_481, k1_xboole_0, k3_xboole_0(A_482, B_483)), B_483) | k3_xboole_0(A_482, B_483)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10284, c_6])).
% 8.17/2.83  tff(c_9601, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 8.17/2.83  tff(c_60, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.17/2.83  tff(c_9704, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9601, c_60])).
% 8.17/2.83  tff(c_9876, plain, (![A_427, C_428, B_429]: (~r2_hidden(A_427, C_428) | ~r2_hidden(A_427, B_429) | ~r2_hidden(A_427, k5_xboole_0(B_429, C_428)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.17/2.83  tff(c_9956, plain, (![A_443, A_444, B_445]: (~r2_hidden(A_443, k3_xboole_0(A_444, B_445)) | ~r2_hidden(A_443, A_444) | ~r2_hidden(A_443, k4_xboole_0(A_444, B_445)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_9876])).
% 8.17/2.83  tff(c_9965, plain, (![A_443]: (~r2_hidden(A_443, k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden(A_443, k1_tarski('#skF_5')) | ~r2_hidden(A_443, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9704, c_9956])).
% 8.17/2.83  tff(c_9970, plain, (![A_443]: (~r2_hidden(A_443, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))) | ~r2_hidden(A_443, k1_tarski('#skF_5')) | ~r2_hidden(A_443, k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_9965])).
% 8.17/2.83  tff(c_10339, plain, (![A_475]: (~r2_hidden('#skF_2'(A_475, k1_xboole_0, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), k1_tarski('#skF_5')) | k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10284, c_9970])).
% 8.17/2.83  tff(c_10415, plain, (![A_475]: (~r2_hidden('#skF_2'(A_475, k1_xboole_0, k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), k1_tarski('#skF_5')))), inference(splitLeft, [status(thm)], [c_10339])).
% 8.17/2.83  tff(c_10485, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10418, c_10415])).
% 8.17/2.83  tff(c_10527, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10485, c_34])).
% 8.17/2.83  tff(c_10537, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9733, c_10527])).
% 8.17/2.83  tff(c_10560, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10537, c_50])).
% 8.17/2.83  tff(c_10582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9600, c_10560])).
% 8.17/2.83  tff(c_10583, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_10339])).
% 8.17/2.83  tff(c_10734, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10583, c_34])).
% 8.17/2.83  tff(c_10743, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9733, c_10734])).
% 8.17/2.83  tff(c_10766, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10743, c_50])).
% 8.17/2.83  tff(c_10788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9600, c_10766])).
% 8.17/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.17/2.83  
% 8.17/2.83  Inference rules
% 8.17/2.83  ----------------------
% 8.17/2.83  #Ref     : 0
% 8.17/2.83  #Sup     : 2431
% 8.17/2.83  #Fact    : 0
% 8.17/2.83  #Define  : 0
% 8.17/2.83  #Split   : 10
% 8.17/2.83  #Chain   : 0
% 8.17/2.83  #Close   : 0
% 8.17/2.83  
% 8.17/2.83  Ordering : KBO
% 8.17/2.83  
% 8.17/2.83  Simplification rules
% 8.17/2.83  ----------------------
% 8.17/2.83  #Subsume      : 459
% 8.17/2.83  #Demod        : 840
% 8.17/2.83  #Tautology    : 529
% 8.17/2.83  #SimpNegUnit  : 172
% 8.17/2.83  #BackRed      : 9
% 8.17/2.83  
% 8.17/2.83  #Partial instantiations: 0
% 8.17/2.83  #Strategies tried      : 1
% 8.17/2.83  
% 8.17/2.83  Timing (in seconds)
% 8.17/2.83  ----------------------
% 8.17/2.83  Preprocessing        : 0.32
% 8.17/2.83  Parsing              : 0.17
% 8.17/2.83  CNF conversion       : 0.02
% 8.17/2.83  Main loop            : 1.66
% 8.17/2.83  Inferencing          : 0.49
% 8.17/2.83  Reduction            : 0.58
% 8.17/2.83  Demodulation         : 0.45
% 8.17/2.83  BG Simplification    : 0.07
% 8.17/2.83  Subsumption          : 0.41
% 8.17/2.83  Abstraction          : 0.08
% 8.17/2.83  MUC search           : 0.00
% 8.17/2.83  Cooper               : 0.00
% 8.17/2.83  Total                : 2.03
% 8.17/2.83  Index Insertion      : 0.00
% 8.17/2.83  Index Deletion       : 0.00
% 8.17/2.83  Index Matching       : 0.00
% 8.17/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
