%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:59 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 250 expanded)
%              Number of leaves         :   32 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 374 expanded)
%              Number of equality atoms :   63 ( 147 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_34,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),B_47)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_151,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = A_68
      | ~ r1_xboole_0(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1287,plain,(
    ! [A_156,B_157] :
      ( k4_xboole_0(k1_tarski(A_156),B_157) = k1_tarski(A_156)
      | r2_hidden(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_42,plain,
    ( k4_xboole_0(k1_tarski('#skF_2'),'#skF_3') != k1_tarski('#skF_2')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_198,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),'#skF_3') != k1_tarski('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_1305,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1287,c_198])).

tff(c_1323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1305])).

tff(c_1324,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1325,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),'#skF_3') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_2'),'#skF_3') != k1_tarski('#skF_2')
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1334,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_46])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1586,plain,(
    ! [A_185,B_186] :
      ( r2_hidden('#skF_1'(A_185,B_186),k3_xboole_0(A_185,B_186))
      | r1_xboole_0(A_185,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_160,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_1,B_2,C_72] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_72,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_160])).

tff(c_1613,plain,(
    ! [B_187,A_188] :
      ( ~ r1_xboole_0(B_187,A_188)
      | r1_xboole_0(A_188,B_187) ) ),
    inference(resolution,[status(thm)],[c_1586,c_163])).

tff(c_1620,plain,(
    ! [B_189,A_190] :
      ( r1_xboole_0(B_189,A_190)
      | k4_xboole_0(A_190,B_189) != A_190 ) ),
    inference(resolution,[status(thm)],[c_18,c_1613])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2524,plain,(
    ! [B_239,A_240] :
      ( k4_xboole_0(B_239,A_240) = B_239
      | k4_xboole_0(A_240,B_239) != A_240 ) ),
    inference(resolution,[status(thm)],[c_1620,c_16])).

tff(c_2536,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_2524])).

tff(c_20,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1645,plain,(
    ! [A_193,B_194,C_195] :
      ( r1_tarski(k2_tarski(A_193,B_194),C_195)
      | ~ r2_hidden(B_194,C_195)
      | ~ r2_hidden(A_193,C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2764,plain,(
    ! [A_245,C_246] :
      ( r1_tarski(k1_tarski(A_245),C_246)
      | ~ r2_hidden(A_245,C_246)
      | ~ r2_hidden(A_245,C_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1645])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2773,plain,(
    ! [A_247,C_248] :
      ( k3_xboole_0(k1_tarski(A_247),C_248) = k1_tarski(A_247)
      | ~ r2_hidden(A_247,C_248) ) ),
    inference(resolution,[status(thm)],[c_2764,c_14])).

tff(c_2921,plain,(
    ! [C_251,A_252] :
      ( k3_xboole_0(C_251,k1_tarski(A_252)) = k1_tarski(A_252)
      | ~ r2_hidden(A_252,C_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2773,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_137,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1434,plain,(
    ! [A_178,B_179] : k3_xboole_0(k3_xboole_0(A_178,B_179),A_178) = k3_xboole_0(A_178,B_179) ),
    inference(resolution,[status(thm)],[c_12,c_137])).

tff(c_1675,plain,(
    ! [B_197,A_198] : k3_xboole_0(k3_xboole_0(B_197,A_198),A_198) = k3_xboole_0(A_198,B_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1434])).

tff(c_1721,plain,(
    ! [A_198,B_197] : r1_tarski(k3_xboole_0(A_198,B_197),k3_xboole_0(B_197,A_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1675,c_12])).

tff(c_5965,plain,(
    ! [A_336,C_337] :
      ( r1_tarski(k1_tarski(A_336),k3_xboole_0(k1_tarski(A_336),C_337))
      | ~ r2_hidden(A_336,C_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2921,c_1721])).

tff(c_1348,plain,(
    ! [A_159,C_160,B_161] :
      ( r2_hidden(A_159,C_160)
      | ~ r1_tarski(k2_tarski(A_159,B_161),C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1355,plain,(
    ! [A_18,C_160] :
      ( r2_hidden(A_18,C_160)
      | ~ r1_tarski(k1_tarski(A_18),C_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1348])).

tff(c_6102,plain,(
    ! [A_341,C_342] :
      ( r2_hidden(A_341,k3_xboole_0(k1_tarski(A_341),C_342))
      | ~ r2_hidden(A_341,C_342) ) ),
    inference(resolution,[status(thm)],[c_5965,c_1355])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_180,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_192,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_180])).

tff(c_1443,plain,(
    ! [A_178,B_179] : k5_xboole_0(A_178,k3_xboole_0(A_178,B_179)) = k4_xboole_0(A_178,k3_xboole_0(A_178,B_179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1434,c_192])).

tff(c_1487,plain,(
    ! [A_178,B_179] : k4_xboole_0(A_178,k3_xboole_0(A_178,B_179)) = k4_xboole_0(A_178,B_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1443])).

tff(c_73,plain,(
    ! [B_56,A_57] : k3_xboole_0(B_56,A_57) = k3_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [B_56,A_57] : r1_tarski(k3_xboole_0(B_56,A_57),A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_12])).

tff(c_1506,plain,(
    ! [B_183,A_184] : k3_xboole_0(k3_xboole_0(B_183,A_184),A_184) = k3_xboole_0(B_183,A_184) ),
    inference(resolution,[status(thm)],[c_88,c_137])).

tff(c_2316,plain,(
    ! [B_235,A_236] : k3_xboole_0(k3_xboole_0(B_235,A_236),B_235) = k3_xboole_0(A_236,B_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1506])).

tff(c_2439,plain,(
    ! [A_1,A_236] : k3_xboole_0(A_1,k3_xboole_0(A_1,A_236)) = k3_xboole_0(A_236,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2316])).

tff(c_1618,plain,(
    ! [B_17,A_16] :
      ( r1_xboole_0(B_17,A_16)
      | k4_xboole_0(A_16,B_17) != A_16 ) ),
    inference(resolution,[status(thm)],[c_18,c_1613])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3068,plain,(
    ! [A_253,B_254,C_255] :
      ( ~ r1_xboole_0(k3_xboole_0(A_253,B_254),A_253)
      | ~ r2_hidden(C_255,k3_xboole_0(A_253,B_254)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1434,c_8])).

tff(c_3090,plain,(
    ! [C_255,A_16,B_254] :
      ( ~ r2_hidden(C_255,k3_xboole_0(A_16,B_254))
      | k4_xboole_0(A_16,k3_xboole_0(A_16,B_254)) != A_16 ) ),
    inference(resolution,[status(thm)],[c_1618,c_3068])).

tff(c_3270,plain,(
    ! [C_259,A_260,B_261] :
      ( ~ r2_hidden(C_259,k3_xboole_0(A_260,B_261))
      | k4_xboole_0(A_260,B_261) != A_260 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_3090])).

tff(c_3282,plain,(
    ! [C_259,A_236,A_1] :
      ( ~ r2_hidden(C_259,k3_xboole_0(A_236,A_1))
      | k4_xboole_0(A_1,k3_xboole_0(A_1,A_236)) != A_1 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2439,c_3270])).

tff(c_3323,plain,(
    ! [C_259,A_236,A_1] :
      ( ~ r2_hidden(C_259,k3_xboole_0(A_236,A_1))
      | k4_xboole_0(A_1,A_236) != A_1 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_3282])).

tff(c_6284,plain,(
    ! [C_347,A_348] :
      ( k4_xboole_0(C_347,k1_tarski(A_348)) != C_347
      | ~ r2_hidden(A_348,C_347) ) ),
    inference(resolution,[status(thm)],[c_6102,c_3323])).

tff(c_6293,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2536,c_6284])).

tff(c_6303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1324,c_6293])).

tff(c_6304,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6305,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6360,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6305,c_48])).

tff(c_6669,plain,(
    ! [A_399,B_400] :
      ( r2_hidden('#skF_1'(A_399,B_400),k3_xboole_0(A_399,B_400))
      | r1_xboole_0(A_399,B_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6399,plain,(
    ! [A_363,B_364,C_365] :
      ( ~ r1_xboole_0(A_363,B_364)
      | ~ r2_hidden(C_365,k3_xboole_0(A_363,B_364)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6402,plain,(
    ! [A_1,B_2,C_365] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_365,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6399])).

tff(c_6696,plain,(
    ! [B_401,A_402] :
      ( ~ r1_xboole_0(B_401,A_402)
      | r1_xboole_0(A_402,B_401) ) ),
    inference(resolution,[status(thm)],[c_6669,c_6402])).

tff(c_6716,plain,(
    ! [B_405,A_406] :
      ( r1_xboole_0(B_405,A_406)
      | k4_xboole_0(A_406,B_405) != A_406 ) ),
    inference(resolution,[status(thm)],[c_18,c_6696])).

tff(c_7805,plain,(
    ! [B_457,A_458] :
      ( k4_xboole_0(B_457,A_458) = B_457
      | k4_xboole_0(A_458,B_457) != A_458 ) ),
    inference(resolution,[status(thm)],[c_6716,c_16])).

tff(c_7818,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6360,c_7805])).

tff(c_6743,plain,(
    ! [A_408,B_409,C_410] :
      ( r1_tarski(k2_tarski(A_408,B_409),C_410)
      | ~ r2_hidden(B_409,C_410)
      | ~ r2_hidden(A_408,C_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7840,plain,(
    ! [A_459,C_460] :
      ( r1_tarski(k1_tarski(A_459),C_460)
      | ~ r2_hidden(A_459,C_460)
      | ~ r2_hidden(A_459,C_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6743])).

tff(c_7849,plain,(
    ! [A_461,C_462] :
      ( k3_xboole_0(k1_tarski(A_461),C_462) = k1_tarski(A_461)
      | ~ r2_hidden(A_461,C_462) ) ),
    inference(resolution,[status(thm)],[c_7840,c_14])).

tff(c_7997,plain,(
    ! [C_465,A_466] :
      ( k3_xboole_0(C_465,k1_tarski(A_466)) = k1_tarski(A_466)
      | ~ r2_hidden(A_466,C_465) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7849,c_2])).

tff(c_6380,plain,(
    ! [A_359,B_360] :
      ( k3_xboole_0(A_359,B_360) = A_359
      | ~ r1_tarski(A_359,B_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6541,plain,(
    ! [A_392,B_393] : k3_xboole_0(k3_xboole_0(A_392,B_393),A_392) = k3_xboole_0(A_392,B_393) ),
    inference(resolution,[status(thm)],[c_12,c_6380])).

tff(c_6890,plain,(
    ! [A_419,B_420] : k3_xboole_0(k3_xboole_0(A_419,B_420),B_420) = k3_xboole_0(B_420,A_419) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6541])).

tff(c_6942,plain,(
    ! [B_420,A_419] : r1_tarski(k3_xboole_0(B_420,A_419),k3_xboole_0(A_419,B_420)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6890,c_12])).

tff(c_10207,plain,(
    ! [A_516,C_517] :
      ( r1_tarski(k1_tarski(A_516),k3_xboole_0(k1_tarski(A_516),C_517))
      | ~ r2_hidden(A_516,C_517) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7997,c_6942])).

tff(c_6426,plain,(
    ! [A_370,C_371,B_372] :
      ( r2_hidden(A_370,C_371)
      | ~ r1_tarski(k2_tarski(A_370,B_372),C_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6433,plain,(
    ! [A_18,C_371] :
      ( r2_hidden(A_18,C_371)
      | ~ r1_tarski(k1_tarski(A_18),C_371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6426])).

tff(c_10259,plain,(
    ! [A_518,C_519] :
      ( r2_hidden(A_518,k3_xboole_0(k1_tarski(A_518),C_519))
      | ~ r2_hidden(A_518,C_519) ) ),
    inference(resolution,[status(thm)],[c_10207,c_6433])).

tff(c_6471,plain,(
    ! [A_384,B_385] : k5_xboole_0(A_384,k3_xboole_0(A_384,B_385)) = k4_xboole_0(A_384,B_385) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6483,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6471])).

tff(c_6553,plain,(
    ! [A_392,B_393] : k5_xboole_0(A_392,k3_xboole_0(A_392,B_393)) = k4_xboole_0(A_392,k3_xboole_0(A_392,B_393)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6541,c_6483])).

tff(c_6597,plain,(
    ! [A_392,B_393] : k4_xboole_0(A_392,k3_xboole_0(A_392,B_393)) = k4_xboole_0(A_392,B_393) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6553])).

tff(c_6702,plain,(
    ! [B_17,A_16] :
      ( r1_xboole_0(B_17,A_16)
      | k4_xboole_0(A_16,B_17) != A_16 ) ),
    inference(resolution,[status(thm)],[c_18,c_6696])).

tff(c_8408,plain,(
    ! [A_472,B_473,C_474] :
      ( ~ r1_xboole_0(k3_xboole_0(A_472,B_473),A_472)
      | ~ r2_hidden(C_474,k3_xboole_0(A_472,B_473)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6541,c_8])).

tff(c_8429,plain,(
    ! [C_474,A_16,B_473] :
      ( ~ r2_hidden(C_474,k3_xboole_0(A_16,B_473))
      | k4_xboole_0(A_16,k3_xboole_0(A_16,B_473)) != A_16 ) ),
    inference(resolution,[status(thm)],[c_6702,c_8408])).

tff(c_8459,plain,(
    ! [C_475,A_476,B_477] :
      ( ~ r2_hidden(C_475,k3_xboole_0(A_476,B_477))
      | k4_xboole_0(A_476,B_477) != A_476 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6597,c_8429])).

tff(c_8505,plain,(
    ! [C_475,B_2,A_1] :
      ( ~ r2_hidden(C_475,k3_xboole_0(B_2,A_1))
      | k4_xboole_0(A_1,B_2) != A_1 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8459])).

tff(c_10361,plain,(
    ! [C_524,A_525] :
      ( k4_xboole_0(C_524,k1_tarski(A_525)) != C_524
      | ~ r2_hidden(A_525,C_524) ) ),
    inference(resolution,[status(thm)],[c_10259,c_8505])).

tff(c_10364,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7818,c_10361])).

tff(c_10375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6304,c_10364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.98/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.50  
% 6.98/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.98/2.50  
% 6.98/2.50  %Foreground sorts:
% 6.98/2.50  
% 6.98/2.50  
% 6.98/2.50  %Background operators:
% 6.98/2.50  
% 6.98/2.50  
% 6.98/2.50  %Foreground operators:
% 6.98/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.98/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.98/2.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.98/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.98/2.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.98/2.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.98/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.98/2.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.98/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.98/2.50  tff('#skF_5', type, '#skF_5': $i).
% 6.98/2.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.98/2.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.98/2.50  tff('#skF_2', type, '#skF_2': $i).
% 6.98/2.50  tff('#skF_3', type, '#skF_3': $i).
% 6.98/2.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.98/2.50  tff('#skF_4', type, '#skF_4': $i).
% 6.98/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.98/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.98/2.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.98/2.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.98/2.50  
% 6.98/2.52  tff(f_86, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 6.98/2.52  tff(f_74, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.98/2.52  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.98/2.52  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.98/2.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.98/2.52  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.98/2.52  tff(f_80, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.98/2.52  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.98/2.52  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.98/2.52  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.98/2.52  tff(c_44, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.98/2.52  tff(c_72, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 6.98/2.52  tff(c_34, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), B_47) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.98/2.52  tff(c_151, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=A_68 | ~r1_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.98/2.52  tff(c_1287, plain, (![A_156, B_157]: (k4_xboole_0(k1_tarski(A_156), B_157)=k1_tarski(A_156) | r2_hidden(A_156, B_157))), inference(resolution, [status(thm)], [c_34, c_151])).
% 6.98/2.52  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_3')!=k1_tarski('#skF_2') | r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.98/2.52  tff(c_198, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_3')!=k1_tarski('#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 6.98/2.52  tff(c_1305, plain, (r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1287, c_198])).
% 6.98/2.52  tff(c_1323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1305])).
% 6.98/2.52  tff(c_1324, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 6.98/2.52  tff(c_1325, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_3')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 6.98/2.52  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_3')!=k1_tarski('#skF_2') | k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.98/2.52  tff(c_1334, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_46])).
% 6.98/2.52  tff(c_18, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k4_xboole_0(A_16, B_17)!=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.98/2.52  tff(c_1586, plain, (![A_185, B_186]: (r2_hidden('#skF_1'(A_185, B_186), k3_xboole_0(A_185, B_186)) | r1_xboole_0(A_185, B_186))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.98/2.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.98/2.52  tff(c_160, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.98/2.52  tff(c_163, plain, (![A_1, B_2, C_72]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_72, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_160])).
% 6.98/2.52  tff(c_1613, plain, (![B_187, A_188]: (~r1_xboole_0(B_187, A_188) | r1_xboole_0(A_188, B_187))), inference(resolution, [status(thm)], [c_1586, c_163])).
% 6.98/2.52  tff(c_1620, plain, (![B_189, A_190]: (r1_xboole_0(B_189, A_190) | k4_xboole_0(A_190, B_189)!=A_190)), inference(resolution, [status(thm)], [c_18, c_1613])).
% 6.98/2.52  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.98/2.52  tff(c_2524, plain, (![B_239, A_240]: (k4_xboole_0(B_239, A_240)=B_239 | k4_xboole_0(A_240, B_239)!=A_240)), inference(resolution, [status(thm)], [c_1620, c_16])).
% 6.98/2.52  tff(c_2536, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1334, c_2524])).
% 6.98/2.52  tff(c_20, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.98/2.52  tff(c_1645, plain, (![A_193, B_194, C_195]: (r1_tarski(k2_tarski(A_193, B_194), C_195) | ~r2_hidden(B_194, C_195) | ~r2_hidden(A_193, C_195))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.98/2.52  tff(c_2764, plain, (![A_245, C_246]: (r1_tarski(k1_tarski(A_245), C_246) | ~r2_hidden(A_245, C_246) | ~r2_hidden(A_245, C_246))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1645])).
% 6.98/2.52  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.98/2.52  tff(c_2773, plain, (![A_247, C_248]: (k3_xboole_0(k1_tarski(A_247), C_248)=k1_tarski(A_247) | ~r2_hidden(A_247, C_248))), inference(resolution, [status(thm)], [c_2764, c_14])).
% 6.98/2.52  tff(c_2921, plain, (![C_251, A_252]: (k3_xboole_0(C_251, k1_tarski(A_252))=k1_tarski(A_252) | ~r2_hidden(A_252, C_251))), inference(superposition, [status(thm), theory('equality')], [c_2773, c_2])).
% 6.98/2.52  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.98/2.52  tff(c_137, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.98/2.52  tff(c_1434, plain, (![A_178, B_179]: (k3_xboole_0(k3_xboole_0(A_178, B_179), A_178)=k3_xboole_0(A_178, B_179))), inference(resolution, [status(thm)], [c_12, c_137])).
% 6.98/2.52  tff(c_1675, plain, (![B_197, A_198]: (k3_xboole_0(k3_xboole_0(B_197, A_198), A_198)=k3_xboole_0(A_198, B_197))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1434])).
% 6.98/2.52  tff(c_1721, plain, (![A_198, B_197]: (r1_tarski(k3_xboole_0(A_198, B_197), k3_xboole_0(B_197, A_198)))), inference(superposition, [status(thm), theory('equality')], [c_1675, c_12])).
% 6.98/2.52  tff(c_5965, plain, (![A_336, C_337]: (r1_tarski(k1_tarski(A_336), k3_xboole_0(k1_tarski(A_336), C_337)) | ~r2_hidden(A_336, C_337))), inference(superposition, [status(thm), theory('equality')], [c_2921, c_1721])).
% 6.98/2.52  tff(c_1348, plain, (![A_159, C_160, B_161]: (r2_hidden(A_159, C_160) | ~r1_tarski(k2_tarski(A_159, B_161), C_160))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.98/2.52  tff(c_1355, plain, (![A_18, C_160]: (r2_hidden(A_18, C_160) | ~r1_tarski(k1_tarski(A_18), C_160))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1348])).
% 6.98/2.52  tff(c_6102, plain, (![A_341, C_342]: (r2_hidden(A_341, k3_xboole_0(k1_tarski(A_341), C_342)) | ~r2_hidden(A_341, C_342))), inference(resolution, [status(thm)], [c_5965, c_1355])).
% 6.98/2.52  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.98/2.52  tff(c_180, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.98/2.52  tff(c_192, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_180])).
% 6.98/2.52  tff(c_1443, plain, (![A_178, B_179]: (k5_xboole_0(A_178, k3_xboole_0(A_178, B_179))=k4_xboole_0(A_178, k3_xboole_0(A_178, B_179)))), inference(superposition, [status(thm), theory('equality')], [c_1434, c_192])).
% 6.98/2.52  tff(c_1487, plain, (![A_178, B_179]: (k4_xboole_0(A_178, k3_xboole_0(A_178, B_179))=k4_xboole_0(A_178, B_179))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1443])).
% 6.98/2.52  tff(c_73, plain, (![B_56, A_57]: (k3_xboole_0(B_56, A_57)=k3_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.98/2.52  tff(c_88, plain, (![B_56, A_57]: (r1_tarski(k3_xboole_0(B_56, A_57), A_57))), inference(superposition, [status(thm), theory('equality')], [c_73, c_12])).
% 6.98/2.52  tff(c_1506, plain, (![B_183, A_184]: (k3_xboole_0(k3_xboole_0(B_183, A_184), A_184)=k3_xboole_0(B_183, A_184))), inference(resolution, [status(thm)], [c_88, c_137])).
% 6.98/2.52  tff(c_2316, plain, (![B_235, A_236]: (k3_xboole_0(k3_xboole_0(B_235, A_236), B_235)=k3_xboole_0(A_236, B_235))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1506])).
% 6.98/2.52  tff(c_2439, plain, (![A_1, A_236]: (k3_xboole_0(A_1, k3_xboole_0(A_1, A_236))=k3_xboole_0(A_236, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2316])).
% 6.98/2.52  tff(c_1618, plain, (![B_17, A_16]: (r1_xboole_0(B_17, A_16) | k4_xboole_0(A_16, B_17)!=A_16)), inference(resolution, [status(thm)], [c_18, c_1613])).
% 6.98/2.52  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.98/2.52  tff(c_3068, plain, (![A_253, B_254, C_255]: (~r1_xboole_0(k3_xboole_0(A_253, B_254), A_253) | ~r2_hidden(C_255, k3_xboole_0(A_253, B_254)))), inference(superposition, [status(thm), theory('equality')], [c_1434, c_8])).
% 6.98/2.52  tff(c_3090, plain, (![C_255, A_16, B_254]: (~r2_hidden(C_255, k3_xboole_0(A_16, B_254)) | k4_xboole_0(A_16, k3_xboole_0(A_16, B_254))!=A_16)), inference(resolution, [status(thm)], [c_1618, c_3068])).
% 6.98/2.52  tff(c_3270, plain, (![C_259, A_260, B_261]: (~r2_hidden(C_259, k3_xboole_0(A_260, B_261)) | k4_xboole_0(A_260, B_261)!=A_260)), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_3090])).
% 6.98/2.52  tff(c_3282, plain, (![C_259, A_236, A_1]: (~r2_hidden(C_259, k3_xboole_0(A_236, A_1)) | k4_xboole_0(A_1, k3_xboole_0(A_1, A_236))!=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2439, c_3270])).
% 6.98/2.52  tff(c_3323, plain, (![C_259, A_236, A_1]: (~r2_hidden(C_259, k3_xboole_0(A_236, A_1)) | k4_xboole_0(A_1, A_236)!=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_3282])).
% 6.98/2.52  tff(c_6284, plain, (![C_347, A_348]: (k4_xboole_0(C_347, k1_tarski(A_348))!=C_347 | ~r2_hidden(A_348, C_347))), inference(resolution, [status(thm)], [c_6102, c_3323])).
% 6.98/2.52  tff(c_6293, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2536, c_6284])).
% 6.98/2.52  tff(c_6303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1324, c_6293])).
% 6.98/2.52  tff(c_6304, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 6.98/2.52  tff(c_6305, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 6.98/2.52  tff(c_48, plain, (~r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.98/2.52  tff(c_6360, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6305, c_48])).
% 6.98/2.52  tff(c_6669, plain, (![A_399, B_400]: (r2_hidden('#skF_1'(A_399, B_400), k3_xboole_0(A_399, B_400)) | r1_xboole_0(A_399, B_400))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.98/2.52  tff(c_6399, plain, (![A_363, B_364, C_365]: (~r1_xboole_0(A_363, B_364) | ~r2_hidden(C_365, k3_xboole_0(A_363, B_364)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.98/2.52  tff(c_6402, plain, (![A_1, B_2, C_365]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_365, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6399])).
% 6.98/2.52  tff(c_6696, plain, (![B_401, A_402]: (~r1_xboole_0(B_401, A_402) | r1_xboole_0(A_402, B_401))), inference(resolution, [status(thm)], [c_6669, c_6402])).
% 6.98/2.52  tff(c_6716, plain, (![B_405, A_406]: (r1_xboole_0(B_405, A_406) | k4_xboole_0(A_406, B_405)!=A_406)), inference(resolution, [status(thm)], [c_18, c_6696])).
% 6.98/2.52  tff(c_7805, plain, (![B_457, A_458]: (k4_xboole_0(B_457, A_458)=B_457 | k4_xboole_0(A_458, B_457)!=A_458)), inference(resolution, [status(thm)], [c_6716, c_16])).
% 6.98/2.52  tff(c_7818, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6360, c_7805])).
% 6.98/2.52  tff(c_6743, plain, (![A_408, B_409, C_410]: (r1_tarski(k2_tarski(A_408, B_409), C_410) | ~r2_hidden(B_409, C_410) | ~r2_hidden(A_408, C_410))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.98/2.52  tff(c_7840, plain, (![A_459, C_460]: (r1_tarski(k1_tarski(A_459), C_460) | ~r2_hidden(A_459, C_460) | ~r2_hidden(A_459, C_460))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6743])).
% 6.98/2.52  tff(c_7849, plain, (![A_461, C_462]: (k3_xboole_0(k1_tarski(A_461), C_462)=k1_tarski(A_461) | ~r2_hidden(A_461, C_462))), inference(resolution, [status(thm)], [c_7840, c_14])).
% 6.98/2.52  tff(c_7997, plain, (![C_465, A_466]: (k3_xboole_0(C_465, k1_tarski(A_466))=k1_tarski(A_466) | ~r2_hidden(A_466, C_465))), inference(superposition, [status(thm), theory('equality')], [c_7849, c_2])).
% 6.98/2.52  tff(c_6380, plain, (![A_359, B_360]: (k3_xboole_0(A_359, B_360)=A_359 | ~r1_tarski(A_359, B_360))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.98/2.52  tff(c_6541, plain, (![A_392, B_393]: (k3_xboole_0(k3_xboole_0(A_392, B_393), A_392)=k3_xboole_0(A_392, B_393))), inference(resolution, [status(thm)], [c_12, c_6380])).
% 6.98/2.52  tff(c_6890, plain, (![A_419, B_420]: (k3_xboole_0(k3_xboole_0(A_419, B_420), B_420)=k3_xboole_0(B_420, A_419))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6541])).
% 6.98/2.52  tff(c_6942, plain, (![B_420, A_419]: (r1_tarski(k3_xboole_0(B_420, A_419), k3_xboole_0(A_419, B_420)))), inference(superposition, [status(thm), theory('equality')], [c_6890, c_12])).
% 6.98/2.52  tff(c_10207, plain, (![A_516, C_517]: (r1_tarski(k1_tarski(A_516), k3_xboole_0(k1_tarski(A_516), C_517)) | ~r2_hidden(A_516, C_517))), inference(superposition, [status(thm), theory('equality')], [c_7997, c_6942])).
% 6.98/2.52  tff(c_6426, plain, (![A_370, C_371, B_372]: (r2_hidden(A_370, C_371) | ~r1_tarski(k2_tarski(A_370, B_372), C_371))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.98/2.52  tff(c_6433, plain, (![A_18, C_371]: (r2_hidden(A_18, C_371) | ~r1_tarski(k1_tarski(A_18), C_371))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6426])).
% 6.98/2.52  tff(c_10259, plain, (![A_518, C_519]: (r2_hidden(A_518, k3_xboole_0(k1_tarski(A_518), C_519)) | ~r2_hidden(A_518, C_519))), inference(resolution, [status(thm)], [c_10207, c_6433])).
% 6.98/2.52  tff(c_6471, plain, (![A_384, B_385]: (k5_xboole_0(A_384, k3_xboole_0(A_384, B_385))=k4_xboole_0(A_384, B_385))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.98/2.52  tff(c_6483, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6471])).
% 6.98/2.52  tff(c_6553, plain, (![A_392, B_393]: (k5_xboole_0(A_392, k3_xboole_0(A_392, B_393))=k4_xboole_0(A_392, k3_xboole_0(A_392, B_393)))), inference(superposition, [status(thm), theory('equality')], [c_6541, c_6483])).
% 6.98/2.52  tff(c_6597, plain, (![A_392, B_393]: (k4_xboole_0(A_392, k3_xboole_0(A_392, B_393))=k4_xboole_0(A_392, B_393))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6553])).
% 6.98/2.52  tff(c_6702, plain, (![B_17, A_16]: (r1_xboole_0(B_17, A_16) | k4_xboole_0(A_16, B_17)!=A_16)), inference(resolution, [status(thm)], [c_18, c_6696])).
% 6.98/2.52  tff(c_8408, plain, (![A_472, B_473, C_474]: (~r1_xboole_0(k3_xboole_0(A_472, B_473), A_472) | ~r2_hidden(C_474, k3_xboole_0(A_472, B_473)))), inference(superposition, [status(thm), theory('equality')], [c_6541, c_8])).
% 6.98/2.52  tff(c_8429, plain, (![C_474, A_16, B_473]: (~r2_hidden(C_474, k3_xboole_0(A_16, B_473)) | k4_xboole_0(A_16, k3_xboole_0(A_16, B_473))!=A_16)), inference(resolution, [status(thm)], [c_6702, c_8408])).
% 6.98/2.52  tff(c_8459, plain, (![C_475, A_476, B_477]: (~r2_hidden(C_475, k3_xboole_0(A_476, B_477)) | k4_xboole_0(A_476, B_477)!=A_476)), inference(demodulation, [status(thm), theory('equality')], [c_6597, c_8429])).
% 6.98/2.52  tff(c_8505, plain, (![C_475, B_2, A_1]: (~r2_hidden(C_475, k3_xboole_0(B_2, A_1)) | k4_xboole_0(A_1, B_2)!=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_8459])).
% 6.98/2.52  tff(c_10361, plain, (![C_524, A_525]: (k4_xboole_0(C_524, k1_tarski(A_525))!=C_524 | ~r2_hidden(A_525, C_524))), inference(resolution, [status(thm)], [c_10259, c_8505])).
% 6.98/2.52  tff(c_10364, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7818, c_10361])).
% 6.98/2.52  tff(c_10375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6304, c_10364])).
% 6.98/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.52  
% 6.98/2.52  Inference rules
% 6.98/2.52  ----------------------
% 6.98/2.52  #Ref     : 0
% 6.98/2.52  #Sup     : 2749
% 6.98/2.52  #Fact    : 0
% 6.98/2.52  #Define  : 0
% 6.98/2.52  #Split   : 2
% 6.98/2.52  #Chain   : 0
% 6.98/2.52  #Close   : 0
% 6.98/2.52  
% 6.98/2.52  Ordering : KBO
% 6.98/2.52  
% 6.98/2.52  Simplification rules
% 6.98/2.52  ----------------------
% 6.98/2.52  #Subsume      : 711
% 6.98/2.52  #Demod        : 2029
% 6.98/2.52  #Tautology    : 862
% 6.98/2.52  #SimpNegUnit  : 5
% 6.98/2.52  #BackRed      : 0
% 6.98/2.52  
% 6.98/2.52  #Partial instantiations: 0
% 6.98/2.52  #Strategies tried      : 1
% 6.98/2.52  
% 6.98/2.52  Timing (in seconds)
% 6.98/2.52  ----------------------
% 6.98/2.52  Preprocessing        : 0.32
% 6.98/2.52  Parsing              : 0.18
% 6.98/2.52  CNF conversion       : 0.02
% 6.98/2.52  Main loop            : 1.41
% 6.98/2.52  Inferencing          : 0.42
% 6.98/2.52  Reduction            : 0.62
% 6.98/2.52  Demodulation         : 0.52
% 6.98/2.52  BG Simplification    : 0.05
% 6.98/2.52  Subsumption          : 0.24
% 6.98/2.52  Abstraction          : 0.08
% 6.98/2.52  MUC search           : 0.00
% 6.98/2.52  Cooper               : 0.00
% 6.98/2.52  Total                : 1.78
% 6.98/2.52  Index Insertion      : 0.00
% 6.98/2.52  Index Deletion       : 0.00
% 6.98/2.52  Index Matching       : 0.00
% 6.98/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
