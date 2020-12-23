%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:25 EST 2020

% Result     : Theorem 8.81s
% Output     : CNFRefutation 9.09s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 168 expanded)
%              Number of leaves         :   37 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 240 expanded)
%              Number of equality atoms :   56 ( 145 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_62,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_102,plain,(
    ! [A_65,B_66] : r1_tarski(A_65,k2_xboole_0(A_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_102])).

tff(c_48,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(k1_tarski(A_53),B_54)
      | r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_324,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_xboole_0(A_107,C_108)
      | ~ r1_xboole_0(B_109,C_108)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7041,plain,(
    ! [A_218,B_219,A_220] :
      ( r1_xboole_0(A_218,B_219)
      | ~ r1_tarski(A_218,k1_tarski(A_220))
      | r2_hidden(A_220,B_219) ) ),
    inference(resolution,[status(thm)],[c_48,c_324])).

tff(c_7058,plain,(
    ! [B_221] :
      ( r1_xboole_0('#skF_2',B_221)
      | r2_hidden('#skF_1',B_221) ) ),
    inference(resolution,[status(thm)],[c_105,c_7041])).

tff(c_34,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1329,plain,(
    ! [A_146,B_147,C_148] :
      ( r1_tarski(k2_tarski(A_146,B_147),C_148)
      | ~ r2_hidden(B_147,C_148)
      | ~ r2_hidden(A_146,C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6206,plain,(
    ! [A_204,C_205] :
      ( r1_tarski(k1_tarski(A_204),C_205)
      | ~ r2_hidden(A_204,C_205)
      | ~ r2_hidden(A_204,C_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1329])).

tff(c_251,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(B_89,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_258,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_251])).

tff(c_284,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_6230,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6206,c_284])).

tff(c_7070,plain,(
    r1_xboole_0('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_7058,c_6230])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7075,plain,(
    k3_xboole_0('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7070,c_4])).

tff(c_7081,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7075])).

tff(c_7083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7081])).

tff(c_7084,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_7088,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7084,c_64])).

tff(c_218,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7255,plain,(
    ! [A_243,B_244] :
      ( k3_xboole_0(k1_tarski(A_243),B_244) = k1_xboole_0
      | r2_hidden(A_243,B_244) ) ),
    inference(resolution,[status(thm)],[c_48,c_218])).

tff(c_7268,plain,(
    ! [B_244] :
      ( k3_xboole_0('#skF_2',B_244) = k1_xboole_0
      | r2_hidden('#skF_1',B_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7084,c_7255])).

tff(c_8198,plain,(
    ! [A_276,B_277,C_278] :
      ( r1_tarski(k2_tarski(A_276,B_277),C_278)
      | ~ r2_hidden(B_277,C_278)
      | ~ r2_hidden(A_276,C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10932,plain,(
    ! [A_346,C_347] :
      ( r1_tarski(k1_tarski(A_346),C_347)
      | ~ r2_hidden(A_346,C_347)
      | ~ r2_hidden(A_346,C_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_8198])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10963,plain,(
    ! [A_348,C_349] :
      ( k2_xboole_0(k1_tarski(A_348),C_349) = C_349
      | ~ r2_hidden(A_348,C_349) ) ),
    inference(resolution,[status(thm)],[c_10932,c_18])).

tff(c_11064,plain,(
    ! [C_350] :
      ( k2_xboole_0('#skF_2',C_350) = C_350
      | ~ r2_hidden('#skF_1',C_350) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7084,c_10963])).

tff(c_12695,plain,(
    ! [B_376] :
      ( k2_xboole_0('#skF_2',B_376) = B_376
      | k3_xboole_0('#skF_2',B_376) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7268,c_11064])).

tff(c_30,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7521,plain,(
    ! [A_260,B_261] : k5_xboole_0(k5_xboole_0(A_260,B_261),k2_xboole_0(A_260,B_261)) = k3_xboole_0(A_260,B_261) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7585,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,A_5),A_5) = k3_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7521])).

tff(c_7596,plain,(
    ! [A_262] : k5_xboole_0(k1_xboole_0,A_262) = A_262 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10,c_7585])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7627,plain,(
    ! [A_262] : k5_xboole_0(A_262,k1_xboole_0) = A_262 ),
    inference(superposition,[status(thm),theory(equality)],[c_7596,c_2])).

tff(c_7570,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7088,c_7521])).

tff(c_7591,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_7570])).

tff(c_7309,plain,(
    ! [A_253,B_254,C_255] : k5_xboole_0(k5_xboole_0(A_253,B_254),C_255) = k5_xboole_0(A_253,k5_xboole_0(B_254,C_255)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7325,plain,(
    ! [A_253,B_254] : k5_xboole_0(A_253,k5_xboole_0(B_254,k5_xboole_0(A_253,B_254))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7309,c_30])).

tff(c_7750,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7591,c_7325])).

tff(c_7592,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10,c_7585])).

tff(c_7348,plain,(
    ! [A_22,C_255] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_255)) = k5_xboole_0(k1_xboole_0,C_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7309])).

tff(c_7779,plain,(
    ! [A_264,C_265] : k5_xboole_0(A_264,k5_xboole_0(A_264,C_265)) = C_265 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7592,c_7348])).

tff(c_7819,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7750,c_7779])).

tff(c_7869,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7627,c_7819])).

tff(c_12730,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12695,c_7869])).

tff(c_12772,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7088,c_12730])).

tff(c_12774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_12772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:55:10 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.81/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.17  
% 8.81/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.81/3.18  
% 8.81/3.18  %Foreground sorts:
% 8.81/3.18  
% 8.81/3.18  
% 8.81/3.18  %Background operators:
% 8.81/3.18  
% 8.81/3.18  
% 8.81/3.18  %Foreground operators:
% 8.81/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.81/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.81/3.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.81/3.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.81/3.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.81/3.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.81/3.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.81/3.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.81/3.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.81/3.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.81/3.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.81/3.18  tff('#skF_2', type, '#skF_2': $i).
% 8.81/3.18  tff('#skF_3', type, '#skF_3': $i).
% 8.81/3.18  tff('#skF_1', type, '#skF_1': $i).
% 8.81/3.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.81/3.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.81/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.81/3.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.81/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.81/3.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.81/3.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.81/3.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.81/3.18  
% 9.09/3.19  tff(f_111, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 9.09/3.19  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.09/3.19  tff(f_65, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.09/3.19  tff(f_90, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.09/3.19  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 9.09/3.19  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.09/3.19  tff(f_98, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 9.09/3.19  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.09/3.19  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.09/3.19  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.09/3.19  tff(f_69, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.09/3.19  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.09/3.19  tff(f_71, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.09/3.19  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.09/3.19  tff(f_67, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.09/3.19  tff(c_62, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.09/3.19  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.09/3.19  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.09/3.19  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.09/3.19  tff(c_64, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.09/3.19  tff(c_102, plain, (![A_65, B_66]: (r1_tarski(A_65, k2_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.09/3.19  tff(c_105, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_102])).
% 9.09/3.19  tff(c_48, plain, (![A_53, B_54]: (r1_xboole_0(k1_tarski(A_53), B_54) | r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.09/3.19  tff(c_324, plain, (![A_107, C_108, B_109]: (r1_xboole_0(A_107, C_108) | ~r1_xboole_0(B_109, C_108) | ~r1_tarski(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.09/3.19  tff(c_7041, plain, (![A_218, B_219, A_220]: (r1_xboole_0(A_218, B_219) | ~r1_tarski(A_218, k1_tarski(A_220)) | r2_hidden(A_220, B_219))), inference(resolution, [status(thm)], [c_48, c_324])).
% 9.09/3.19  tff(c_7058, plain, (![B_221]: (r1_xboole_0('#skF_2', B_221) | r2_hidden('#skF_1', B_221))), inference(resolution, [status(thm)], [c_105, c_7041])).
% 9.09/3.19  tff(c_34, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.09/3.19  tff(c_1329, plain, (![A_146, B_147, C_148]: (r1_tarski(k2_tarski(A_146, B_147), C_148) | ~r2_hidden(B_147, C_148) | ~r2_hidden(A_146, C_148))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.09/3.19  tff(c_6206, plain, (![A_204, C_205]: (r1_tarski(k1_tarski(A_204), C_205) | ~r2_hidden(A_204, C_205) | ~r2_hidden(A_204, C_205))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1329])).
% 9.09/3.19  tff(c_251, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(B_89, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.09/3.19  tff(c_258, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_105, c_251])).
% 9.09/3.19  tff(c_284, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_258])).
% 9.09/3.19  tff(c_6230, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6206, c_284])).
% 9.09/3.19  tff(c_7070, plain, (r1_xboole_0('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_7058, c_6230])).
% 9.09/3.19  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.09/3.19  tff(c_7075, plain, (k3_xboole_0('#skF_2', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_7070, c_4])).
% 9.09/3.19  tff(c_7081, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_7075])).
% 9.09/3.19  tff(c_7083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_7081])).
% 9.09/3.19  tff(c_7084, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_258])).
% 9.09/3.19  tff(c_7088, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7084, c_64])).
% 9.09/3.19  tff(c_218, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.09/3.19  tff(c_7255, plain, (![A_243, B_244]: (k3_xboole_0(k1_tarski(A_243), B_244)=k1_xboole_0 | r2_hidden(A_243, B_244))), inference(resolution, [status(thm)], [c_48, c_218])).
% 9.09/3.19  tff(c_7268, plain, (![B_244]: (k3_xboole_0('#skF_2', B_244)=k1_xboole_0 | r2_hidden('#skF_1', B_244))), inference(superposition, [status(thm), theory('equality')], [c_7084, c_7255])).
% 9.09/3.19  tff(c_8198, plain, (![A_276, B_277, C_278]: (r1_tarski(k2_tarski(A_276, B_277), C_278) | ~r2_hidden(B_277, C_278) | ~r2_hidden(A_276, C_278))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.09/3.19  tff(c_10932, plain, (![A_346, C_347]: (r1_tarski(k1_tarski(A_346), C_347) | ~r2_hidden(A_346, C_347) | ~r2_hidden(A_346, C_347))), inference(superposition, [status(thm), theory('equality')], [c_34, c_8198])).
% 9.09/3.19  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.09/3.19  tff(c_10963, plain, (![A_348, C_349]: (k2_xboole_0(k1_tarski(A_348), C_349)=C_349 | ~r2_hidden(A_348, C_349))), inference(resolution, [status(thm)], [c_10932, c_18])).
% 9.09/3.19  tff(c_11064, plain, (![C_350]: (k2_xboole_0('#skF_2', C_350)=C_350 | ~r2_hidden('#skF_1', C_350))), inference(superposition, [status(thm), theory('equality')], [c_7084, c_10963])).
% 9.09/3.19  tff(c_12695, plain, (![B_376]: (k2_xboole_0('#skF_2', B_376)=B_376 | k3_xboole_0('#skF_2', B_376)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7268, c_11064])).
% 9.09/3.19  tff(c_30, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.09/3.19  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.09/3.19  tff(c_7521, plain, (![A_260, B_261]: (k5_xboole_0(k5_xboole_0(A_260, B_261), k2_xboole_0(A_260, B_261))=k3_xboole_0(A_260, B_261))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.09/3.19  tff(c_7585, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, A_5), A_5)=k3_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7521])).
% 9.09/3.19  tff(c_7596, plain, (![A_262]: (k5_xboole_0(k1_xboole_0, A_262)=A_262)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10, c_7585])).
% 9.09/3.19  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.09/3.19  tff(c_7627, plain, (![A_262]: (k5_xboole_0(A_262, k1_xboole_0)=A_262)), inference(superposition, [status(thm), theory('equality')], [c_7596, c_2])).
% 9.09/3.19  tff(c_7570, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7088, c_7521])).
% 9.09/3.19  tff(c_7591, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_7570])).
% 9.09/3.19  tff(c_7309, plain, (![A_253, B_254, C_255]: (k5_xboole_0(k5_xboole_0(A_253, B_254), C_255)=k5_xboole_0(A_253, k5_xboole_0(B_254, C_255)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.09/3.19  tff(c_7325, plain, (![A_253, B_254]: (k5_xboole_0(A_253, k5_xboole_0(B_254, k5_xboole_0(A_253, B_254)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7309, c_30])).
% 9.09/3.19  tff(c_7750, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7591, c_7325])).
% 9.09/3.19  tff(c_7592, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10, c_7585])).
% 9.09/3.19  tff(c_7348, plain, (![A_22, C_255]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_255))=k5_xboole_0(k1_xboole_0, C_255))), inference(superposition, [status(thm), theory('equality')], [c_30, c_7309])).
% 9.09/3.19  tff(c_7779, plain, (![A_264, C_265]: (k5_xboole_0(A_264, k5_xboole_0(A_264, C_265))=C_265)), inference(demodulation, [status(thm), theory('equality')], [c_7592, c_7348])).
% 9.09/3.19  tff(c_7819, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7750, c_7779])).
% 9.09/3.19  tff(c_7869, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7627, c_7819])).
% 9.09/3.19  tff(c_12730, plain, (k1_xboole_0='#skF_3' | k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12695, c_7869])).
% 9.09/3.19  tff(c_12772, plain, (k1_xboole_0='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7088, c_12730])).
% 9.09/3.19  tff(c_12774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_12772])).
% 9.09/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.09/3.19  
% 9.09/3.19  Inference rules
% 9.09/3.19  ----------------------
% 9.09/3.19  #Ref     : 0
% 9.09/3.19  #Sup     : 3235
% 9.09/3.19  #Fact    : 0
% 9.09/3.19  #Define  : 0
% 9.09/3.19  #Split   : 3
% 9.09/3.19  #Chain   : 0
% 9.09/3.19  #Close   : 0
% 9.09/3.19  
% 9.09/3.19  Ordering : KBO
% 9.09/3.19  
% 9.09/3.19  Simplification rules
% 9.09/3.19  ----------------------
% 9.09/3.19  #Subsume      : 163
% 9.09/3.19  #Demod        : 3072
% 9.09/3.19  #Tautology    : 1676
% 9.09/3.19  #SimpNegUnit  : 15
% 9.09/3.19  #BackRed      : 13
% 9.09/3.19  
% 9.09/3.19  #Partial instantiations: 0
% 9.09/3.19  #Strategies tried      : 1
% 9.09/3.19  
% 9.09/3.19  Timing (in seconds)
% 9.09/3.19  ----------------------
% 9.09/3.20  Preprocessing        : 0.33
% 9.09/3.20  Parsing              : 0.17
% 9.09/3.20  CNF conversion       : 0.02
% 9.09/3.20  Main loop            : 2.09
% 9.09/3.20  Inferencing          : 0.52
% 9.09/3.20  Reduction            : 1.09
% 9.09/3.20  Demodulation         : 0.94
% 9.09/3.20  BG Simplification    : 0.07
% 9.09/3.20  Subsumption          : 0.30
% 9.09/3.20  Abstraction          : 0.09
% 9.09/3.20  MUC search           : 0.00
% 9.09/3.20  Cooper               : 0.00
% 9.09/3.20  Total                : 2.46
% 9.09/3.20  Index Insertion      : 0.00
% 9.09/3.20  Index Deletion       : 0.00
% 9.09/3.20  Index Matching       : 0.00
% 9.09/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
