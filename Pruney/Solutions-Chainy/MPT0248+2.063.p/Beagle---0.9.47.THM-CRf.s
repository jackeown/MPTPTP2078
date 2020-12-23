%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:12 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 471 expanded)
%              Number of leaves         :   40 ( 167 expanded)
%              Depth                    :   25
%              Number of atoms          :  155 ( 749 expanded)
%              Number of equality atoms :  123 ( 714 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_70,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_60,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_118,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_99,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_114,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_28])).

tff(c_668,plain,(
    ! [B_117,A_118] :
      ( k1_tarski(B_117) = A_118
      | k1_xboole_0 = A_118
      | ~ r1_tarski(A_118,k1_tarski(B_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_679,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_114,c_668])).

tff(c_687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_99,c_679])).

tff(c_688,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_689,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_26,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_691,plain,(
    ! [A_22] : k5_xboole_0(A_22,'#skF_4') = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_26])).

tff(c_32,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_692,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_32])).

tff(c_22,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_690,plain,(
    ! [A_19] : k3_xboole_0(A_19,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_689,c_22])).

tff(c_947,plain,(
    ! [A_142,B_143] : k5_xboole_0(A_142,k3_xboole_0(A_142,B_143)) = k4_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_974,plain,(
    ! [A_19] : k5_xboole_0(A_19,'#skF_4') = k4_xboole_0(A_19,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_947])).

tff(c_981,plain,(
    ! [A_19] : k4_xboole_0(A_19,'#skF_4') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_974])).

tff(c_1058,plain,(
    ! [A_152,B_153] : k5_xboole_0(A_152,k4_xboole_0(B_153,A_152)) = k2_xboole_0(A_152,B_153) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1079,plain,(
    ! [A_19] : k5_xboole_0('#skF_4',A_19) = k2_xboole_0('#skF_4',A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_1058])).

tff(c_1790,plain,(
    ! [A_200,B_201,C_202] : k5_xboole_0(k5_xboole_0(A_200,B_201),C_202) = k5_xboole_0(A_200,k5_xboole_0(B_201,C_202)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2191,plain,(
    ! [A_242,B_243] : k5_xboole_0(A_242,k5_xboole_0(B_243,k5_xboole_0(A_242,B_243))) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1790,c_692])).

tff(c_2246,plain,(
    ! [A_22] : k5_xboole_0(A_22,k5_xboole_0('#skF_4',A_22)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_2191])).

tff(c_2262,plain,(
    ! [A_244] : k5_xboole_0(A_244,k2_xboole_0('#skF_4',A_244)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_2246])).

tff(c_2299,plain,(
    k5_xboole_0('#skF_5',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2262])).

tff(c_30,plain,(
    ! [A_25,B_26,C_27] : k5_xboole_0(k5_xboole_0(A_25,B_26),C_27) = k5_xboole_0(A_25,k5_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2314,plain,(
    ! [C_27] : k5_xboole_0('#skF_5',k5_xboole_0(k1_tarski('#skF_3'),C_27)) = k5_xboole_0('#skF_4',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_2299,c_30])).

tff(c_2436,plain,(
    ! [C_267] : k5_xboole_0('#skF_5',k5_xboole_0(k1_tarski('#skF_3'),C_267)) = k2_xboole_0('#skF_4',C_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_2314])).

tff(c_2488,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_2436])).

tff(c_2499,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_2488])).

tff(c_2260,plain,(
    ! [A_22] : k5_xboole_0(A_22,k2_xboole_0('#skF_4',A_22)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_2246])).

tff(c_2509,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),'#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2499,c_2260])).

tff(c_2318,plain,(
    ! [C_27] : k5_xboole_0('#skF_5',k5_xboole_0(k1_tarski('#skF_3'),C_27)) = k2_xboole_0('#skF_4',C_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_2314])).

tff(c_2544,plain,(
    k5_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2509,c_2318])).

tff(c_2553,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_64,c_2544])).

tff(c_2555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_688,c_2553])).

tff(c_2556,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2557,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2594,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2557,c_62])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2858,plain,(
    ! [A_291,B_292] : k5_xboole_0(A_291,k3_xboole_0(A_291,B_292)) = k4_xboole_0(A_291,B_292) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2891,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2858])).

tff(c_2900,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2891])).

tff(c_3043,plain,(
    ! [A_305,B_306] : k4_xboole_0(A_305,k4_xboole_0(A_305,B_306)) = k3_xboole_0(A_305,B_306) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3084,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_3043])).

tff(c_3098,plain,(
    ! [A_307] : k4_xboole_0(A_307,A_307) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3084])).

tff(c_3103,plain,(
    ! [A_307] : k4_xboole_0(A_307,k1_xboole_0) = k3_xboole_0(A_307,A_307) ),
    inference(superposition,[status(thm),theory(equality)],[c_3098,c_24])).

tff(c_3121,plain,(
    ! [A_307] : k3_xboole_0(A_307,A_307) = A_307 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2900,c_3103])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3129,plain,(
    ! [A_308] : k3_xboole_0(A_308,A_308) = A_308 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2900,c_3103])).

tff(c_16,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3197,plain,(
    ! [A_313,C_314] :
      ( ~ r1_xboole_0(A_313,A_313)
      | ~ r2_hidden(C_314,A_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3129,c_16])).

tff(c_3200,plain,(
    ! [C_314,B_9] :
      ( ~ r2_hidden(C_314,B_9)
      | k3_xboole_0(B_9,B_9) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_3197])).

tff(c_3337,plain,(
    ! [C_323,B_324] :
      ( ~ r2_hidden(C_323,B_324)
      | k1_xboole_0 != B_324 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3121,c_3200])).

tff(c_3344,plain,(
    ! [A_325,B_326] :
      ( k1_xboole_0 != A_325
      | r1_tarski(A_325,B_326) ) ),
    inference(resolution,[status(thm)],[c_8,c_3337])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3401,plain,(
    ! [A_328,B_329] :
      ( k3_xboole_0(A_328,B_329) = A_328
      | k1_xboole_0 != A_328 ) ),
    inference(resolution,[status(thm)],[c_3344,c_20])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3414,plain,(
    ! [A_328,B_329] :
      ( k5_xboole_0(A_328,A_328) = k4_xboole_0(A_328,B_329)
      | k1_xboole_0 != A_328 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3401,c_18])).

tff(c_3455,plain,(
    ! [A_330,B_331] :
      ( k4_xboole_0(A_330,B_331) = k1_xboole_0
      | k1_xboole_0 != A_330 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3414])).

tff(c_3590,plain,(
    ! [A_339,B_340] :
      ( k3_xboole_0(A_339,B_340) = k1_xboole_0
      | k1_xboole_0 != A_339 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3455])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3733,plain,(
    ! [B_345,A_346] :
      ( k3_xboole_0(B_345,A_346) = k1_xboole_0
      | k1_xboole_0 != A_346 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3590,c_2])).

tff(c_3755,plain,(
    ! [B_345,A_346] :
      ( k5_xboole_0(B_345,k1_xboole_0) = k4_xboole_0(B_345,A_346)
      | k1_xboole_0 != A_346 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3733,c_18])).

tff(c_3879,plain,(
    ! [B_345] : k4_xboole_0(B_345,k1_xboole_0) = B_345 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3755])).

tff(c_2564,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_64])).

tff(c_34,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3203,plain,(
    ! [A_315,B_316] : k5_xboole_0(A_315,k4_xboole_0(B_316,A_315)) = k2_xboole_0(A_315,B_316) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3230,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,A_19) = k2_xboole_0(k1_xboole_0,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_3203])).

tff(c_3799,plain,(
    ! [A_350,B_351,C_352] : k5_xboole_0(k5_xboole_0(A_350,B_351),C_352) = k5_xboole_0(A_350,k5_xboole_0(B_351,C_352)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3854,plain,(
    ! [A_28,C_352] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_352)) = k5_xboole_0(k1_xboole_0,C_352) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3799])).

tff(c_4379,plain,(
    ! [A_401,C_402] : k5_xboole_0(A_401,k5_xboole_0(A_401,C_402)) = k2_xboole_0(k1_xboole_0,C_402) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_3854])).

tff(c_4452,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4379])).

tff(c_4467,plain,(
    ! [A_28] : k2_xboole_0(k1_xboole_0,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4452])).

tff(c_3867,plain,(
    ! [A_28,C_352] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_352)) = k2_xboole_0(k1_xboole_0,C_352) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_3854])).

tff(c_4612,plain,(
    ! [A_412,C_413] : k5_xboole_0(A_412,k5_xboole_0(A_412,C_413)) = C_413 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4467,c_3867])).

tff(c_5470,plain,(
    ! [A_447,B_448] : k5_xboole_0(A_447,k2_xboole_0(A_447,B_448)) = k4_xboole_0(B_448,A_447) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4612])).

tff(c_5522,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2564,c_5470])).

tff(c_5532,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5522])).

tff(c_5548,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5532,c_24])).

tff(c_5563,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3879,c_2,c_5548])).

tff(c_5608,plain,(
    k5_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5563,c_18])).

tff(c_3858,plain,(
    ! [A_350,B_351] : k5_xboole_0(A_350,k5_xboole_0(B_351,k5_xboole_0(A_350,B_351))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3799])).

tff(c_4656,plain,(
    ! [B_351,A_350] : k5_xboole_0(B_351,k5_xboole_0(A_350,B_351)) = k5_xboole_0(A_350,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3858,c_4612])).

tff(c_4695,plain,(
    ! [B_351,A_350] : k5_xboole_0(B_351,k5_xboole_0(A_350,B_351)) = A_350 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4656])).

tff(c_5680,plain,(
    k5_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5608,c_4695])).

tff(c_5743,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5680,c_34])).

tff(c_5796,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5743,c_28])).

tff(c_3554,plain,(
    ! [B_334,A_335] :
      ( k1_tarski(B_334) = A_335
      | k1_xboole_0 = A_335
      | ~ r1_tarski(A_335,k1_tarski(B_334)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3565,plain,(
    ! [A_335] :
      ( k1_tarski('#skF_3') = A_335
      | k1_xboole_0 = A_335
      | ~ r1_tarski(A_335,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2557,c_3554])).

tff(c_3569,plain,(
    ! [A_335] :
      ( A_335 = '#skF_4'
      | k1_xboole_0 = A_335
      | ~ r1_tarski(A_335,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_3565])).

tff(c_5810,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5796,c_3569])).

tff(c_5817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2556,c_2594,c_5810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:59:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.97  
% 4.79/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.79/1.97  
% 4.79/1.97  %Foreground sorts:
% 4.79/1.97  
% 4.79/1.97  
% 4.79/1.97  %Background operators:
% 4.79/1.97  
% 4.79/1.97  
% 4.79/1.97  %Foreground operators:
% 4.79/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.79/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.79/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.79/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.79/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.79/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.79/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.79/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.79/1.97  tff('#skF_5', type, '#skF_5': $i).
% 4.79/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.79/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.79/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.79/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.79/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.79/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.79/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.79/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.79/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.79/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.79/1.98  
% 5.14/2.00  tff(f_113, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.14/2.00  tff(f_66, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.14/2.00  tff(f_92, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.14/2.00  tff(f_64, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.14/2.00  tff(f_70, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.14/2.00  tff(f_60, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.14/2.00  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.14/2.00  tff(f_72, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.14/2.00  tff(f_68, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.14/2.00  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.14/2.00  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.14/2.00  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.14/2.00  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.14/2.00  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.14/2.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.14/2.00  tff(c_60, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.14/2.00  tff(c_118, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 5.14/2.00  tff(c_58, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.14/2.00  tff(c_99, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 5.14/2.00  tff(c_64, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.14/2.00  tff(c_28, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.14/2.00  tff(c_114, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_28])).
% 5.14/2.00  tff(c_668, plain, (![B_117, A_118]: (k1_tarski(B_117)=A_118 | k1_xboole_0=A_118 | ~r1_tarski(A_118, k1_tarski(B_117)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.14/2.00  tff(c_679, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_114, c_668])).
% 5.14/2.00  tff(c_687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_99, c_679])).
% 5.14/2.00  tff(c_688, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 5.14/2.00  tff(c_689, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 5.14/2.00  tff(c_26, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.14/2.00  tff(c_691, plain, (![A_22]: (k5_xboole_0(A_22, '#skF_4')=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_689, c_26])).
% 5.14/2.00  tff(c_32, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.14/2.00  tff(c_692, plain, (![A_28]: (k5_xboole_0(A_28, A_28)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_689, c_32])).
% 5.14/2.00  tff(c_22, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.14/2.00  tff(c_690, plain, (![A_19]: (k3_xboole_0(A_19, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_689, c_689, c_22])).
% 5.14/2.00  tff(c_947, plain, (![A_142, B_143]: (k5_xboole_0(A_142, k3_xboole_0(A_142, B_143))=k4_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.14/2.00  tff(c_974, plain, (![A_19]: (k5_xboole_0(A_19, '#skF_4')=k4_xboole_0(A_19, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_690, c_947])).
% 5.14/2.00  tff(c_981, plain, (![A_19]: (k4_xboole_0(A_19, '#skF_4')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_691, c_974])).
% 5.14/2.00  tff(c_1058, plain, (![A_152, B_153]: (k5_xboole_0(A_152, k4_xboole_0(B_153, A_152))=k2_xboole_0(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.14/2.00  tff(c_1079, plain, (![A_19]: (k5_xboole_0('#skF_4', A_19)=k2_xboole_0('#skF_4', A_19))), inference(superposition, [status(thm), theory('equality')], [c_981, c_1058])).
% 5.14/2.00  tff(c_1790, plain, (![A_200, B_201, C_202]: (k5_xboole_0(k5_xboole_0(A_200, B_201), C_202)=k5_xboole_0(A_200, k5_xboole_0(B_201, C_202)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.14/2.00  tff(c_2191, plain, (![A_242, B_243]: (k5_xboole_0(A_242, k5_xboole_0(B_243, k5_xboole_0(A_242, B_243)))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1790, c_692])).
% 5.14/2.00  tff(c_2246, plain, (![A_22]: (k5_xboole_0(A_22, k5_xboole_0('#skF_4', A_22))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_691, c_2191])).
% 5.14/2.00  tff(c_2262, plain, (![A_244]: (k5_xboole_0(A_244, k2_xboole_0('#skF_4', A_244))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_2246])).
% 5.14/2.00  tff(c_2299, plain, (k5_xboole_0('#skF_5', k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_64, c_2262])).
% 5.14/2.00  tff(c_30, plain, (![A_25, B_26, C_27]: (k5_xboole_0(k5_xboole_0(A_25, B_26), C_27)=k5_xboole_0(A_25, k5_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.14/2.00  tff(c_2314, plain, (![C_27]: (k5_xboole_0('#skF_5', k5_xboole_0(k1_tarski('#skF_3'), C_27))=k5_xboole_0('#skF_4', C_27))), inference(superposition, [status(thm), theory('equality')], [c_2299, c_30])).
% 5.14/2.00  tff(c_2436, plain, (![C_267]: (k5_xboole_0('#skF_5', k5_xboole_0(k1_tarski('#skF_3'), C_267))=k2_xboole_0('#skF_4', C_267))), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_2314])).
% 5.14/2.00  tff(c_2488, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_692, c_2436])).
% 5.14/2.00  tff(c_2499, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_691, c_2488])).
% 5.14/2.00  tff(c_2260, plain, (![A_22]: (k5_xboole_0(A_22, k2_xboole_0('#skF_4', A_22))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_2246])).
% 5.14/2.00  tff(c_2509, plain, (k5_xboole_0(k1_tarski('#skF_3'), '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2499, c_2260])).
% 5.14/2.00  tff(c_2318, plain, (![C_27]: (k5_xboole_0('#skF_5', k5_xboole_0(k1_tarski('#skF_3'), C_27))=k2_xboole_0('#skF_4', C_27))), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_2314])).
% 5.14/2.00  tff(c_2544, plain, (k5_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2509, c_2318])).
% 5.14/2.00  tff(c_2553, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_691, c_64, c_2544])).
% 5.14/2.00  tff(c_2555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_688, c_2553])).
% 5.14/2.00  tff(c_2556, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 5.14/2.00  tff(c_2557, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 5.14/2.00  tff(c_62, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.14/2.00  tff(c_2594, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2557, c_62])).
% 5.14/2.00  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.14/2.00  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.14/2.00  tff(c_2858, plain, (![A_291, B_292]: (k5_xboole_0(A_291, k3_xboole_0(A_291, B_292))=k4_xboole_0(A_291, B_292))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.14/2.00  tff(c_2891, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2858])).
% 5.14/2.00  tff(c_2900, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2891])).
% 5.14/2.00  tff(c_3043, plain, (![A_305, B_306]: (k4_xboole_0(A_305, k4_xboole_0(A_305, B_306))=k3_xboole_0(A_305, B_306))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.14/2.00  tff(c_3084, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2900, c_3043])).
% 5.14/2.00  tff(c_3098, plain, (![A_307]: (k4_xboole_0(A_307, A_307)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3084])).
% 5.14/2.00  tff(c_3103, plain, (![A_307]: (k4_xboole_0(A_307, k1_xboole_0)=k3_xboole_0(A_307, A_307))), inference(superposition, [status(thm), theory('equality')], [c_3098, c_24])).
% 5.14/2.00  tff(c_3121, plain, (![A_307]: (k3_xboole_0(A_307, A_307)=A_307)), inference(demodulation, [status(thm), theory('equality')], [c_2900, c_3103])).
% 5.14/2.00  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.14/2.00  tff(c_3129, plain, (![A_308]: (k3_xboole_0(A_308, A_308)=A_308)), inference(demodulation, [status(thm), theory('equality')], [c_2900, c_3103])).
% 5.14/2.00  tff(c_16, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.14/2.00  tff(c_3197, plain, (![A_313, C_314]: (~r1_xboole_0(A_313, A_313) | ~r2_hidden(C_314, A_313))), inference(superposition, [status(thm), theory('equality')], [c_3129, c_16])).
% 5.14/2.00  tff(c_3200, plain, (![C_314, B_9]: (~r2_hidden(C_314, B_9) | k3_xboole_0(B_9, B_9)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_3197])).
% 5.14/2.00  tff(c_3337, plain, (![C_323, B_324]: (~r2_hidden(C_323, B_324) | k1_xboole_0!=B_324)), inference(demodulation, [status(thm), theory('equality')], [c_3121, c_3200])).
% 5.14/2.00  tff(c_3344, plain, (![A_325, B_326]: (k1_xboole_0!=A_325 | r1_tarski(A_325, B_326))), inference(resolution, [status(thm)], [c_8, c_3337])).
% 5.14/2.00  tff(c_20, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.14/2.00  tff(c_3401, plain, (![A_328, B_329]: (k3_xboole_0(A_328, B_329)=A_328 | k1_xboole_0!=A_328)), inference(resolution, [status(thm)], [c_3344, c_20])).
% 5.14/2.00  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.14/2.00  tff(c_3414, plain, (![A_328, B_329]: (k5_xboole_0(A_328, A_328)=k4_xboole_0(A_328, B_329) | k1_xboole_0!=A_328)), inference(superposition, [status(thm), theory('equality')], [c_3401, c_18])).
% 5.14/2.00  tff(c_3455, plain, (![A_330, B_331]: (k4_xboole_0(A_330, B_331)=k1_xboole_0 | k1_xboole_0!=A_330)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3414])).
% 5.14/2.00  tff(c_3590, plain, (![A_339, B_340]: (k3_xboole_0(A_339, B_340)=k1_xboole_0 | k1_xboole_0!=A_339)), inference(superposition, [status(thm), theory('equality')], [c_24, c_3455])).
% 5.14/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.14/2.00  tff(c_3733, plain, (![B_345, A_346]: (k3_xboole_0(B_345, A_346)=k1_xboole_0 | k1_xboole_0!=A_346)), inference(superposition, [status(thm), theory('equality')], [c_3590, c_2])).
% 5.14/2.00  tff(c_3755, plain, (![B_345, A_346]: (k5_xboole_0(B_345, k1_xboole_0)=k4_xboole_0(B_345, A_346) | k1_xboole_0!=A_346)), inference(superposition, [status(thm), theory('equality')], [c_3733, c_18])).
% 5.14/2.00  tff(c_3879, plain, (![B_345]: (k4_xboole_0(B_345, k1_xboole_0)=B_345)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3755])).
% 5.14/2.00  tff(c_2564, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_64])).
% 5.14/2.00  tff(c_34, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.14/2.00  tff(c_3203, plain, (![A_315, B_316]: (k5_xboole_0(A_315, k4_xboole_0(B_316, A_315))=k2_xboole_0(A_315, B_316))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.14/2.00  tff(c_3230, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, A_19)=k2_xboole_0(k1_xboole_0, A_19))), inference(superposition, [status(thm), theory('equality')], [c_2900, c_3203])).
% 5.14/2.00  tff(c_3799, plain, (![A_350, B_351, C_352]: (k5_xboole_0(k5_xboole_0(A_350, B_351), C_352)=k5_xboole_0(A_350, k5_xboole_0(B_351, C_352)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.14/2.00  tff(c_3854, plain, (![A_28, C_352]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_352))=k5_xboole_0(k1_xboole_0, C_352))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3799])).
% 5.14/2.00  tff(c_4379, plain, (![A_401, C_402]: (k5_xboole_0(A_401, k5_xboole_0(A_401, C_402))=k2_xboole_0(k1_xboole_0, C_402))), inference(demodulation, [status(thm), theory('equality')], [c_3230, c_3854])).
% 5.14/2.00  tff(c_4452, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_28))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4379])).
% 5.14/2.00  tff(c_4467, plain, (![A_28]: (k2_xboole_0(k1_xboole_0, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4452])).
% 5.14/2.00  tff(c_3867, plain, (![A_28, C_352]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_352))=k2_xboole_0(k1_xboole_0, C_352))), inference(demodulation, [status(thm), theory('equality')], [c_3230, c_3854])).
% 5.14/2.00  tff(c_4612, plain, (![A_412, C_413]: (k5_xboole_0(A_412, k5_xboole_0(A_412, C_413))=C_413)), inference(demodulation, [status(thm), theory('equality')], [c_4467, c_3867])).
% 5.14/2.00  tff(c_5470, plain, (![A_447, B_448]: (k5_xboole_0(A_447, k2_xboole_0(A_447, B_448))=k4_xboole_0(B_448, A_447))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4612])).
% 5.14/2.00  tff(c_5522, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2564, c_5470])).
% 5.14/2.00  tff(c_5532, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5522])).
% 5.14/2.00  tff(c_5548, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5532, c_24])).
% 5.14/2.00  tff(c_5563, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3879, c_2, c_5548])).
% 5.14/2.00  tff(c_5608, plain, (k5_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5563, c_18])).
% 5.14/2.00  tff(c_3858, plain, (![A_350, B_351]: (k5_xboole_0(A_350, k5_xboole_0(B_351, k5_xboole_0(A_350, B_351)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_3799])).
% 5.14/2.00  tff(c_4656, plain, (![B_351, A_350]: (k5_xboole_0(B_351, k5_xboole_0(A_350, B_351))=k5_xboole_0(A_350, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3858, c_4612])).
% 5.14/2.00  tff(c_4695, plain, (![B_351, A_350]: (k5_xboole_0(B_351, k5_xboole_0(A_350, B_351))=A_350)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4656])).
% 5.14/2.00  tff(c_5680, plain, (k5_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5608, c_4695])).
% 5.14/2.00  tff(c_5743, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5680, c_34])).
% 5.14/2.00  tff(c_5796, plain, (r1_tarski('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5743, c_28])).
% 5.14/2.00  tff(c_3554, plain, (![B_334, A_335]: (k1_tarski(B_334)=A_335 | k1_xboole_0=A_335 | ~r1_tarski(A_335, k1_tarski(B_334)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.14/2.00  tff(c_3565, plain, (![A_335]: (k1_tarski('#skF_3')=A_335 | k1_xboole_0=A_335 | ~r1_tarski(A_335, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2557, c_3554])).
% 5.14/2.00  tff(c_3569, plain, (![A_335]: (A_335='#skF_4' | k1_xboole_0=A_335 | ~r1_tarski(A_335, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_3565])).
% 5.14/2.00  tff(c_5810, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_5796, c_3569])).
% 5.14/2.00  tff(c_5817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2556, c_2594, c_5810])).
% 5.14/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/2.00  
% 5.14/2.00  Inference rules
% 5.14/2.00  ----------------------
% 5.14/2.00  #Ref     : 2
% 5.14/2.00  #Sup     : 1428
% 5.14/2.00  #Fact    : 0
% 5.14/2.00  #Define  : 0
% 5.14/2.00  #Split   : 11
% 5.14/2.00  #Chain   : 0
% 5.14/2.00  #Close   : 0
% 5.14/2.00  
% 5.14/2.00  Ordering : KBO
% 5.14/2.00  
% 5.14/2.00  Simplification rules
% 5.14/2.00  ----------------------
% 5.14/2.00  #Subsume      : 270
% 5.14/2.00  #Demod        : 675
% 5.14/2.00  #Tautology    : 845
% 5.14/2.00  #SimpNegUnit  : 33
% 5.14/2.00  #BackRed      : 24
% 5.14/2.00  
% 5.14/2.00  #Partial instantiations: 0
% 5.14/2.00  #Strategies tried      : 1
% 5.14/2.00  
% 5.14/2.00  Timing (in seconds)
% 5.14/2.00  ----------------------
% 5.14/2.00  Preprocessing        : 0.35
% 5.14/2.00  Parsing              : 0.19
% 5.14/2.00  CNF conversion       : 0.02
% 5.14/2.00  Main loop            : 0.85
% 5.14/2.00  Inferencing          : 0.31
% 5.14/2.00  Reduction            : 0.32
% 5.14/2.00  Demodulation         : 0.24
% 5.14/2.00  BG Simplification    : 0.04
% 5.14/2.00  Subsumption          : 0.13
% 5.14/2.00  Abstraction          : 0.04
% 5.14/2.00  MUC search           : 0.00
% 5.14/2.00  Cooper               : 0.00
% 5.14/2.00  Total                : 1.25
% 5.14/2.00  Index Insertion      : 0.00
% 5.14/2.00  Index Deletion       : 0.00
% 5.14/2.00  Index Matching       : 0.00
% 5.14/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
