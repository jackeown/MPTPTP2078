%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:10 EST 2020

% Result     : Theorem 8.24s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 361 expanded)
%              Number of leaves         :   45 ( 134 expanded)
%              Depth                    :   18
%              Number of atoms          :  242 ( 709 expanded)
%              Number of equality atoms :  102 ( 379 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_76,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_82,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_70,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_114,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_68,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_102,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_119,plain,(
    ! [A_75,B_76] : r1_tarski(A_75,k2_xboole_0(A_75,B_76)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_122,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_119])).

tff(c_1403,plain,(
    ! [B_169,A_170] :
      ( k1_tarski(B_169) = A_170
      | k1_xboole_0 = A_170
      | ~ r1_tarski(A_170,k1_tarski(B_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1430,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_122,c_1403])).

tff(c_1449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_102,c_1430])).

tff(c_1450,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2457,plain,(
    ! [A_252,B_253] :
      ( r2_hidden('#skF_2'(A_252,B_253),A_252)
      | r1_tarski(A_252,B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden('#skF_2'(A_9,B_10),B_10)
      | r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2468,plain,(
    ! [A_254] : r1_tarski(A_254,A_254) ),
    inference(resolution,[status(thm)],[c_2457,c_12])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2480,plain,(
    ! [A_254] : k3_xboole_0(A_254,A_254) = A_254 ),
    inference(resolution,[status(thm)],[c_2468,c_30])).

tff(c_1451,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1657,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_18])).

tff(c_2666,plain,(
    ! [A_261,B_262,C_263] :
      ( ~ r1_xboole_0(A_261,B_262)
      | ~ r2_hidden(C_263,k3_xboole_0(A_261,B_262)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2891,plain,(
    ! [A_281,C_282] :
      ( ~ r1_xboole_0(A_281,A_281)
      | ~ r2_hidden(C_282,A_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_2666])).

tff(c_2897,plain,(
    ! [C_282,B_15] :
      ( ~ r2_hidden(C_282,B_15)
      | k3_xboole_0(B_15,B_15) != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1657,c_2891])).

tff(c_2903,plain,(
    ! [C_283,B_284] :
      ( ~ r2_hidden(C_283,B_284)
      | B_284 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2480,c_2897])).

tff(c_2971,plain,(
    ! [A_287] :
      ( A_287 != '#skF_5'
      | v1_xboole_0(A_287) ) ),
    inference(resolution,[status(thm)],[c_8,c_2903])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2695,plain,(
    ! [A_264,B_265] :
      ( ~ v1_xboole_0(A_264)
      | r1_tarski(A_264,B_265) ) ),
    inference(resolution,[status(thm)],[c_2457,c_6])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2706,plain,(
    ! [A_264,B_265] :
      ( k2_xboole_0(A_264,B_265) = B_265
      | ~ v1_xboole_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_2695,c_28])).

tff(c_3175,plain,(
    ! [B_265] : k2_xboole_0('#skF_5',B_265) = B_265 ),
    inference(resolution,[status(thm)],[c_2971,c_2706])).

tff(c_3177,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3175,c_74])).

tff(c_3179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1450,c_3177])).

tff(c_3180,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3181,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3254,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3181,c_3181,c_72])).

tff(c_3210,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3181,c_74])).

tff(c_34,plain,(
    ! [A_32] : k5_xboole_0(A_32,k1_xboole_0) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),A_9)
      | r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4464,plain,(
    ! [A_387,B_388] :
      ( ~ r2_hidden('#skF_2'(A_387,B_388),B_388)
      | r1_tarski(A_387,B_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4472,plain,(
    ! [A_389] : r1_tarski(A_389,A_389) ),
    inference(resolution,[status(thm)],[c_14,c_4464])).

tff(c_4491,plain,(
    ! [A_389] : k3_xboole_0(A_389,A_389) = A_389 ),
    inference(resolution,[status(thm)],[c_4472,c_30])).

tff(c_4673,plain,(
    ! [A_394,B_395,C_396] :
      ( ~ r1_xboole_0(A_394,B_395)
      | ~ r2_hidden(C_396,k3_xboole_0(A_394,B_395)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6103,plain,(
    ! [A_447,C_448] :
      ( ~ r1_xboole_0(A_447,A_447)
      | ~ r2_hidden(C_448,A_447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4491,c_4673])).

tff(c_6109,plain,(
    ! [C_448,B_15] :
      ( ~ r2_hidden(C_448,B_15)
      | k3_xboole_0(B_15,B_15) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_6103])).

tff(c_6128,plain,(
    ! [C_449,B_450] :
      ( ~ r2_hidden(C_449,B_450)
      | k1_xboole_0 != B_450 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4491,c_6109])).

tff(c_6166,plain,(
    ! [A_452] :
      ( k1_xboole_0 != A_452
      | v1_xboole_0(A_452) ) ),
    inference(resolution,[status(thm)],[c_8,c_6128])).

tff(c_4318,plain,(
    ! [A_376,B_377] :
      ( r2_hidden('#skF_2'(A_376,B_377),A_376)
      | r1_tarski(A_376,B_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4323,plain,(
    ! [A_378,B_379] :
      ( ~ v1_xboole_0(A_378)
      | r1_tarski(A_378,B_379) ) ),
    inference(resolution,[status(thm)],[c_4318,c_6])).

tff(c_4339,plain,(
    ! [A_378,B_379] :
      ( k2_xboole_0(A_378,B_379) = B_379
      | ~ v1_xboole_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_4323,c_28])).

tff(c_6191,plain,(
    ! [A_452,B_379] :
      ( k2_xboole_0(A_452,B_379) = B_379
      | k1_xboole_0 != A_452 ) ),
    inference(resolution,[status(thm)],[c_6166,c_4339])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3632,plain,(
    ! [A_345,B_346,C_347] : r1_tarski(k3_xboole_0(A_345,B_346),k2_xboole_0(A_345,C_347)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7459,plain,(
    ! [B_500,A_501,C_502] : r1_tarski(k3_xboole_0(B_500,A_501),k2_xboole_0(A_501,C_502)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3632])).

tff(c_7472,plain,(
    ! [B_500,A_452,B_379] :
      ( r1_tarski(k3_xboole_0(B_500,A_452),B_379)
      | k1_xboole_0 != A_452 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6191,c_7459])).

tff(c_5328,plain,(
    ! [C_419,B_420,A_421] :
      ( r2_hidden(C_419,B_420)
      | ~ r2_hidden(C_419,A_421)
      | ~ r1_tarski(A_421,B_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12689,plain,(
    ! [A_650,B_651] :
      ( r2_hidden('#skF_1'(A_650),B_651)
      | ~ r1_tarski(A_650,B_651)
      | v1_xboole_0(A_650) ) ),
    inference(resolution,[status(thm)],[c_8,c_5328])).

tff(c_64,plain,(
    ! [B_65] : r1_tarski(k1_xboole_0,k1_tarski(B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3184,plain,(
    r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3181,c_64])).

tff(c_3357,plain,(
    ! [A_313,B_314] :
      ( k3_xboole_0(A_313,B_314) = A_313
      | ~ r1_tarski(A_313,B_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3376,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3184,c_3357])).

tff(c_3385,plain,(
    k3_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3376,c_2])).

tff(c_4703,plain,(
    ! [C_396] :
      ( ~ r1_xboole_0(k1_xboole_0,'#skF_5')
      | ~ r2_hidden(C_396,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3376,c_4673])).

tff(c_4931,plain,(
    ~ r1_xboole_0(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4703])).

tff(c_4934,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_4931])).

tff(c_4938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3385,c_2,c_4934])).

tff(c_4939,plain,(
    ! [C_396] : ~ r2_hidden(C_396,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4703])).

tff(c_12725,plain,(
    ! [A_652] :
      ( ~ r1_tarski(A_652,k1_xboole_0)
      | v1_xboole_0(A_652) ) ),
    inference(resolution,[status(thm)],[c_12689,c_4939])).

tff(c_13056,plain,(
    ! [B_659,A_660] :
      ( v1_xboole_0(k3_xboole_0(B_659,A_660))
      | k1_xboole_0 != A_660 ) ),
    inference(resolution,[status(thm)],[c_7472,c_12725])).

tff(c_6197,plain,(
    ! [A_453,B_454] :
      ( r2_hidden('#skF_3'(A_453,B_454),k3_xboole_0(A_453,B_454))
      | r1_xboole_0(A_453,B_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7883,plain,(
    ! [A_510,B_511] :
      ( ~ v1_xboole_0(k3_xboole_0(A_510,B_511))
      | r1_xboole_0(A_510,B_511) ) ),
    inference(resolution,[status(thm)],[c_6197,c_6])).

tff(c_7928,plain,(
    ! [A_512] :
      ( ~ v1_xboole_0(A_512)
      | r1_xboole_0(A_512,A_512) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4491,c_7883])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7941,plain,(
    ! [A_512] :
      ( k3_xboole_0(A_512,A_512) = k1_xboole_0
      | ~ v1_xboole_0(A_512) ) ),
    inference(resolution,[status(thm)],[c_7928,c_16])).

tff(c_7947,plain,(
    ! [A_512] :
      ( k1_xboole_0 = A_512
      | ~ v1_xboole_0(A_512) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4491,c_7941])).

tff(c_13461,plain,(
    ! [B_667,A_668] :
      ( k3_xboole_0(B_667,A_668) = k1_xboole_0
      | k1_xboole_0 != A_668 ) ),
    inference(resolution,[status(thm)],[c_13056,c_7947])).

tff(c_26,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_13623,plain,(
    ! [B_667,A_668] :
      ( k5_xboole_0(B_667,k1_xboole_0) = k4_xboole_0(B_667,A_668)
      | k1_xboole_0 != A_668 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13461,c_26])).

tff(c_13815,plain,(
    ! [B_667] : k4_xboole_0(B_667,k1_xboole_0) = B_667 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_13623])).

tff(c_62,plain,(
    ! [B_65] : r1_tarski(k1_tarski(B_65),k1_tarski(B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3452,plain,(
    ! [A_326,B_327] :
      ( r2_hidden(A_326,B_327)
      | ~ r1_tarski(k1_tarski(A_326),B_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3469,plain,(
    ! [B_328] : r2_hidden(B_328,k1_tarski(B_328)) ),
    inference(resolution,[status(thm)],[c_62,c_3452])).

tff(c_3483,plain,(
    ! [B_329] : ~ v1_xboole_0(k1_tarski(B_329)) ),
    inference(resolution,[status(thm)],[c_3469,c_6])).

tff(c_3485,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3181,c_3483])).

tff(c_36,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3373,plain,(
    ! [A_33,B_34] : k3_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = A_33 ),
    inference(resolution,[status(thm)],[c_36,c_3357])).

tff(c_7307,plain,(
    ! [A_496,B_497] :
      ( ~ r1_xboole_0(A_496,B_497)
      | v1_xboole_0(k3_xboole_0(A_496,B_497)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4673])).

tff(c_8129,plain,(
    ! [A_524,B_525] :
      ( ~ r1_xboole_0(A_524,k2_xboole_0(A_524,B_525))
      | v1_xboole_0(A_524) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3373,c_7307])).

tff(c_8171,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3210,c_8129])).

tff(c_8186,plain,(
    ~ r1_xboole_0('#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_3485,c_8171])).

tff(c_3436,plain,(
    ! [A_320,B_321] :
      ( r1_xboole_0(k1_tarski(A_320),B_321)
      | r2_hidden(A_320,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3441,plain,(
    ! [B_323] :
      ( r1_xboole_0('#skF_5',B_323)
      | r2_hidden('#skF_4',B_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3181,c_3436])).

tff(c_3428,plain,(
    ! [A_318,B_319] :
      ( r1_tarski(k1_tarski(A_318),B_319)
      | ~ r2_hidden(A_318,B_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3434,plain,(
    ! [B_319] :
      ( r1_tarski('#skF_5',B_319)
      | ~ r2_hidden('#skF_4',B_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3181,c_3428])).

tff(c_3448,plain,(
    ! [B_323] :
      ( r1_tarski('#skF_5',B_323)
      | r1_xboole_0('#skF_5',B_323) ) ),
    inference(resolution,[status(thm)],[c_3441,c_3434])).

tff(c_4717,plain,(
    ! [A_394,B_395] :
      ( ~ r1_xboole_0(A_394,B_395)
      | v1_xboole_0(k3_xboole_0(A_394,B_395)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4673])).

tff(c_8242,plain,(
    ! [A_528,B_529] :
      ( ~ v1_xboole_0(k3_xboole_0(A_528,B_529))
      | r1_xboole_0(B_529,A_528) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7883])).

tff(c_8377,plain,(
    ! [B_532,A_533] :
      ( r1_xboole_0(B_532,A_533)
      | ~ r1_xboole_0(A_533,B_532) ) ),
    inference(resolution,[status(thm)],[c_4717,c_8242])).

tff(c_8447,plain,(
    ! [B_535] :
      ( r1_xboole_0(B_535,'#skF_5')
      | r1_tarski('#skF_5',B_535) ) ),
    inference(resolution,[status(thm)],[c_3448,c_8377])).

tff(c_9696,plain,(
    ! [B_580] :
      ( k3_xboole_0(B_580,'#skF_5') = k1_xboole_0
      | r1_tarski('#skF_5',B_580) ) ),
    inference(resolution,[status(thm)],[c_8447,c_16])).

tff(c_3439,plain,(
    ! [B_321] :
      ( r1_xboole_0('#skF_5',B_321)
      | r2_hidden('#skF_4',B_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3181,c_3436])).

tff(c_5351,plain,(
    ! [B_420,B_321] :
      ( r2_hidden('#skF_4',B_420)
      | ~ r1_tarski(B_321,B_420)
      | r1_xboole_0('#skF_5',B_321) ) ),
    inference(resolution,[status(thm)],[c_3439,c_5328])).

tff(c_9709,plain,(
    ! [B_580] :
      ( r2_hidden('#skF_4',B_580)
      | r1_xboole_0('#skF_5','#skF_5')
      | k3_xboole_0(B_580,'#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9696,c_5351])).

tff(c_9743,plain,(
    ! [B_580] :
      ( r2_hidden('#skF_4',B_580)
      | k3_xboole_0(B_580,'#skF_5') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_8186,c_9709])).

tff(c_56,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3495,plain,(
    ! [A_330,B_331] :
      ( k2_xboole_0(A_330,B_331) = B_331
      | ~ r1_tarski(A_330,B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11023,plain,(
    ! [A_620,B_621] :
      ( k2_xboole_0(k1_tarski(A_620),B_621) = B_621
      | ~ r2_hidden(A_620,B_621) ) ),
    inference(resolution,[status(thm)],[c_56,c_3495])).

tff(c_11137,plain,(
    ! [B_622] :
      ( k2_xboole_0('#skF_5',B_622) = B_622
      | ~ r2_hidden('#skF_4',B_622) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3181,c_11023])).

tff(c_15525,plain,(
    ! [B_707] :
      ( k2_xboole_0('#skF_5',B_707) = B_707
      | k3_xboole_0(B_707,'#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9743,c_11137])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5931,plain,(
    ! [A_442,B_443] : k4_xboole_0(k2_xboole_0(A_442,B_443),k3_xboole_0(A_442,B_443)) = k5_xboole_0(A_442,B_443) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5973,plain,(
    k4_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_6')) = k5_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3210,c_5931])).

tff(c_5984,plain,(
    k4_xboole_0('#skF_5',k3_xboole_0('#skF_6','#skF_5')) = k5_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_5973])).

tff(c_15662,plain,
    ( k5_xboole_0('#skF_6','#skF_5') = k4_xboole_0('#skF_5',k1_xboole_0)
    | k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15525,c_5984])).

tff(c_15788,plain,
    ( k5_xboole_0('#skF_6','#skF_5') = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3210,c_13815,c_15662])).

tff(c_15789,plain,(
    k5_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3254,c_15788])).

tff(c_3260,plain,(
    ! [B_310,A_311] : k5_xboole_0(B_310,A_311) = k5_xboole_0(A_311,B_310) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3276,plain,(
    ! [A_311] : k5_xboole_0(k1_xboole_0,A_311) = A_311 ),
    inference(superposition,[status(thm),theory(equality)],[c_3260,c_34])).

tff(c_40,plain,(
    ! [A_38] : k5_xboole_0(A_38,A_38) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5421,plain,(
    ! [A_426,B_427,C_428] : k5_xboole_0(k5_xboole_0(A_426,B_427),C_428) = k5_xboole_0(A_426,k5_xboole_0(B_427,C_428)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5485,plain,(
    ! [A_38,C_428] : k5_xboole_0(A_38,k5_xboole_0(A_38,C_428)) = k5_xboole_0(k1_xboole_0,C_428) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5421])).

tff(c_5498,plain,(
    ! [A_38,C_428] : k5_xboole_0(A_38,k5_xboole_0(A_38,C_428)) = C_428 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3276,c_5485])).

tff(c_5499,plain,(
    ! [A_429,C_430] : k5_xboole_0(A_429,k5_xboole_0(A_429,C_430)) = C_430 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3276,c_5485])).

tff(c_5564,plain,(
    ! [A_431,B_432] : k5_xboole_0(A_431,k5_xboole_0(B_432,A_431)) = B_432 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5499])).

tff(c_5597,plain,(
    ! [A_38,C_428] : k5_xboole_0(k5_xboole_0(A_38,C_428),C_428) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_5498,c_5564])).

tff(c_15825,plain,(
    k5_xboole_0('#skF_5','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15789,c_5597])).

tff(c_15911,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15825,c_40])).

tff(c_15925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3180,c_15911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.24/2.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.96  
% 8.24/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.24/2.97  
% 8.24/2.97  %Foreground sorts:
% 8.24/2.97  
% 8.24/2.97  
% 8.24/2.97  %Background operators:
% 8.24/2.97  
% 8.24/2.97  
% 8.24/2.97  %Foreground operators:
% 8.24/2.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/2.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.24/2.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.24/2.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.24/2.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.24/2.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.24/2.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.24/2.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.24/2.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.24/2.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.24/2.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.24/2.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.24/2.97  tff('#skF_5', type, '#skF_5': $i).
% 8.24/2.97  tff('#skF_6', type, '#skF_6': $i).
% 8.24/2.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.24/2.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.24/2.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.24/2.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/2.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.24/2.97  tff('#skF_4', type, '#skF_4': $i).
% 8.24/2.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/2.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.24/2.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.24/2.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.24/2.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.24/2.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.24/2.97  
% 8.24/2.99  tff(f_130, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 8.24/2.99  tff(f_78, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.24/2.99  tff(f_109, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 8.24/2.99  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.24/2.99  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.24/2.99  tff(f_72, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.24/2.99  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.24/2.99  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.24/2.99  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.24/2.99  tff(f_76, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.24/2.99  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.24/2.99  tff(f_74, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 8.24/2.99  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.24/2.99  tff(f_98, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.24/2.99  tff(f_103, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.24/2.99  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.24/2.99  tff(f_62, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 8.24/2.99  tff(f_82, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.24/2.99  tff(f_80, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.24/2.99  tff(c_70, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.24/2.99  tff(c_114, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_70])).
% 8.24/2.99  tff(c_68, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.24/2.99  tff(c_102, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_68])).
% 8.24/2.99  tff(c_74, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.24/2.99  tff(c_119, plain, (![A_75, B_76]: (r1_tarski(A_75, k2_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.24/2.99  tff(c_122, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_119])).
% 8.24/2.99  tff(c_1403, plain, (![B_169, A_170]: (k1_tarski(B_169)=A_170 | k1_xboole_0=A_170 | ~r1_tarski(A_170, k1_tarski(B_169)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.24/2.99  tff(c_1430, plain, (k1_tarski('#skF_4')='#skF_5' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_122, c_1403])).
% 8.24/2.99  tff(c_1449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_102, c_1430])).
% 8.24/2.99  tff(c_1450, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_70])).
% 8.24/2.99  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.24/2.99  tff(c_2457, plain, (![A_252, B_253]: (r2_hidden('#skF_2'(A_252, B_253), A_252) | r1_tarski(A_252, B_253))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.24/2.99  tff(c_12, plain, (![A_9, B_10]: (~r2_hidden('#skF_2'(A_9, B_10), B_10) | r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.24/2.99  tff(c_2468, plain, (![A_254]: (r1_tarski(A_254, A_254))), inference(resolution, [status(thm)], [c_2457, c_12])).
% 8.24/2.99  tff(c_30, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.24/2.99  tff(c_2480, plain, (![A_254]: (k3_xboole_0(A_254, A_254)=A_254)), inference(resolution, [status(thm)], [c_2468, c_30])).
% 8.24/2.99  tff(c_1451, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_70])).
% 8.24/2.99  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.24/2.99  tff(c_1657, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_18])).
% 8.24/2.99  tff(c_2666, plain, (![A_261, B_262, C_263]: (~r1_xboole_0(A_261, B_262) | ~r2_hidden(C_263, k3_xboole_0(A_261, B_262)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.24/2.99  tff(c_2891, plain, (![A_281, C_282]: (~r1_xboole_0(A_281, A_281) | ~r2_hidden(C_282, A_281))), inference(superposition, [status(thm), theory('equality')], [c_2480, c_2666])).
% 8.24/2.99  tff(c_2897, plain, (![C_282, B_15]: (~r2_hidden(C_282, B_15) | k3_xboole_0(B_15, B_15)!='#skF_5')), inference(resolution, [status(thm)], [c_1657, c_2891])).
% 8.24/2.99  tff(c_2903, plain, (![C_283, B_284]: (~r2_hidden(C_283, B_284) | B_284!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2480, c_2897])).
% 8.24/2.99  tff(c_2971, plain, (![A_287]: (A_287!='#skF_5' | v1_xboole_0(A_287))), inference(resolution, [status(thm)], [c_8, c_2903])).
% 8.24/2.99  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.24/2.99  tff(c_2695, plain, (![A_264, B_265]: (~v1_xboole_0(A_264) | r1_tarski(A_264, B_265))), inference(resolution, [status(thm)], [c_2457, c_6])).
% 8.24/2.99  tff(c_28, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.24/2.99  tff(c_2706, plain, (![A_264, B_265]: (k2_xboole_0(A_264, B_265)=B_265 | ~v1_xboole_0(A_264))), inference(resolution, [status(thm)], [c_2695, c_28])).
% 8.24/2.99  tff(c_3175, plain, (![B_265]: (k2_xboole_0('#skF_5', B_265)=B_265)), inference(resolution, [status(thm)], [c_2971, c_2706])).
% 8.24/2.99  tff(c_3177, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3175, c_74])).
% 8.24/2.99  tff(c_3179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1450, c_3177])).
% 8.24/2.99  tff(c_3180, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_68])).
% 8.24/2.99  tff(c_3181, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_68])).
% 8.24/2.99  tff(c_72, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.24/2.99  tff(c_3254, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3181, c_3181, c_72])).
% 8.24/2.99  tff(c_3210, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3181, c_74])).
% 8.24/2.99  tff(c_34, plain, (![A_32]: (k5_xboole_0(A_32, k1_xboole_0)=A_32)), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.24/2.99  tff(c_14, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), A_9) | r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.24/2.99  tff(c_4464, plain, (![A_387, B_388]: (~r2_hidden('#skF_2'(A_387, B_388), B_388) | r1_tarski(A_387, B_388))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.24/2.99  tff(c_4472, plain, (![A_389]: (r1_tarski(A_389, A_389))), inference(resolution, [status(thm)], [c_14, c_4464])).
% 8.24/2.99  tff(c_4491, plain, (![A_389]: (k3_xboole_0(A_389, A_389)=A_389)), inference(resolution, [status(thm)], [c_4472, c_30])).
% 8.24/2.99  tff(c_4673, plain, (![A_394, B_395, C_396]: (~r1_xboole_0(A_394, B_395) | ~r2_hidden(C_396, k3_xboole_0(A_394, B_395)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.24/2.99  tff(c_6103, plain, (![A_447, C_448]: (~r1_xboole_0(A_447, A_447) | ~r2_hidden(C_448, A_447))), inference(superposition, [status(thm), theory('equality')], [c_4491, c_4673])).
% 8.24/2.99  tff(c_6109, plain, (![C_448, B_15]: (~r2_hidden(C_448, B_15) | k3_xboole_0(B_15, B_15)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_6103])).
% 8.24/2.99  tff(c_6128, plain, (![C_449, B_450]: (~r2_hidden(C_449, B_450) | k1_xboole_0!=B_450)), inference(demodulation, [status(thm), theory('equality')], [c_4491, c_6109])).
% 8.24/2.99  tff(c_6166, plain, (![A_452]: (k1_xboole_0!=A_452 | v1_xboole_0(A_452))), inference(resolution, [status(thm)], [c_8, c_6128])).
% 8.24/2.99  tff(c_4318, plain, (![A_376, B_377]: (r2_hidden('#skF_2'(A_376, B_377), A_376) | r1_tarski(A_376, B_377))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.24/2.99  tff(c_4323, plain, (![A_378, B_379]: (~v1_xboole_0(A_378) | r1_tarski(A_378, B_379))), inference(resolution, [status(thm)], [c_4318, c_6])).
% 8.24/2.99  tff(c_4339, plain, (![A_378, B_379]: (k2_xboole_0(A_378, B_379)=B_379 | ~v1_xboole_0(A_378))), inference(resolution, [status(thm)], [c_4323, c_28])).
% 8.24/2.99  tff(c_6191, plain, (![A_452, B_379]: (k2_xboole_0(A_452, B_379)=B_379 | k1_xboole_0!=A_452)), inference(resolution, [status(thm)], [c_6166, c_4339])).
% 8.24/2.99  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.24/2.99  tff(c_3632, plain, (![A_345, B_346, C_347]: (r1_tarski(k3_xboole_0(A_345, B_346), k2_xboole_0(A_345, C_347)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.24/2.99  tff(c_7459, plain, (![B_500, A_501, C_502]: (r1_tarski(k3_xboole_0(B_500, A_501), k2_xboole_0(A_501, C_502)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3632])).
% 8.24/2.99  tff(c_7472, plain, (![B_500, A_452, B_379]: (r1_tarski(k3_xboole_0(B_500, A_452), B_379) | k1_xboole_0!=A_452)), inference(superposition, [status(thm), theory('equality')], [c_6191, c_7459])).
% 8.24/2.99  tff(c_5328, plain, (![C_419, B_420, A_421]: (r2_hidden(C_419, B_420) | ~r2_hidden(C_419, A_421) | ~r1_tarski(A_421, B_420))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.24/2.99  tff(c_12689, plain, (![A_650, B_651]: (r2_hidden('#skF_1'(A_650), B_651) | ~r1_tarski(A_650, B_651) | v1_xboole_0(A_650))), inference(resolution, [status(thm)], [c_8, c_5328])).
% 8.24/2.99  tff(c_64, plain, (![B_65]: (r1_tarski(k1_xboole_0, k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.24/2.99  tff(c_3184, plain, (r1_tarski(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3181, c_64])).
% 8.24/2.99  tff(c_3357, plain, (![A_313, B_314]: (k3_xboole_0(A_313, B_314)=A_313 | ~r1_tarski(A_313, B_314))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.24/2.99  tff(c_3376, plain, (k3_xboole_0(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_3184, c_3357])).
% 8.24/2.99  tff(c_3385, plain, (k3_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3376, c_2])).
% 8.24/2.99  tff(c_4703, plain, (![C_396]: (~r1_xboole_0(k1_xboole_0, '#skF_5') | ~r2_hidden(C_396, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3376, c_4673])).
% 8.24/2.99  tff(c_4931, plain, (~r1_xboole_0(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_4703])).
% 8.24/2.99  tff(c_4934, plain, (k3_xboole_0(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_4931])).
% 8.24/2.99  tff(c_4938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3385, c_2, c_4934])).
% 8.24/2.99  tff(c_4939, plain, (![C_396]: (~r2_hidden(C_396, k1_xboole_0))), inference(splitRight, [status(thm)], [c_4703])).
% 8.24/2.99  tff(c_12725, plain, (![A_652]: (~r1_tarski(A_652, k1_xboole_0) | v1_xboole_0(A_652))), inference(resolution, [status(thm)], [c_12689, c_4939])).
% 8.24/2.99  tff(c_13056, plain, (![B_659, A_660]: (v1_xboole_0(k3_xboole_0(B_659, A_660)) | k1_xboole_0!=A_660)), inference(resolution, [status(thm)], [c_7472, c_12725])).
% 8.24/2.99  tff(c_6197, plain, (![A_453, B_454]: (r2_hidden('#skF_3'(A_453, B_454), k3_xboole_0(A_453, B_454)) | r1_xboole_0(A_453, B_454))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.24/2.99  tff(c_7883, plain, (![A_510, B_511]: (~v1_xboole_0(k3_xboole_0(A_510, B_511)) | r1_xboole_0(A_510, B_511))), inference(resolution, [status(thm)], [c_6197, c_6])).
% 8.24/2.99  tff(c_7928, plain, (![A_512]: (~v1_xboole_0(A_512) | r1_xboole_0(A_512, A_512))), inference(superposition, [status(thm), theory('equality')], [c_4491, c_7883])).
% 8.24/2.99  tff(c_16, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.24/2.99  tff(c_7941, plain, (![A_512]: (k3_xboole_0(A_512, A_512)=k1_xboole_0 | ~v1_xboole_0(A_512))), inference(resolution, [status(thm)], [c_7928, c_16])).
% 8.24/2.99  tff(c_7947, plain, (![A_512]: (k1_xboole_0=A_512 | ~v1_xboole_0(A_512))), inference(demodulation, [status(thm), theory('equality')], [c_4491, c_7941])).
% 8.24/2.99  tff(c_13461, plain, (![B_667, A_668]: (k3_xboole_0(B_667, A_668)=k1_xboole_0 | k1_xboole_0!=A_668)), inference(resolution, [status(thm)], [c_13056, c_7947])).
% 8.24/2.99  tff(c_26, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.24/2.99  tff(c_13623, plain, (![B_667, A_668]: (k5_xboole_0(B_667, k1_xboole_0)=k4_xboole_0(B_667, A_668) | k1_xboole_0!=A_668)), inference(superposition, [status(thm), theory('equality')], [c_13461, c_26])).
% 8.24/2.99  tff(c_13815, plain, (![B_667]: (k4_xboole_0(B_667, k1_xboole_0)=B_667)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_13623])).
% 8.24/2.99  tff(c_62, plain, (![B_65]: (r1_tarski(k1_tarski(B_65), k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.24/2.99  tff(c_3452, plain, (![A_326, B_327]: (r2_hidden(A_326, B_327) | ~r1_tarski(k1_tarski(A_326), B_327))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.24/2.99  tff(c_3469, plain, (![B_328]: (r2_hidden(B_328, k1_tarski(B_328)))), inference(resolution, [status(thm)], [c_62, c_3452])).
% 8.24/2.99  tff(c_3483, plain, (![B_329]: (~v1_xboole_0(k1_tarski(B_329)))), inference(resolution, [status(thm)], [c_3469, c_6])).
% 8.24/2.99  tff(c_3485, plain, (~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3181, c_3483])).
% 8.24/2.99  tff(c_36, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.24/2.99  tff(c_3373, plain, (![A_33, B_34]: (k3_xboole_0(A_33, k2_xboole_0(A_33, B_34))=A_33)), inference(resolution, [status(thm)], [c_36, c_3357])).
% 8.24/2.99  tff(c_7307, plain, (![A_496, B_497]: (~r1_xboole_0(A_496, B_497) | v1_xboole_0(k3_xboole_0(A_496, B_497)))), inference(resolution, [status(thm)], [c_8, c_4673])).
% 8.24/2.99  tff(c_8129, plain, (![A_524, B_525]: (~r1_xboole_0(A_524, k2_xboole_0(A_524, B_525)) | v1_xboole_0(A_524))), inference(superposition, [status(thm), theory('equality')], [c_3373, c_7307])).
% 8.24/2.99  tff(c_8171, plain, (~r1_xboole_0('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3210, c_8129])).
% 8.24/2.99  tff(c_8186, plain, (~r1_xboole_0('#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_3485, c_8171])).
% 8.24/2.99  tff(c_3436, plain, (![A_320, B_321]: (r1_xboole_0(k1_tarski(A_320), B_321) | r2_hidden(A_320, B_321))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.24/2.99  tff(c_3441, plain, (![B_323]: (r1_xboole_0('#skF_5', B_323) | r2_hidden('#skF_4', B_323))), inference(superposition, [status(thm), theory('equality')], [c_3181, c_3436])).
% 8.24/2.99  tff(c_3428, plain, (![A_318, B_319]: (r1_tarski(k1_tarski(A_318), B_319) | ~r2_hidden(A_318, B_319))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.24/2.99  tff(c_3434, plain, (![B_319]: (r1_tarski('#skF_5', B_319) | ~r2_hidden('#skF_4', B_319))), inference(superposition, [status(thm), theory('equality')], [c_3181, c_3428])).
% 8.24/2.99  tff(c_3448, plain, (![B_323]: (r1_tarski('#skF_5', B_323) | r1_xboole_0('#skF_5', B_323))), inference(resolution, [status(thm)], [c_3441, c_3434])).
% 8.24/2.99  tff(c_4717, plain, (![A_394, B_395]: (~r1_xboole_0(A_394, B_395) | v1_xboole_0(k3_xboole_0(A_394, B_395)))), inference(resolution, [status(thm)], [c_8, c_4673])).
% 8.24/2.99  tff(c_8242, plain, (![A_528, B_529]: (~v1_xboole_0(k3_xboole_0(A_528, B_529)) | r1_xboole_0(B_529, A_528))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7883])).
% 8.24/2.99  tff(c_8377, plain, (![B_532, A_533]: (r1_xboole_0(B_532, A_533) | ~r1_xboole_0(A_533, B_532))), inference(resolution, [status(thm)], [c_4717, c_8242])).
% 8.24/2.99  tff(c_8447, plain, (![B_535]: (r1_xboole_0(B_535, '#skF_5') | r1_tarski('#skF_5', B_535))), inference(resolution, [status(thm)], [c_3448, c_8377])).
% 8.24/2.99  tff(c_9696, plain, (![B_580]: (k3_xboole_0(B_580, '#skF_5')=k1_xboole_0 | r1_tarski('#skF_5', B_580))), inference(resolution, [status(thm)], [c_8447, c_16])).
% 8.24/2.99  tff(c_3439, plain, (![B_321]: (r1_xboole_0('#skF_5', B_321) | r2_hidden('#skF_4', B_321))), inference(superposition, [status(thm), theory('equality')], [c_3181, c_3436])).
% 8.24/2.99  tff(c_5351, plain, (![B_420, B_321]: (r2_hidden('#skF_4', B_420) | ~r1_tarski(B_321, B_420) | r1_xboole_0('#skF_5', B_321))), inference(resolution, [status(thm)], [c_3439, c_5328])).
% 8.24/2.99  tff(c_9709, plain, (![B_580]: (r2_hidden('#skF_4', B_580) | r1_xboole_0('#skF_5', '#skF_5') | k3_xboole_0(B_580, '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_9696, c_5351])).
% 8.24/2.99  tff(c_9743, plain, (![B_580]: (r2_hidden('#skF_4', B_580) | k3_xboole_0(B_580, '#skF_5')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_8186, c_9709])).
% 8.24/2.99  tff(c_56, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.24/2.99  tff(c_3495, plain, (![A_330, B_331]: (k2_xboole_0(A_330, B_331)=B_331 | ~r1_tarski(A_330, B_331))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.24/2.99  tff(c_11023, plain, (![A_620, B_621]: (k2_xboole_0(k1_tarski(A_620), B_621)=B_621 | ~r2_hidden(A_620, B_621))), inference(resolution, [status(thm)], [c_56, c_3495])).
% 8.24/2.99  tff(c_11137, plain, (![B_622]: (k2_xboole_0('#skF_5', B_622)=B_622 | ~r2_hidden('#skF_4', B_622))), inference(superposition, [status(thm), theory('equality')], [c_3181, c_11023])).
% 8.24/2.99  tff(c_15525, plain, (![B_707]: (k2_xboole_0('#skF_5', B_707)=B_707 | k3_xboole_0(B_707, '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_9743, c_11137])).
% 8.24/2.99  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.24/2.99  tff(c_5931, plain, (![A_442, B_443]: (k4_xboole_0(k2_xboole_0(A_442, B_443), k3_xboole_0(A_442, B_443))=k5_xboole_0(A_442, B_443))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.24/2.99  tff(c_5973, plain, (k4_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3210, c_5931])).
% 8.24/2.99  tff(c_5984, plain, (k4_xboole_0('#skF_5', k3_xboole_0('#skF_6', '#skF_5'))=k5_xboole_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_5973])).
% 8.24/2.99  tff(c_15662, plain, (k5_xboole_0('#skF_6', '#skF_5')=k4_xboole_0('#skF_5', k1_xboole_0) | k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_15525, c_5984])).
% 8.24/2.99  tff(c_15788, plain, (k5_xboole_0('#skF_6', '#skF_5')='#skF_5' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3210, c_13815, c_15662])).
% 8.24/2.99  tff(c_15789, plain, (k5_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3254, c_15788])).
% 8.24/2.99  tff(c_3260, plain, (![B_310, A_311]: (k5_xboole_0(B_310, A_311)=k5_xboole_0(A_311, B_310))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.24/2.99  tff(c_3276, plain, (![A_311]: (k5_xboole_0(k1_xboole_0, A_311)=A_311)), inference(superposition, [status(thm), theory('equality')], [c_3260, c_34])).
% 8.24/2.99  tff(c_40, plain, (![A_38]: (k5_xboole_0(A_38, A_38)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.24/2.99  tff(c_5421, plain, (![A_426, B_427, C_428]: (k5_xboole_0(k5_xboole_0(A_426, B_427), C_428)=k5_xboole_0(A_426, k5_xboole_0(B_427, C_428)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.24/2.99  tff(c_5485, plain, (![A_38, C_428]: (k5_xboole_0(A_38, k5_xboole_0(A_38, C_428))=k5_xboole_0(k1_xboole_0, C_428))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5421])).
% 8.24/2.99  tff(c_5498, plain, (![A_38, C_428]: (k5_xboole_0(A_38, k5_xboole_0(A_38, C_428))=C_428)), inference(demodulation, [status(thm), theory('equality')], [c_3276, c_5485])).
% 8.24/2.99  tff(c_5499, plain, (![A_429, C_430]: (k5_xboole_0(A_429, k5_xboole_0(A_429, C_430))=C_430)), inference(demodulation, [status(thm), theory('equality')], [c_3276, c_5485])).
% 8.24/2.99  tff(c_5564, plain, (![A_431, B_432]: (k5_xboole_0(A_431, k5_xboole_0(B_432, A_431))=B_432)), inference(superposition, [status(thm), theory('equality')], [c_4, c_5499])).
% 8.24/2.99  tff(c_5597, plain, (![A_38, C_428]: (k5_xboole_0(k5_xboole_0(A_38, C_428), C_428)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_5498, c_5564])).
% 8.24/2.99  tff(c_15825, plain, (k5_xboole_0('#skF_5', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_15789, c_5597])).
% 8.24/2.99  tff(c_15911, plain, (k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_15825, c_40])).
% 8.24/2.99  tff(c_15925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3180, c_15911])).
% 8.24/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.99  
% 8.24/2.99  Inference rules
% 8.24/2.99  ----------------------
% 8.24/2.99  #Ref     : 1
% 8.24/2.99  #Sup     : 3844
% 8.24/2.99  #Fact    : 0
% 8.24/2.99  #Define  : 0
% 8.24/2.99  #Split   : 6
% 8.24/2.99  #Chain   : 0
% 8.24/2.99  #Close   : 0
% 8.24/2.99  
% 8.24/2.99  Ordering : KBO
% 8.24/2.99  
% 8.24/2.99  Simplification rules
% 8.24/2.99  ----------------------
% 8.24/2.99  #Subsume      : 1018
% 8.24/2.99  #Demod        : 1770
% 8.24/2.99  #Tautology    : 1831
% 8.24/2.99  #SimpNegUnit  : 176
% 8.24/2.99  #BackRed      : 35
% 8.24/2.99  
% 8.24/2.99  #Partial instantiations: 0
% 8.24/2.99  #Strategies tried      : 1
% 8.24/2.99  
% 8.24/2.99  Timing (in seconds)
% 8.24/2.99  ----------------------
% 8.54/2.99  Preprocessing        : 0.35
% 8.54/2.99  Parsing              : 0.19
% 8.54/2.99  CNF conversion       : 0.02
% 8.54/2.99  Main loop            : 1.86
% 8.54/2.99  Inferencing          : 0.55
% 8.54/2.99  Reduction            : 0.77
% 8.54/2.99  Demodulation         : 0.59
% 8.54/2.99  BG Simplification    : 0.06
% 8.54/2.99  Subsumption          : 0.34
% 8.54/2.99  Abstraction          : 0.07
% 8.54/2.99  MUC search           : 0.00
% 8.54/2.99  Cooper               : 0.00
% 8.54/2.99  Total                : 2.26
% 8.54/2.99  Index Insertion      : 0.00
% 8.54/2.99  Index Deletion       : 0.00
% 8.54/2.99  Index Matching       : 0.00
% 8.54/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
