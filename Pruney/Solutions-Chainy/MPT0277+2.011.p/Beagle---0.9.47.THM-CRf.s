%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:21 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :  351 (1415 expanded)
%              Number of leaves         :   40 ( 460 expanded)
%              Depth                    :   13
%              Number of atoms          :  421 (2385 expanded)
%              Number of equality atoms :  349 (2205 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_32,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12179,plain,(
    ! [A_531,B_532] : k5_xboole_0(k5_xboole_0(A_531,B_532),k2_xboole_0(A_531,B_532)) = k3_xboole_0(A_531,B_532) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12212,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_26,A_26)) = k3_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_12179])).

tff(c_12218,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_12212])).

tff(c_12334,plain,(
    ! [A_537,B_538,C_539] : k5_xboole_0(k5_xboole_0(A_537,B_538),C_539) = k5_xboole_0(A_537,k5_xboole_0(B_538,C_539)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12402,plain,(
    ! [A_26,C_539] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_539)) = k5_xboole_0(k1_xboole_0,C_539) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_12334])).

tff(c_12415,plain,(
    ! [A_26,C_539] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_539)) = C_539 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12218,c_12402])).

tff(c_22,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12484,plain,(
    ! [A_542,B_543] : k5_xboole_0(A_542,k5_xboole_0(B_543,k5_xboole_0(A_542,B_543))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_12334])).

tff(c_12492,plain,(
    ! [B_543,A_542] : k5_xboole_0(B_543,k5_xboole_0(A_542,B_543)) = k5_xboole_0(A_542,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12484,c_12415])).

tff(c_12585,plain,(
    ! [B_544,A_545] : k5_xboole_0(B_544,k5_xboole_0(A_545,B_544)) = A_545 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12492])).

tff(c_12621,plain,(
    ! [A_26,C_539] : k5_xboole_0(k5_xboole_0(A_26,C_539),C_539) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_12415,c_12585])).

tff(c_11934,plain,(
    ! [A_502,B_503] : k5_xboole_0(A_502,k3_xboole_0(A_502,B_503)) = k4_xboole_0(A_502,B_503) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_11943,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_11934])).

tff(c_11946,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11943])).

tff(c_9672,plain,(
    ! [A_417,B_418] : k5_xboole_0(k5_xboole_0(A_417,B_418),k2_xboole_0(A_417,B_418)) = k3_xboole_0(A_417,B_418) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9739,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_26,A_26)) = k3_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_9672])).

tff(c_9745,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_9739])).

tff(c_9433,plain,(
    ! [A_409,B_410,C_411] : k5_xboole_0(k5_xboole_0(A_409,B_410),C_411) = k5_xboole_0(A_409,k5_xboole_0(B_410,C_411)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9474,plain,(
    ! [A_26,C_411] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_411)) = k5_xboole_0(k1_xboole_0,C_411) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_9433])).

tff(c_9747,plain,(
    ! [A_26,C_411] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_411)) = C_411 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9745,c_9474])).

tff(c_9451,plain,(
    ! [A_409,B_410] : k5_xboole_0(A_409,k5_xboole_0(B_410,k5_xboole_0(A_409,B_410))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9433,c_32])).

tff(c_9852,plain,(
    ! [A_422,C_423] : k5_xboole_0(A_422,k5_xboole_0(A_422,C_423)) = C_423 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9745,c_9474])).

tff(c_9902,plain,(
    ! [B_410,A_409] : k5_xboole_0(B_410,k5_xboole_0(A_409,B_410)) = k5_xboole_0(A_409,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9451,c_9852])).

tff(c_9953,plain,(
    ! [B_428,A_429] : k5_xboole_0(B_428,k5_xboole_0(A_429,B_428)) = A_429 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_9902])).

tff(c_9989,plain,(
    ! [A_26,C_411] : k5_xboole_0(k5_xboole_0(A_26,C_411),C_411) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_9747,c_9953])).

tff(c_237,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_246,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_237])).

tff(c_249,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_246])).

tff(c_7089,plain,(
    ! [A_317,B_318] : k5_xboole_0(k5_xboole_0(A_317,B_318),k2_xboole_0(A_317,B_318)) = k3_xboole_0(A_317,B_318) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7147,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_26,A_26)) = k3_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7089])).

tff(c_7153,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_7147])).

tff(c_7037,plain,(
    ! [A_314,B_315,C_316] : k5_xboole_0(k5_xboole_0(A_314,B_315),C_316) = k5_xboole_0(A_314,k5_xboole_0(B_315,C_316)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7078,plain,(
    ! [A_26,C_316] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_316)) = k5_xboole_0(k1_xboole_0,C_316) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7037])).

tff(c_7240,plain,(
    ! [A_26,C_316] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_316)) = C_316 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_7078])).

tff(c_7315,plain,(
    ! [A_328,B_329] : k5_xboole_0(A_328,k5_xboole_0(B_329,k5_xboole_0(A_328,B_329))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7037])).

tff(c_7323,plain,(
    ! [B_329,A_328] : k5_xboole_0(B_329,k5_xboole_0(A_328,B_329)) = k5_xboole_0(A_328,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7315,c_7240])).

tff(c_7413,plain,(
    ! [B_330,A_331] : k5_xboole_0(B_330,k5_xboole_0(A_331,B_330)) = A_331 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7323])).

tff(c_7449,plain,(
    ! [A_26,C_316] : k5_xboole_0(k5_xboole_0(A_26,C_316),C_316) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_7240,c_7413])).

tff(c_70,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_140,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_66,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_205,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_tarski('#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_258,plain,(
    k1_tarski('#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_369,plain,(
    k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_468,plain,(
    ! [A_106,B_107,C_108] : k5_xboole_0(k5_xboole_0(A_106,B_107),C_108) = k5_xboole_0(A_106,k5_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_622,plain,(
    ! [A_112,C_113] : k5_xboole_0(A_112,k5_xboole_0(A_112,C_113)) = k5_xboole_0(k1_xboole_0,C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_468])).

tff(c_690,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,A_26) = k5_xboole_0(A_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_622])).

tff(c_706,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_690])).

tff(c_509,plain,(
    ! [A_26,C_108] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_108)) = k5_xboole_0(k1_xboole_0,C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_468])).

tff(c_708,plain,(
    ! [A_26,C_108] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_108)) = C_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_509])).

tff(c_486,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k5_xboole_0(B_107,k5_xboole_0(A_106,B_107))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_32])).

tff(c_771,plain,(
    ! [A_115,C_116] : k5_xboole_0(A_115,k5_xboole_0(A_115,C_116)) = C_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_509])).

tff(c_815,plain,(
    ! [B_107,A_106] : k5_xboole_0(B_107,k5_xboole_0(A_106,B_107)) = k5_xboole_0(A_106,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_771])).

tff(c_987,plain,(
    ! [B_122,A_123] : k5_xboole_0(B_122,k5_xboole_0(A_123,B_122)) = A_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_815])).

tff(c_1026,plain,(
    ! [A_26,C_108] : k5_xboole_0(k5_xboole_0(A_26,C_108),C_108) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_987])).

tff(c_76,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1862,plain,(
    k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_873,plain,(
    ! [A_118,B_119] : k5_xboole_0(k5_xboole_0(A_118,B_119),k2_xboole_0(A_118,B_119)) = k3_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] : k5_xboole_0(k5_xboole_0(A_23,B_24),C_25) = k5_xboole_0(A_23,k5_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2218,plain,(
    ! [A_159,B_160] : k5_xboole_0(A_159,k5_xboole_0(B_160,k2_xboole_0(A_159,B_160))) = k3_xboole_0(A_159,B_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_30])).

tff(c_2236,plain,(
    ! [B_160,A_159] : k5_xboole_0(B_160,k2_xboole_0(A_159,B_160)) = k5_xboole_0(A_159,k3_xboole_0(A_159,B_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2218,c_708])).

tff(c_2542,plain,(
    ! [B_173,A_174] : k5_xboole_0(B_173,k2_xboole_0(A_174,B_173)) = k4_xboole_0(A_174,B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2236])).

tff(c_2736,plain,(
    ! [B_177,A_178] : k5_xboole_0(B_177,k4_xboole_0(A_178,B_177)) = k2_xboole_0(A_178,B_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_2542,c_708])).

tff(c_2784,plain,(
    k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) = k2_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_2736])).

tff(c_2815,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2784])).

tff(c_28,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2880,plain,(
    r1_tarski('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2815,c_28])).

tff(c_46,plain,(
    ! [B_45,C_46,A_44] :
      ( k2_tarski(B_45,C_46) = A_44
      | k1_tarski(C_46) = A_44
      | k1_tarski(B_45) = A_44
      | k1_xboole_0 = A_44
      | ~ r1_tarski(A_44,k2_tarski(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2892,plain,
    ( k2_tarski('#skF_7','#skF_8') = '#skF_6'
    | k1_tarski('#skF_8') = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2880,c_46])).

tff(c_2899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_205,c_258,c_369,c_2892])).

tff(c_2900,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2970,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2900])).

tff(c_74,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_707,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_2971,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2970,c_707])).

tff(c_2974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_2971])).

tff(c_2975,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2900])).

tff(c_2977,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2975])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_328,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,B_95)
      | ~ r2_hidden(C_96,A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_332,plain,(
    ! [C_97] : ~ r2_hidden(C_97,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_328])).

tff(c_372,plain,(
    ! [B_100] : r1_tarski(k1_xboole_0,B_100) ),
    inference(resolution,[status(thm)],[c_6,c_332])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_376,plain,(
    ! [B_100] : k2_xboole_0(k1_xboole_0,B_100) = B_100 ),
    inference(resolution,[status(thm)],[c_372,c_20])).

tff(c_903,plain,(
    ! [A_26] : k5_xboole_0(A_26,k2_xboole_0(k1_xboole_0,A_26)) = k3_xboole_0(k1_xboole_0,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_873])).

tff(c_940,plain,(
    ! [A_26] : k3_xboole_0(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_376,c_903])).

tff(c_711,plain,(
    ! [A_114] : k5_xboole_0(k1_xboole_0,A_114) = A_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_690])).

tff(c_732,plain,(
    ! [B_16] : k4_xboole_0(k1_xboole_0,B_16) = k3_xboole_0(k1_xboole_0,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_18])).

tff(c_945,plain,(
    ! [B_16] : k4_xboole_0(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_732])).

tff(c_2984,plain,(
    ! [B_16] : k4_xboole_0('#skF_3',B_16) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2977,c_2977,c_945])).

tff(c_2986,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2977,c_707])).

tff(c_3303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2984,c_2986])).

tff(c_3304,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2975])).

tff(c_3306,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3304])).

tff(c_50,plain,(
    ! [C_46,B_45] : r1_tarski(k1_tarski(C_46),k2_tarski(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_156,plain,(
    ! [A_65,B_66] :
      ( k2_xboole_0(A_65,B_66) = B_66
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_175,plain,(
    ! [C_46,B_45] : k2_xboole_0(k1_tarski(C_46),k2_tarski(B_45,C_46)) = k2_tarski(B_45,C_46) ),
    inference(resolution,[status(thm)],[c_50,c_156])).

tff(c_3466,plain,(
    ! [B_204] : k2_xboole_0('#skF_3',k2_tarski(B_204,'#skF_5')) = k2_tarski(B_204,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3306,c_175])).

tff(c_34,plain,(
    ! [A_27,B_28] : k5_xboole_0(k5_xboole_0(A_27,B_28),k2_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3476,plain,(
    ! [B_204] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski(B_204,'#skF_5')),k2_tarski(B_204,'#skF_5')) = k3_xboole_0('#skF_3',k2_tarski(B_204,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3466,c_34])).

tff(c_3503,plain,(
    ! [B_205] : k3_xboole_0('#skF_3',k2_tarski(B_205,'#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_3476])).

tff(c_3520,plain,(
    ! [B_205] : k4_xboole_0('#skF_3',k2_tarski(B_205,'#skF_5')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3503,c_18])).

tff(c_3533,plain,(
    ! [B_205] : k4_xboole_0('#skF_3',k2_tarski(B_205,'#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3520])).

tff(c_3539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3533,c_707])).

tff(c_3540,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3304])).

tff(c_52,plain,(
    ! [B_45,C_46] : r1_tarski(k1_tarski(B_45),k2_tarski(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_176,plain,(
    ! [B_45,C_46] : k2_xboole_0(k1_tarski(B_45),k2_tarski(B_45,C_46)) = k2_tarski(B_45,C_46) ),
    inference(resolution,[status(thm)],[c_52,c_156])).

tff(c_3624,plain,(
    ! [C_211] : k2_xboole_0('#skF_3',k2_tarski('#skF_4',C_211)) = k2_tarski('#skF_4',C_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_3540,c_176])).

tff(c_3630,plain,(
    ! [C_211] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski('#skF_4',C_211)),k2_tarski('#skF_4',C_211)) = k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3624,c_34])).

tff(c_3686,plain,(
    ! [C_213] : k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_213)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_3630])).

tff(c_3700,plain,(
    ! [C_213] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_213)) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3686,c_18])).

tff(c_3709,plain,(
    ! [C_213] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_213)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3700])).

tff(c_3748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3709,c_707])).

tff(c_3749,plain,(
    k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4199,plain,(
    ! [A_225,B_226] : k5_xboole_0(k5_xboole_0(A_225,B_226),k2_xboole_0(A_225,B_226)) = k3_xboole_0(A_225,B_226) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5300,plain,(
    ! [A_260,B_261] : k5_xboole_0(A_260,k5_xboole_0(B_261,k2_xboole_0(A_260,B_261))) = k3_xboole_0(A_260,B_261) ),
    inference(superposition,[status(thm),theory(equality)],[c_4199,c_30])).

tff(c_3751,plain,(
    ! [A_26,C_108] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_108)) = C_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_509])).

tff(c_5318,plain,(
    ! [B_261,A_260] : k5_xboole_0(B_261,k2_xboole_0(A_260,B_261)) = k5_xboole_0(A_260,k3_xboole_0(A_260,B_261)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5300,c_3751])).

tff(c_5648,plain,(
    ! [B_279,A_280] : k5_xboole_0(B_279,k2_xboole_0(A_280,B_279)) = k4_xboole_0(A_280,B_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5318])).

tff(c_5725,plain,(
    ! [B_281,A_282] : k5_xboole_0(B_281,k4_xboole_0(A_282,B_281)) = k2_xboole_0(A_282,B_281) ),
    inference(superposition,[status(thm),theory(equality)],[c_5648,c_3751])).

tff(c_5786,plain,(
    k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) = k2_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3749,c_5725])).

tff(c_5810,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_5786])).

tff(c_6599,plain,(
    r1_tarski('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5810,c_28])).

tff(c_6830,plain,
    ( k2_tarski('#skF_7','#skF_8') = '#skF_6'
    | k1_tarski('#skF_8') = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6599,c_46])).

tff(c_6837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_205,c_258,c_369,c_6830])).

tff(c_6839,plain,(
    k2_tarski('#skF_7','#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_60,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_7850,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6839,c_60])).

tff(c_7851,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7850])).

tff(c_6842,plain,(
    ! [B_308] : r1_tarski(k1_xboole_0,B_308) ),
    inference(resolution,[status(thm)],[c_6,c_332])).

tff(c_6846,plain,(
    ! [B_308] : k2_xboole_0(k1_xboole_0,B_308) = B_308 ),
    inference(resolution,[status(thm)],[c_6842,c_20])).

tff(c_7155,plain,(
    ! [A_319] : k5_xboole_0(k1_xboole_0,A_319) = A_319 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_7147])).

tff(c_7161,plain,(
    ! [A_319] : k5_xboole_0(A_319,k2_xboole_0(k1_xboole_0,A_319)) = k3_xboole_0(k1_xboole_0,A_319) ),
    inference(superposition,[status(thm),theory(equality)],[c_7155,c_34])).

tff(c_7201,plain,(
    ! [A_320] : k3_xboole_0(k1_xboole_0,A_320) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6846,c_7161])).

tff(c_7206,plain,(
    ! [A_320] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_320) ),
    inference(superposition,[status(thm),theory(equality)],[c_7201,c_18])).

tff(c_7218,plain,(
    ! [A_320] : k4_xboole_0(k1_xboole_0,A_320) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7206])).

tff(c_7852,plain,(
    ! [A_320] : k4_xboole_0('#skF_3',A_320) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7851,c_7851,c_7218])).

tff(c_6838,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7855,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7851,c_6838])).

tff(c_8210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7852,c_7855])).

tff(c_8211,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7850])).

tff(c_8584,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8211])).

tff(c_8585,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8584,c_6838])).

tff(c_8588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_8585])).

tff(c_8589,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8211])).

tff(c_8591,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8589])).

tff(c_8774,plain,(
    ! [C_372] : k2_xboole_0('#skF_3',k2_tarski('#skF_4',C_372)) = k2_tarski('#skF_4',C_372) ),
    inference(superposition,[status(thm),theory(equality)],[c_8591,c_176])).

tff(c_8784,plain,(
    ! [C_372] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski('#skF_4',C_372)),k2_tarski('#skF_4',C_372)) = k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_372)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8774,c_34])).

tff(c_8841,plain,(
    ! [C_374] : k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_374)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7449,c_8784])).

tff(c_8855,plain,(
    ! [C_374] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_374)) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8841,c_18])).

tff(c_8867,plain,(
    ! [C_374] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_374)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8855])).

tff(c_8873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8867,c_6838])).

tff(c_8874,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8589])).

tff(c_9058,plain,(
    ! [B_383] : k2_xboole_0('#skF_3',k2_tarski(B_383,'#skF_5')) = k2_tarski(B_383,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8874,c_175])).

tff(c_9068,plain,(
    ! [B_383] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski(B_383,'#skF_5')),k2_tarski(B_383,'#skF_5')) = k3_xboole_0('#skF_3',k2_tarski(B_383,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9058,c_34])).

tff(c_9094,plain,(
    ! [B_384] : k3_xboole_0('#skF_3',k2_tarski(B_384,'#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7449,c_9068])).

tff(c_9108,plain,(
    ! [B_384] : k4_xboole_0('#skF_3',k2_tarski(B_384,'#skF_5')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9094,c_18])).

tff(c_9120,plain,(
    ! [B_384] : k4_xboole_0('#skF_3',k2_tarski(B_384,'#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9108])).

tff(c_9126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9120,c_6838])).

tff(c_9128,plain,(
    k1_tarski('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_64,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10109,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9128,c_64])).

tff(c_10110,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10109])).

tff(c_9186,plain,(
    ! [A_387,B_388,C_389] :
      ( ~ r1_xboole_0(A_387,B_388)
      | ~ r2_hidden(C_389,B_388)
      | ~ r2_hidden(C_389,A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9190,plain,(
    ! [C_390] : ~ r2_hidden(C_390,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_9186])).

tff(c_9230,plain,(
    ! [B_393] : r1_tarski(k1_xboole_0,B_393) ),
    inference(resolution,[status(thm)],[c_6,c_9190])).

tff(c_9234,plain,(
    ! [B_393] : k2_xboole_0(k1_xboole_0,B_393) = B_393 ),
    inference(resolution,[status(thm)],[c_9230,c_20])).

tff(c_9750,plain,(
    ! [A_419] : k5_xboole_0(k1_xboole_0,A_419) = A_419 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_9739])).

tff(c_9756,plain,(
    ! [A_419] : k5_xboole_0(A_419,k2_xboole_0(k1_xboole_0,A_419)) = k3_xboole_0(k1_xboole_0,A_419) ),
    inference(superposition,[status(thm),theory(equality)],[c_9750,c_34])).

tff(c_9816,plain,(
    ! [A_420] : k3_xboole_0(k1_xboole_0,A_420) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9234,c_9756])).

tff(c_9821,plain,(
    ! [A_420] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_420) ),
    inference(superposition,[status(thm),theory(equality)],[c_9816,c_18])).

tff(c_9833,plain,(
    ! [A_420] : k4_xboole_0(k1_xboole_0,A_420) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_9821])).

tff(c_10111,plain,(
    ! [A_420] : k4_xboole_0('#skF_3',A_420) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10110,c_10110,c_9833])).

tff(c_9127,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_10119,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10110,c_9127])).

tff(c_10418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10111,c_10119])).

tff(c_10419,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10109])).

tff(c_10693,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10419])).

tff(c_10694,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10693,c_9127])).

tff(c_10697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_10694])).

tff(c_10698,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10419])).

tff(c_10700,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10698])).

tff(c_11162,plain,(
    ! [C_469] : k2_xboole_0('#skF_3',k2_tarski('#skF_4',C_469)) = k2_tarski('#skF_4',C_469) ),
    inference(superposition,[status(thm),theory(equality)],[c_10700,c_176])).

tff(c_11172,plain,(
    ! [C_469] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski('#skF_4',C_469)),k2_tarski('#skF_4',C_469)) = k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_469)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11162,c_34])).

tff(c_11198,plain,(
    ! [C_470] : k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_470)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9989,c_11172])).

tff(c_11206,plain,(
    ! [C_470] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_470)) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11198,c_18])).

tff(c_11218,plain,(
    ! [C_470] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_470)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11206])).

tff(c_11440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11218,c_9127])).

tff(c_11441,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10698])).

tff(c_11808,plain,(
    ! [B_493] : k2_xboole_0('#skF_3',k2_tarski(B_493,'#skF_5')) = k2_tarski(B_493,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11441,c_175])).

tff(c_11814,plain,(
    ! [B_493] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski(B_493,'#skF_5')),k2_tarski(B_493,'#skF_5')) = k3_xboole_0('#skF_3',k2_tarski(B_493,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11808,c_34])).

tff(c_11834,plain,(
    ! [B_494] : k3_xboole_0('#skF_3',k2_tarski(B_494,'#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9989,c_11814])).

tff(c_11839,plain,(
    ! [B_494] : k4_xboole_0('#skF_3',k2_tarski(B_494,'#skF_5')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11834,c_18])).

tff(c_11847,plain,(
    ! [B_494] : k4_xboole_0('#skF_3',k2_tarski(B_494,'#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11839])).

tff(c_11852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11847,c_9127])).

tff(c_11854,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_68,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12666,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11854,c_68])).

tff(c_12667,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12666])).

tff(c_12090,plain,(
    ! [A_523,B_524,C_525] :
      ( ~ r1_xboole_0(A_523,B_524)
      | ~ r2_hidden(C_525,B_524)
      | ~ r2_hidden(C_525,A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12094,plain,(
    ! [C_526] : ~ r2_hidden(C_526,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_12090])).

tff(c_12124,plain,(
    ! [B_528] : r1_tarski(k1_xboole_0,B_528) ),
    inference(resolution,[status(thm)],[c_6,c_12094])).

tff(c_12128,plain,(
    ! [B_528] : k2_xboole_0(k1_xboole_0,B_528) = B_528 ),
    inference(resolution,[status(thm)],[c_12124,c_20])).

tff(c_12220,plain,(
    ! [A_533] : k5_xboole_0(k1_xboole_0,A_533) = A_533 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_12212])).

tff(c_12226,plain,(
    ! [A_533] : k5_xboole_0(A_533,k2_xboole_0(k1_xboole_0,A_533)) = k3_xboole_0(k1_xboole_0,A_533) ),
    inference(superposition,[status(thm),theory(equality)],[c_12220,c_34])).

tff(c_12262,plain,(
    ! [A_534] : k3_xboole_0(k1_xboole_0,A_534) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12128,c_12226])).

tff(c_12267,plain,(
    ! [A_534] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_534) ),
    inference(superposition,[status(thm),theory(equality)],[c_12262,c_18])).

tff(c_12279,plain,(
    ! [A_534] : k4_xboole_0(k1_xboole_0,A_534) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12267])).

tff(c_12669,plain,(
    ! [A_534] : k4_xboole_0('#skF_3',A_534) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12667,c_12667,c_12279])).

tff(c_11853,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12678,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12667,c_11853])).

tff(c_12971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12669,c_12678])).

tff(c_12972,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12666])).

tff(c_13330,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12972])).

tff(c_13331,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13330,c_11853])).

tff(c_13334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11946,c_13331])).

tff(c_13335,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12972])).

tff(c_13337,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_13335])).

tff(c_13367,plain,(
    ! [C_565] : r1_tarski('#skF_3',k2_tarski('#skF_4',C_565)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13337,c_52])).

tff(c_13608,plain,(
    ! [C_582] : k2_xboole_0('#skF_3',k2_tarski('#skF_4',C_582)) = k2_tarski('#skF_4',C_582) ),
    inference(resolution,[status(thm)],[c_13367,c_20])).

tff(c_13618,plain,(
    ! [C_582] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski('#skF_4',C_582)),k2_tarski('#skF_4',C_582)) = k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_582)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13608,c_34])).

tff(c_13644,plain,(
    ! [C_583] : k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_583)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12621,c_13618])).

tff(c_13652,plain,(
    ! [C_583] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_583)) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13644,c_18])).

tff(c_13664,plain,(
    ! [C_583] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_583)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_13652])).

tff(c_13687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13664,c_11853])).

tff(c_13688,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13335])).

tff(c_13707,plain,(
    ! [B_585] : r1_tarski('#skF_3',k2_tarski(B_585,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13688,c_50])).

tff(c_13891,plain,(
    ! [B_595] : k2_xboole_0('#skF_3',k2_tarski(B_595,'#skF_5')) = k2_tarski(B_595,'#skF_5') ),
    inference(resolution,[status(thm)],[c_13707,c_20])).

tff(c_13897,plain,(
    ! [B_595] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski(B_595,'#skF_5')),k2_tarski(B_595,'#skF_5')) = k3_xboole_0('#skF_3',k2_tarski(B_595,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13891,c_34])).

tff(c_13926,plain,(
    ! [B_601] : k3_xboole_0('#skF_3',k2_tarski(B_601,'#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12621,c_13897])).

tff(c_13931,plain,(
    ! [B_601] : k4_xboole_0('#skF_3',k2_tarski(B_601,'#skF_5')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13926,c_18])).

tff(c_13939,plain,(
    ! [B_601] : k4_xboole_0('#skF_3',k2_tarski(B_601,'#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_13931])).

tff(c_13944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13939,c_11853])).

tff(c_13946,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_13951,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13946,c_32])).

tff(c_15971,plain,(
    ! [A_719,B_720] : k5_xboole_0(k5_xboole_0(A_719,B_720),k2_xboole_0(A_719,B_720)) = k3_xboole_0(A_719,B_720) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16010,plain,(
    ! [A_26] : k5_xboole_0('#skF_6',k2_xboole_0(A_26,A_26)) = k3_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_13951,c_15971])).

tff(c_16016,plain,(
    ! [A_26] : k5_xboole_0('#skF_6',A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_16010])).

tff(c_16018,plain,(
    ! [A_721,B_722,C_723] : k5_xboole_0(k5_xboole_0(A_721,B_722),C_723) = k5_xboole_0(A_721,k5_xboole_0(B_722,C_723)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16072,plain,(
    ! [A_26,C_723] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_723)) = k5_xboole_0('#skF_6',C_723) ),
    inference(superposition,[status(thm),theory(equality)],[c_13951,c_16018])).

tff(c_16299,plain,(
    ! [A_26,C_723] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_723)) = C_723 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16016,c_16072])).

tff(c_13950,plain,(
    ! [A_19] : k5_xboole_0(A_19,'#skF_6') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13946,c_22])).

tff(c_16043,plain,(
    ! [A_721,B_722] : k5_xboole_0(A_721,k5_xboole_0(B_722,k5_xboole_0(A_721,B_722))) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_16018,c_13951])).

tff(c_16300,plain,(
    ! [A_734,C_735] : k5_xboole_0(A_734,k5_xboole_0(A_734,C_735)) = C_735 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16016,c_16072])).

tff(c_16343,plain,(
    ! [B_722,A_721] : k5_xboole_0(B_722,k5_xboole_0(A_721,B_722)) = k5_xboole_0(A_721,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16043,c_16300])).

tff(c_16393,plain,(
    ! [B_736,A_737] : k5_xboole_0(B_736,k5_xboole_0(A_737,B_736)) = A_737 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13950,c_16343])).

tff(c_16429,plain,(
    ! [A_26,C_723] : k5_xboole_0(k5_xboole_0(A_26,C_723),C_723) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_16299,c_16393])).

tff(c_14707,plain,(
    ! [A_674,B_675] : k5_xboole_0(k5_xboole_0(A_674,B_675),k2_xboole_0(A_674,B_675)) = k3_xboole_0(A_674,B_675) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14740,plain,(
    ! [A_26] : k5_xboole_0('#skF_6',k2_xboole_0(A_26,A_26)) = k3_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_13951,c_14707])).

tff(c_14746,plain,(
    ! [A_26] : k5_xboole_0('#skF_6',A_26) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_14740])).

tff(c_14853,plain,(
    ! [A_681,B_682,C_683] : k5_xboole_0(k5_xboole_0(A_681,B_682),C_683) = k5_xboole_0(A_681,k5_xboole_0(B_682,C_683)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14910,plain,(
    ! [A_26,C_683] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_683)) = k5_xboole_0('#skF_6',C_683) ),
    inference(superposition,[status(thm),theory(equality)],[c_13951,c_14853])).

tff(c_14923,plain,(
    ! [A_26,C_683] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_683)) = C_683 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14746,c_14910])).

tff(c_15039,plain,(
    ! [A_687,B_688] : k5_xboole_0(A_687,k5_xboole_0(B_688,k5_xboole_0(A_687,B_688))) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_14853,c_13951])).

tff(c_15047,plain,(
    ! [B_688,A_687] : k5_xboole_0(B_688,k5_xboole_0(A_687,B_688)) = k5_xboole_0(A_687,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_15039,c_14923])).

tff(c_15140,plain,(
    ! [B_689,A_690] : k5_xboole_0(B_689,k5_xboole_0(A_690,B_689)) = A_690 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13950,c_15047])).

tff(c_15179,plain,(
    ! [A_26,C_683] : k5_xboole_0(k5_xboole_0(A_26,C_683),C_683) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_14923,c_15140])).

tff(c_14096,plain,(
    ! [A_631,B_632] : k5_xboole_0(A_631,k3_xboole_0(A_631,B_632)) = k4_xboole_0(A_631,B_632) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14105,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14096])).

tff(c_14108,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13951,c_14105])).

tff(c_72,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14295,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13946,c_13946,c_72])).

tff(c_14296,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14295])).

tff(c_14306,plain,(
    ! [A_19] : k5_xboole_0(A_19,'#skF_3') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14296,c_13950])).

tff(c_14307,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14296,c_13951])).

tff(c_13952,plain,(
    r1_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13946,c_13946,c_24])).

tff(c_14167,plain,(
    ! [A_638,B_639,C_640] :
      ( ~ r1_xboole_0(A_638,B_639)
      | ~ r2_hidden(C_640,B_639)
      | ~ r2_hidden(C_640,A_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14171,plain,(
    ! [C_641] : ~ r2_hidden(C_641,'#skF_6') ),
    inference(resolution,[status(thm)],[c_13952,c_14167])).

tff(c_14200,plain,(
    ! [B_643] : r1_tarski('#skF_6',B_643) ),
    inference(resolution,[status(thm)],[c_6,c_14171])).

tff(c_14204,plain,(
    ! [B_643] : k2_xboole_0('#skF_6',B_643) = B_643 ),
    inference(resolution,[status(thm)],[c_14200,c_20])).

tff(c_14297,plain,(
    ! [B_643] : k2_xboole_0('#skF_3',B_643) = B_643 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14296,c_14204])).

tff(c_14467,plain,(
    ! [A_665,B_666] : k5_xboole_0(k5_xboole_0(A_665,B_666),k2_xboole_0(A_665,B_666)) = k3_xboole_0(A_665,B_666) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14488,plain,(
    ! [A_26] : k5_xboole_0('#skF_3',k2_xboole_0(A_26,A_26)) = k3_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_14307,c_14467])).

tff(c_14508,plain,(
    ! [A_667] : k5_xboole_0('#skF_3',A_667) = A_667 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_14488])).

tff(c_14514,plain,(
    ! [A_667] : k5_xboole_0(A_667,k2_xboole_0('#skF_3',A_667)) = k3_xboole_0('#skF_3',A_667) ),
    inference(superposition,[status(thm),theory(equality)],[c_14508,c_34])).

tff(c_14550,plain,(
    ! [A_668] : k3_xboole_0('#skF_3',A_668) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14307,c_14297,c_14514])).

tff(c_14555,plain,(
    ! [A_668] : k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3',A_668) ),
    inference(superposition,[status(thm),theory(equality)],[c_14550,c_18])).

tff(c_14567,plain,(
    ! [A_668] : k4_xboole_0('#skF_3',A_668) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14306,c_14555])).

tff(c_13945,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_14003,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13946,c_13945])).

tff(c_14303,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14296,c_14003])).

tff(c_14644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14567,c_14303])).

tff(c_14645,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14295])).

tff(c_14680,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14645])).

tff(c_14681,plain,(
    k4_xboole_0('#skF_3','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14680,c_14003])).

tff(c_14684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14108,c_14681])).

tff(c_14685,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14645])).

tff(c_14687,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14685])).

tff(c_14014,plain,(
    ! [A_615,B_616] :
      ( k2_xboole_0(A_615,B_616) = B_616
      | ~ r1_tarski(A_615,B_616) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14034,plain,(
    ! [B_45,C_46] : k2_xboole_0(k1_tarski(B_45),k2_tarski(B_45,C_46)) = k2_tarski(B_45,C_46) ),
    inference(resolution,[status(thm)],[c_52,c_14014])).

tff(c_15773,plain,(
    ! [C_711] : k2_xboole_0('#skF_3',k2_tarski('#skF_4',C_711)) = k2_tarski('#skF_4',C_711) ),
    inference(superposition,[status(thm),theory(equality)],[c_14687,c_14034])).

tff(c_15783,plain,(
    ! [C_711] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski('#skF_4',C_711)),k2_tarski('#skF_4',C_711)) = k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_711)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15773,c_34])).

tff(c_15825,plain,(
    ! [C_713] : k3_xboole_0('#skF_3',k2_tarski('#skF_4',C_713)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15179,c_15783])).

tff(c_15833,plain,(
    ! [C_713] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_713)) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15825,c_18])).

tff(c_15845,plain,(
    ! [C_713] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',C_713)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13951,c_15833])).

tff(c_15867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15845,c_14003])).

tff(c_15868,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14685])).

tff(c_14033,plain,(
    ! [C_46,B_45] : k2_xboole_0(k1_tarski(C_46),k2_tarski(B_45,C_46)) = k2_tarski(B_45,C_46) ),
    inference(resolution,[status(thm)],[c_50,c_14014])).

tff(c_15876,plain,(
    ! [B_45] : k2_xboole_0('#skF_3',k2_tarski(B_45,'#skF_5')) = k2_tarski(B_45,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15868,c_14033])).

tff(c_15986,plain,(
    ! [B_45] : k5_xboole_0(k5_xboole_0('#skF_3',k2_tarski(B_45,'#skF_5')),k2_tarski(B_45,'#skF_5')) = k3_xboole_0('#skF_3',k2_tarski(B_45,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15876,c_15971])).

tff(c_16841,plain,(
    ! [B_749] : k3_xboole_0('#skF_3',k2_tarski(B_749,'#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16429,c_15986])).

tff(c_16846,plain,(
    ! [B_749] : k4_xboole_0('#skF_3',k2_tarski(B_749,'#skF_5')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16841,c_18])).

tff(c_16854,plain,(
    ! [B_749] : k4_xboole_0('#skF_3',k2_tarski(B_749,'#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13951,c_16846])).

tff(c_16859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16854,c_14003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:03:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.78/2.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.93  
% 7.90/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 7.90/2.94  
% 7.90/2.94  %Foreground sorts:
% 7.90/2.94  
% 7.90/2.94  
% 7.90/2.94  %Background operators:
% 7.90/2.94  
% 7.90/2.94  
% 7.90/2.94  %Foreground operators:
% 7.90/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.90/2.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.90/2.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.90/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.90/2.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.90/2.94  tff('#skF_7', type, '#skF_7': $i).
% 7.90/2.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.90/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.90/2.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.90/2.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.90/2.94  tff('#skF_5', type, '#skF_5': $i).
% 7.90/2.94  tff('#skF_6', type, '#skF_6': $i).
% 7.90/2.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.90/2.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.90/2.94  tff('#skF_3', type, '#skF_3': $i).
% 7.90/2.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.90/2.94  tff('#skF_8', type, '#skF_8': $i).
% 7.90/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/2.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.90/2.94  tff('#skF_4', type, '#skF_4': $i).
% 7.90/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/2.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.90/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.90/2.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.90/2.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.90/2.94  
% 7.90/2.97  tff(f_80, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.90/2.97  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.90/2.97  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.90/2.97  tff(f_82, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.90/2.97  tff(f_78, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.90/2.97  tff(f_62, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.90/2.97  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.90/2.97  tff(f_125, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 7.90/2.97  tff(f_76, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.90/2.97  tff(f_107, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 7.90/2.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.90/2.97  tff(f_74, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 7.90/2.97  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.90/2.97  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.90/2.97  tff(c_32, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.90/2.97  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.90/2.97  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.90/2.97  tff(c_12179, plain, (![A_531, B_532]: (k5_xboole_0(k5_xboole_0(A_531, B_532), k2_xboole_0(A_531, B_532))=k3_xboole_0(A_531, B_532))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_12212, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_26, A_26))=k3_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_32, c_12179])).
% 7.90/2.97  tff(c_12218, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_12212])).
% 7.90/2.97  tff(c_12334, plain, (![A_537, B_538, C_539]: (k5_xboole_0(k5_xboole_0(A_537, B_538), C_539)=k5_xboole_0(A_537, k5_xboole_0(B_538, C_539)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.90/2.97  tff(c_12402, plain, (![A_26, C_539]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_539))=k5_xboole_0(k1_xboole_0, C_539))), inference(superposition, [status(thm), theory('equality')], [c_32, c_12334])).
% 7.90/2.97  tff(c_12415, plain, (![A_26, C_539]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_539))=C_539)), inference(demodulation, [status(thm), theory('equality')], [c_12218, c_12402])).
% 7.90/2.97  tff(c_22, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.90/2.97  tff(c_12484, plain, (![A_542, B_543]: (k5_xboole_0(A_542, k5_xboole_0(B_543, k5_xboole_0(A_542, B_543)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_12334])).
% 7.90/2.97  tff(c_12492, plain, (![B_543, A_542]: (k5_xboole_0(B_543, k5_xboole_0(A_542, B_543))=k5_xboole_0(A_542, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12484, c_12415])).
% 7.90/2.97  tff(c_12585, plain, (![B_544, A_545]: (k5_xboole_0(B_544, k5_xboole_0(A_545, B_544))=A_545)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12492])).
% 7.90/2.97  tff(c_12621, plain, (![A_26, C_539]: (k5_xboole_0(k5_xboole_0(A_26, C_539), C_539)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_12415, c_12585])).
% 7.90/2.97  tff(c_11934, plain, (![A_502, B_503]: (k5_xboole_0(A_502, k3_xboole_0(A_502, B_503))=k4_xboole_0(A_502, B_503))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.90/2.97  tff(c_11943, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_11934])).
% 7.90/2.97  tff(c_11946, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_11943])).
% 7.90/2.97  tff(c_9672, plain, (![A_417, B_418]: (k5_xboole_0(k5_xboole_0(A_417, B_418), k2_xboole_0(A_417, B_418))=k3_xboole_0(A_417, B_418))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_9739, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_26, A_26))=k3_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_32, c_9672])).
% 7.90/2.97  tff(c_9745, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_9739])).
% 7.90/2.97  tff(c_9433, plain, (![A_409, B_410, C_411]: (k5_xboole_0(k5_xboole_0(A_409, B_410), C_411)=k5_xboole_0(A_409, k5_xboole_0(B_410, C_411)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.90/2.97  tff(c_9474, plain, (![A_26, C_411]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_411))=k5_xboole_0(k1_xboole_0, C_411))), inference(superposition, [status(thm), theory('equality')], [c_32, c_9433])).
% 7.90/2.97  tff(c_9747, plain, (![A_26, C_411]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_411))=C_411)), inference(demodulation, [status(thm), theory('equality')], [c_9745, c_9474])).
% 7.90/2.97  tff(c_9451, plain, (![A_409, B_410]: (k5_xboole_0(A_409, k5_xboole_0(B_410, k5_xboole_0(A_409, B_410)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9433, c_32])).
% 7.90/2.97  tff(c_9852, plain, (![A_422, C_423]: (k5_xboole_0(A_422, k5_xboole_0(A_422, C_423))=C_423)), inference(demodulation, [status(thm), theory('equality')], [c_9745, c_9474])).
% 7.90/2.97  tff(c_9902, plain, (![B_410, A_409]: (k5_xboole_0(B_410, k5_xboole_0(A_409, B_410))=k5_xboole_0(A_409, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9451, c_9852])).
% 7.90/2.97  tff(c_9953, plain, (![B_428, A_429]: (k5_xboole_0(B_428, k5_xboole_0(A_429, B_428))=A_429)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_9902])).
% 7.90/2.97  tff(c_9989, plain, (![A_26, C_411]: (k5_xboole_0(k5_xboole_0(A_26, C_411), C_411)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_9747, c_9953])).
% 7.90/2.97  tff(c_237, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.90/2.97  tff(c_246, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_237])).
% 7.90/2.97  tff(c_249, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_246])).
% 7.90/2.97  tff(c_7089, plain, (![A_317, B_318]: (k5_xboole_0(k5_xboole_0(A_317, B_318), k2_xboole_0(A_317, B_318))=k3_xboole_0(A_317, B_318))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_7147, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_26, A_26))=k3_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_32, c_7089])).
% 7.90/2.97  tff(c_7153, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_7147])).
% 7.90/2.97  tff(c_7037, plain, (![A_314, B_315, C_316]: (k5_xboole_0(k5_xboole_0(A_314, B_315), C_316)=k5_xboole_0(A_314, k5_xboole_0(B_315, C_316)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.90/2.97  tff(c_7078, plain, (![A_26, C_316]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_316))=k5_xboole_0(k1_xboole_0, C_316))), inference(superposition, [status(thm), theory('equality')], [c_32, c_7037])).
% 7.90/2.97  tff(c_7240, plain, (![A_26, C_316]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_316))=C_316)), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_7078])).
% 7.90/2.97  tff(c_7315, plain, (![A_328, B_329]: (k5_xboole_0(A_328, k5_xboole_0(B_329, k5_xboole_0(A_328, B_329)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_7037])).
% 7.90/2.97  tff(c_7323, plain, (![B_329, A_328]: (k5_xboole_0(B_329, k5_xboole_0(A_328, B_329))=k5_xboole_0(A_328, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7315, c_7240])).
% 7.90/2.97  tff(c_7413, plain, (![B_330, A_331]: (k5_xboole_0(B_330, k5_xboole_0(A_331, B_330))=A_331)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7323])).
% 7.90/2.97  tff(c_7449, plain, (![A_26, C_316]: (k5_xboole_0(k5_xboole_0(A_26, C_316), C_316)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_7240, c_7413])).
% 7.90/2.97  tff(c_70, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_140, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_70])).
% 7.90/2.97  tff(c_66, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_205, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_66])).
% 7.90/2.97  tff(c_62, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_tarski('#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_258, plain, (k1_tarski('#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_62])).
% 7.90/2.97  tff(c_58, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_369, plain, (k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_58])).
% 7.90/2.97  tff(c_468, plain, (![A_106, B_107, C_108]: (k5_xboole_0(k5_xboole_0(A_106, B_107), C_108)=k5_xboole_0(A_106, k5_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.90/2.97  tff(c_622, plain, (![A_112, C_113]: (k5_xboole_0(A_112, k5_xboole_0(A_112, C_113))=k5_xboole_0(k1_xboole_0, C_113))), inference(superposition, [status(thm), theory('equality')], [c_32, c_468])).
% 7.90/2.97  tff(c_690, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, A_26)=k5_xboole_0(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_622])).
% 7.90/2.97  tff(c_706, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_690])).
% 7.90/2.97  tff(c_509, plain, (![A_26, C_108]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_108))=k5_xboole_0(k1_xboole_0, C_108))), inference(superposition, [status(thm), theory('equality')], [c_32, c_468])).
% 7.90/2.97  tff(c_708, plain, (![A_26, C_108]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_108))=C_108)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_509])).
% 7.90/2.97  tff(c_486, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k5_xboole_0(B_107, k5_xboole_0(A_106, B_107)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_468, c_32])).
% 7.90/2.97  tff(c_771, plain, (![A_115, C_116]: (k5_xboole_0(A_115, k5_xboole_0(A_115, C_116))=C_116)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_509])).
% 7.90/2.97  tff(c_815, plain, (![B_107, A_106]: (k5_xboole_0(B_107, k5_xboole_0(A_106, B_107))=k5_xboole_0(A_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_486, c_771])).
% 7.90/2.97  tff(c_987, plain, (![B_122, A_123]: (k5_xboole_0(B_122, k5_xboole_0(A_123, B_122))=A_123)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_815])).
% 7.90/2.97  tff(c_1026, plain, (![A_26, C_108]: (k5_xboole_0(k5_xboole_0(A_26, C_108), C_108)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_708, c_987])).
% 7.90/2.97  tff(c_76, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_1862, plain, (k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_76])).
% 7.90/2.97  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.90/2.97  tff(c_873, plain, (![A_118, B_119]: (k5_xboole_0(k5_xboole_0(A_118, B_119), k2_xboole_0(A_118, B_119))=k3_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_30, plain, (![A_23, B_24, C_25]: (k5_xboole_0(k5_xboole_0(A_23, B_24), C_25)=k5_xboole_0(A_23, k5_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.90/2.97  tff(c_2218, plain, (![A_159, B_160]: (k5_xboole_0(A_159, k5_xboole_0(B_160, k2_xboole_0(A_159, B_160)))=k3_xboole_0(A_159, B_160))), inference(superposition, [status(thm), theory('equality')], [c_873, c_30])).
% 7.90/2.97  tff(c_2236, plain, (![B_160, A_159]: (k5_xboole_0(B_160, k2_xboole_0(A_159, B_160))=k5_xboole_0(A_159, k3_xboole_0(A_159, B_160)))), inference(superposition, [status(thm), theory('equality')], [c_2218, c_708])).
% 7.90/2.97  tff(c_2542, plain, (![B_173, A_174]: (k5_xboole_0(B_173, k2_xboole_0(A_174, B_173))=k4_xboole_0(A_174, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2236])).
% 7.90/2.97  tff(c_2736, plain, (![B_177, A_178]: (k5_xboole_0(B_177, k4_xboole_0(A_178, B_177))=k2_xboole_0(A_178, B_177))), inference(superposition, [status(thm), theory('equality')], [c_2542, c_708])).
% 7.90/2.97  tff(c_2784, plain, (k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)=k2_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1862, c_2736])).
% 7.90/2.97  tff(c_2815, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2784])).
% 7.90/2.97  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.90/2.97  tff(c_2880, plain, (r1_tarski('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2815, c_28])).
% 7.90/2.97  tff(c_46, plain, (![B_45, C_46, A_44]: (k2_tarski(B_45, C_46)=A_44 | k1_tarski(C_46)=A_44 | k1_tarski(B_45)=A_44 | k1_xboole_0=A_44 | ~r1_tarski(A_44, k2_tarski(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.90/2.97  tff(c_2892, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6' | k1_tarski('#skF_8')='#skF_6' | k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2880, c_46])).
% 7.90/2.97  tff(c_2899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_205, c_258, c_369, c_2892])).
% 7.90/2.97  tff(c_2900, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_76])).
% 7.90/2.97  tff(c_2970, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_2900])).
% 7.90/2.97  tff(c_74, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_707, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 7.90/2.97  tff(c_2971, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2970, c_707])).
% 7.90/2.97  tff(c_2974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_2971])).
% 7.90/2.97  tff(c_2975, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2900])).
% 7.90/2.97  tff(c_2977, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2975])).
% 7.90/2.97  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.90/2.97  tff(c_24, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.90/2.97  tff(c_328, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, B_95) | ~r2_hidden(C_96, A_94))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.90/2.97  tff(c_332, plain, (![C_97]: (~r2_hidden(C_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_328])).
% 7.90/2.97  tff(c_372, plain, (![B_100]: (r1_tarski(k1_xboole_0, B_100))), inference(resolution, [status(thm)], [c_6, c_332])).
% 7.90/2.97  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.90/2.97  tff(c_376, plain, (![B_100]: (k2_xboole_0(k1_xboole_0, B_100)=B_100)), inference(resolution, [status(thm)], [c_372, c_20])).
% 7.90/2.97  tff(c_903, plain, (![A_26]: (k5_xboole_0(A_26, k2_xboole_0(k1_xboole_0, A_26))=k3_xboole_0(k1_xboole_0, A_26))), inference(superposition, [status(thm), theory('equality')], [c_706, c_873])).
% 7.90/2.97  tff(c_940, plain, (![A_26]: (k3_xboole_0(k1_xboole_0, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_376, c_903])).
% 7.90/2.97  tff(c_711, plain, (![A_114]: (k5_xboole_0(k1_xboole_0, A_114)=A_114)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_690])).
% 7.90/2.97  tff(c_732, plain, (![B_16]: (k4_xboole_0(k1_xboole_0, B_16)=k3_xboole_0(k1_xboole_0, B_16))), inference(superposition, [status(thm), theory('equality')], [c_711, c_18])).
% 7.90/2.97  tff(c_945, plain, (![B_16]: (k4_xboole_0(k1_xboole_0, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_940, c_732])).
% 7.90/2.97  tff(c_2984, plain, (![B_16]: (k4_xboole_0('#skF_3', B_16)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2977, c_2977, c_945])).
% 7.90/2.97  tff(c_2986, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2977, c_707])).
% 7.90/2.97  tff(c_3303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2984, c_2986])).
% 7.90/2.97  tff(c_3304, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_2975])).
% 7.90/2.97  tff(c_3306, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_3304])).
% 7.90/2.97  tff(c_50, plain, (![C_46, B_45]: (r1_tarski(k1_tarski(C_46), k2_tarski(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.90/2.97  tff(c_156, plain, (![A_65, B_66]: (k2_xboole_0(A_65, B_66)=B_66 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.90/2.97  tff(c_175, plain, (![C_46, B_45]: (k2_xboole_0(k1_tarski(C_46), k2_tarski(B_45, C_46))=k2_tarski(B_45, C_46))), inference(resolution, [status(thm)], [c_50, c_156])).
% 7.90/2.97  tff(c_3466, plain, (![B_204]: (k2_xboole_0('#skF_3', k2_tarski(B_204, '#skF_5'))=k2_tarski(B_204, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3306, c_175])).
% 7.90/2.97  tff(c_34, plain, (![A_27, B_28]: (k5_xboole_0(k5_xboole_0(A_27, B_28), k2_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_3476, plain, (![B_204]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski(B_204, '#skF_5')), k2_tarski(B_204, '#skF_5'))=k3_xboole_0('#skF_3', k2_tarski(B_204, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_3466, c_34])).
% 7.90/2.97  tff(c_3503, plain, (![B_205]: (k3_xboole_0('#skF_3', k2_tarski(B_205, '#skF_5'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_3476])).
% 7.90/2.97  tff(c_3520, plain, (![B_205]: (k4_xboole_0('#skF_3', k2_tarski(B_205, '#skF_5'))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3503, c_18])).
% 7.90/2.97  tff(c_3533, plain, (![B_205]: (k4_xboole_0('#skF_3', k2_tarski(B_205, '#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3520])).
% 7.90/2.97  tff(c_3539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3533, c_707])).
% 7.90/2.97  tff(c_3540, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_3304])).
% 7.90/2.97  tff(c_52, plain, (![B_45, C_46]: (r1_tarski(k1_tarski(B_45), k2_tarski(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.90/2.97  tff(c_176, plain, (![B_45, C_46]: (k2_xboole_0(k1_tarski(B_45), k2_tarski(B_45, C_46))=k2_tarski(B_45, C_46))), inference(resolution, [status(thm)], [c_52, c_156])).
% 7.90/2.97  tff(c_3624, plain, (![C_211]: (k2_xboole_0('#skF_3', k2_tarski('#skF_4', C_211))=k2_tarski('#skF_4', C_211))), inference(superposition, [status(thm), theory('equality')], [c_3540, c_176])).
% 7.90/2.97  tff(c_3630, plain, (![C_211]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski('#skF_4', C_211)), k2_tarski('#skF_4', C_211))=k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_211)))), inference(superposition, [status(thm), theory('equality')], [c_3624, c_34])).
% 7.90/2.97  tff(c_3686, plain, (![C_213]: (k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_213))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_3630])).
% 7.90/2.97  tff(c_3700, plain, (![C_213]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_213))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3686, c_18])).
% 7.90/2.97  tff(c_3709, plain, (![C_213]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_213))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3700])).
% 7.90/2.97  tff(c_3748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3709, c_707])).
% 7.90/2.97  tff(c_3749, plain, (k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 7.90/2.97  tff(c_4199, plain, (![A_225, B_226]: (k5_xboole_0(k5_xboole_0(A_225, B_226), k2_xboole_0(A_225, B_226))=k3_xboole_0(A_225, B_226))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_5300, plain, (![A_260, B_261]: (k5_xboole_0(A_260, k5_xboole_0(B_261, k2_xboole_0(A_260, B_261)))=k3_xboole_0(A_260, B_261))), inference(superposition, [status(thm), theory('equality')], [c_4199, c_30])).
% 7.90/2.97  tff(c_3751, plain, (![A_26, C_108]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_108))=C_108)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_509])).
% 7.90/2.97  tff(c_5318, plain, (![B_261, A_260]: (k5_xboole_0(B_261, k2_xboole_0(A_260, B_261))=k5_xboole_0(A_260, k3_xboole_0(A_260, B_261)))), inference(superposition, [status(thm), theory('equality')], [c_5300, c_3751])).
% 7.90/2.97  tff(c_5648, plain, (![B_279, A_280]: (k5_xboole_0(B_279, k2_xboole_0(A_280, B_279))=k4_xboole_0(A_280, B_279))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5318])).
% 7.90/2.97  tff(c_5725, plain, (![B_281, A_282]: (k5_xboole_0(B_281, k4_xboole_0(A_282, B_281))=k2_xboole_0(A_282, B_281))), inference(superposition, [status(thm), theory('equality')], [c_5648, c_3751])).
% 7.90/2.97  tff(c_5786, plain, (k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)=k2_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3749, c_5725])).
% 7.90/2.97  tff(c_5810, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_5786])).
% 7.90/2.97  tff(c_6599, plain, (r1_tarski('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5810, c_28])).
% 7.90/2.97  tff(c_6830, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6' | k1_tarski('#skF_8')='#skF_6' | k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6599, c_46])).
% 7.90/2.97  tff(c_6837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_205, c_258, c_369, c_6830])).
% 7.90/2.97  tff(c_6839, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_58])).
% 7.90/2.97  tff(c_60, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_7850, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6839, c_60])).
% 7.90/2.97  tff(c_7851, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_7850])).
% 7.90/2.97  tff(c_6842, plain, (![B_308]: (r1_tarski(k1_xboole_0, B_308))), inference(resolution, [status(thm)], [c_6, c_332])).
% 7.90/2.97  tff(c_6846, plain, (![B_308]: (k2_xboole_0(k1_xboole_0, B_308)=B_308)), inference(resolution, [status(thm)], [c_6842, c_20])).
% 7.90/2.97  tff(c_7155, plain, (![A_319]: (k5_xboole_0(k1_xboole_0, A_319)=A_319)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_7147])).
% 7.90/2.97  tff(c_7161, plain, (![A_319]: (k5_xboole_0(A_319, k2_xboole_0(k1_xboole_0, A_319))=k3_xboole_0(k1_xboole_0, A_319))), inference(superposition, [status(thm), theory('equality')], [c_7155, c_34])).
% 7.90/2.97  tff(c_7201, plain, (![A_320]: (k3_xboole_0(k1_xboole_0, A_320)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6846, c_7161])).
% 7.90/2.97  tff(c_7206, plain, (![A_320]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_320))), inference(superposition, [status(thm), theory('equality')], [c_7201, c_18])).
% 7.90/2.97  tff(c_7218, plain, (![A_320]: (k4_xboole_0(k1_xboole_0, A_320)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7206])).
% 7.90/2.97  tff(c_7852, plain, (![A_320]: (k4_xboole_0('#skF_3', A_320)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7851, c_7851, c_7218])).
% 7.90/2.97  tff(c_6838, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 7.90/2.97  tff(c_7855, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7851, c_6838])).
% 7.90/2.97  tff(c_8210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7852, c_7855])).
% 7.90/2.97  tff(c_8211, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_7850])).
% 7.90/2.97  tff(c_8584, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_8211])).
% 7.90/2.97  tff(c_8585, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8584, c_6838])).
% 7.90/2.97  tff(c_8588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_8585])).
% 7.90/2.97  tff(c_8589, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_8211])).
% 7.90/2.97  tff(c_8591, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_8589])).
% 7.90/2.97  tff(c_8774, plain, (![C_372]: (k2_xboole_0('#skF_3', k2_tarski('#skF_4', C_372))=k2_tarski('#skF_4', C_372))), inference(superposition, [status(thm), theory('equality')], [c_8591, c_176])).
% 7.90/2.97  tff(c_8784, plain, (![C_372]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski('#skF_4', C_372)), k2_tarski('#skF_4', C_372))=k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_372)))), inference(superposition, [status(thm), theory('equality')], [c_8774, c_34])).
% 7.90/2.97  tff(c_8841, plain, (![C_374]: (k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_374))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7449, c_8784])).
% 7.90/2.97  tff(c_8855, plain, (![C_374]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_374))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8841, c_18])).
% 7.90/2.97  tff(c_8867, plain, (![C_374]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_374))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8855])).
% 7.90/2.97  tff(c_8873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8867, c_6838])).
% 7.90/2.97  tff(c_8874, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_8589])).
% 7.90/2.97  tff(c_9058, plain, (![B_383]: (k2_xboole_0('#skF_3', k2_tarski(B_383, '#skF_5'))=k2_tarski(B_383, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8874, c_175])).
% 7.90/2.97  tff(c_9068, plain, (![B_383]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski(B_383, '#skF_5')), k2_tarski(B_383, '#skF_5'))=k3_xboole_0('#skF_3', k2_tarski(B_383, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9058, c_34])).
% 7.90/2.97  tff(c_9094, plain, (![B_384]: (k3_xboole_0('#skF_3', k2_tarski(B_384, '#skF_5'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7449, c_9068])).
% 7.90/2.97  tff(c_9108, plain, (![B_384]: (k4_xboole_0('#skF_3', k2_tarski(B_384, '#skF_5'))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9094, c_18])).
% 7.90/2.97  tff(c_9120, plain, (![B_384]: (k4_xboole_0('#skF_3', k2_tarski(B_384, '#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9108])).
% 7.90/2.97  tff(c_9126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9120, c_6838])).
% 7.90/2.97  tff(c_9128, plain, (k1_tarski('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_62])).
% 7.90/2.97  tff(c_64, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski('#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_10109, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9128, c_64])).
% 7.90/2.97  tff(c_10110, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_10109])).
% 7.90/2.97  tff(c_9186, plain, (![A_387, B_388, C_389]: (~r1_xboole_0(A_387, B_388) | ~r2_hidden(C_389, B_388) | ~r2_hidden(C_389, A_387))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.90/2.97  tff(c_9190, plain, (![C_390]: (~r2_hidden(C_390, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_9186])).
% 7.90/2.97  tff(c_9230, plain, (![B_393]: (r1_tarski(k1_xboole_0, B_393))), inference(resolution, [status(thm)], [c_6, c_9190])).
% 7.90/2.97  tff(c_9234, plain, (![B_393]: (k2_xboole_0(k1_xboole_0, B_393)=B_393)), inference(resolution, [status(thm)], [c_9230, c_20])).
% 7.90/2.97  tff(c_9750, plain, (![A_419]: (k5_xboole_0(k1_xboole_0, A_419)=A_419)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_9739])).
% 7.90/2.97  tff(c_9756, plain, (![A_419]: (k5_xboole_0(A_419, k2_xboole_0(k1_xboole_0, A_419))=k3_xboole_0(k1_xboole_0, A_419))), inference(superposition, [status(thm), theory('equality')], [c_9750, c_34])).
% 7.90/2.97  tff(c_9816, plain, (![A_420]: (k3_xboole_0(k1_xboole_0, A_420)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9234, c_9756])).
% 7.90/2.97  tff(c_9821, plain, (![A_420]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_420))), inference(superposition, [status(thm), theory('equality')], [c_9816, c_18])).
% 7.90/2.97  tff(c_9833, plain, (![A_420]: (k4_xboole_0(k1_xboole_0, A_420)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_9821])).
% 7.90/2.97  tff(c_10111, plain, (![A_420]: (k4_xboole_0('#skF_3', A_420)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10110, c_10110, c_9833])).
% 7.90/2.97  tff(c_9127, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 7.90/2.97  tff(c_10119, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10110, c_9127])).
% 7.90/2.97  tff(c_10418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10111, c_10119])).
% 7.90/2.97  tff(c_10419, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_10109])).
% 7.90/2.97  tff(c_10693, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_10419])).
% 7.90/2.97  tff(c_10694, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10693, c_9127])).
% 7.90/2.97  tff(c_10697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_10694])).
% 7.90/2.97  tff(c_10698, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_10419])).
% 7.90/2.97  tff(c_10700, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_10698])).
% 7.90/2.97  tff(c_11162, plain, (![C_469]: (k2_xboole_0('#skF_3', k2_tarski('#skF_4', C_469))=k2_tarski('#skF_4', C_469))), inference(superposition, [status(thm), theory('equality')], [c_10700, c_176])).
% 7.90/2.97  tff(c_11172, plain, (![C_469]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski('#skF_4', C_469)), k2_tarski('#skF_4', C_469))=k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_469)))), inference(superposition, [status(thm), theory('equality')], [c_11162, c_34])).
% 7.90/2.97  tff(c_11198, plain, (![C_470]: (k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_470))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9989, c_11172])).
% 7.90/2.97  tff(c_11206, plain, (![C_470]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_470))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11198, c_18])).
% 7.90/2.97  tff(c_11218, plain, (![C_470]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_470))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_11206])).
% 7.90/2.97  tff(c_11440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11218, c_9127])).
% 7.90/2.97  tff(c_11441, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_10698])).
% 7.90/2.97  tff(c_11808, plain, (![B_493]: (k2_xboole_0('#skF_3', k2_tarski(B_493, '#skF_5'))=k2_tarski(B_493, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11441, c_175])).
% 7.90/2.97  tff(c_11814, plain, (![B_493]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski(B_493, '#skF_5')), k2_tarski(B_493, '#skF_5'))=k3_xboole_0('#skF_3', k2_tarski(B_493, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11808, c_34])).
% 7.90/2.97  tff(c_11834, plain, (![B_494]: (k3_xboole_0('#skF_3', k2_tarski(B_494, '#skF_5'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9989, c_11814])).
% 7.90/2.97  tff(c_11839, plain, (![B_494]: (k4_xboole_0('#skF_3', k2_tarski(B_494, '#skF_5'))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11834, c_18])).
% 7.90/2.97  tff(c_11847, plain, (![B_494]: (k4_xboole_0('#skF_3', k2_tarski(B_494, '#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_11839])).
% 7.90/2.97  tff(c_11852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11847, c_9127])).
% 7.90/2.97  tff(c_11854, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 7.90/2.97  tff(c_68, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_12666, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11854, c_68])).
% 7.90/2.97  tff(c_12667, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_12666])).
% 7.90/2.97  tff(c_12090, plain, (![A_523, B_524, C_525]: (~r1_xboole_0(A_523, B_524) | ~r2_hidden(C_525, B_524) | ~r2_hidden(C_525, A_523))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.90/2.97  tff(c_12094, plain, (![C_526]: (~r2_hidden(C_526, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_12090])).
% 7.90/2.97  tff(c_12124, plain, (![B_528]: (r1_tarski(k1_xboole_0, B_528))), inference(resolution, [status(thm)], [c_6, c_12094])).
% 7.90/2.97  tff(c_12128, plain, (![B_528]: (k2_xboole_0(k1_xboole_0, B_528)=B_528)), inference(resolution, [status(thm)], [c_12124, c_20])).
% 7.90/2.97  tff(c_12220, plain, (![A_533]: (k5_xboole_0(k1_xboole_0, A_533)=A_533)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_12212])).
% 7.90/2.97  tff(c_12226, plain, (![A_533]: (k5_xboole_0(A_533, k2_xboole_0(k1_xboole_0, A_533))=k3_xboole_0(k1_xboole_0, A_533))), inference(superposition, [status(thm), theory('equality')], [c_12220, c_34])).
% 7.90/2.97  tff(c_12262, plain, (![A_534]: (k3_xboole_0(k1_xboole_0, A_534)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12128, c_12226])).
% 7.90/2.97  tff(c_12267, plain, (![A_534]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_534))), inference(superposition, [status(thm), theory('equality')], [c_12262, c_18])).
% 7.90/2.97  tff(c_12279, plain, (![A_534]: (k4_xboole_0(k1_xboole_0, A_534)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12267])).
% 7.90/2.97  tff(c_12669, plain, (![A_534]: (k4_xboole_0('#skF_3', A_534)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12667, c_12667, c_12279])).
% 7.90/2.97  tff(c_11853, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 7.90/2.97  tff(c_12678, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12667, c_11853])).
% 7.90/2.97  tff(c_12971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12669, c_12678])).
% 7.90/2.97  tff(c_12972, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_12666])).
% 7.90/2.97  tff(c_13330, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_12972])).
% 7.90/2.97  tff(c_13331, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13330, c_11853])).
% 7.90/2.97  tff(c_13334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11946, c_13331])).
% 7.90/2.97  tff(c_13335, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_12972])).
% 7.90/2.97  tff(c_13337, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_13335])).
% 7.90/2.97  tff(c_13367, plain, (![C_565]: (r1_tarski('#skF_3', k2_tarski('#skF_4', C_565)))), inference(superposition, [status(thm), theory('equality')], [c_13337, c_52])).
% 7.90/2.97  tff(c_13608, plain, (![C_582]: (k2_xboole_0('#skF_3', k2_tarski('#skF_4', C_582))=k2_tarski('#skF_4', C_582))), inference(resolution, [status(thm)], [c_13367, c_20])).
% 7.90/2.97  tff(c_13618, plain, (![C_582]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski('#skF_4', C_582)), k2_tarski('#skF_4', C_582))=k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_582)))), inference(superposition, [status(thm), theory('equality')], [c_13608, c_34])).
% 7.90/2.97  tff(c_13644, plain, (![C_583]: (k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_583))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12621, c_13618])).
% 7.90/2.97  tff(c_13652, plain, (![C_583]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_583))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13644, c_18])).
% 7.90/2.97  tff(c_13664, plain, (![C_583]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_583))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_13652])).
% 7.90/2.97  tff(c_13687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13664, c_11853])).
% 7.90/2.97  tff(c_13688, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_13335])).
% 7.90/2.97  tff(c_13707, plain, (![B_585]: (r1_tarski('#skF_3', k2_tarski(B_585, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_13688, c_50])).
% 7.90/2.97  tff(c_13891, plain, (![B_595]: (k2_xboole_0('#skF_3', k2_tarski(B_595, '#skF_5'))=k2_tarski(B_595, '#skF_5'))), inference(resolution, [status(thm)], [c_13707, c_20])).
% 7.90/2.97  tff(c_13897, plain, (![B_595]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski(B_595, '#skF_5')), k2_tarski(B_595, '#skF_5'))=k3_xboole_0('#skF_3', k2_tarski(B_595, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_13891, c_34])).
% 7.90/2.97  tff(c_13926, plain, (![B_601]: (k3_xboole_0('#skF_3', k2_tarski(B_601, '#skF_5'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12621, c_13897])).
% 7.90/2.97  tff(c_13931, plain, (![B_601]: (k4_xboole_0('#skF_3', k2_tarski(B_601, '#skF_5'))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13926, c_18])).
% 7.90/2.97  tff(c_13939, plain, (![B_601]: (k4_xboole_0('#skF_3', k2_tarski(B_601, '#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_13931])).
% 7.90/2.97  tff(c_13944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13939, c_11853])).
% 7.90/2.97  tff(c_13946, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_70])).
% 7.90/2.97  tff(c_13951, plain, (![A_26]: (k5_xboole_0(A_26, A_26)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13946, c_32])).
% 7.90/2.97  tff(c_15971, plain, (![A_719, B_720]: (k5_xboole_0(k5_xboole_0(A_719, B_720), k2_xboole_0(A_719, B_720))=k3_xboole_0(A_719, B_720))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_16010, plain, (![A_26]: (k5_xboole_0('#skF_6', k2_xboole_0(A_26, A_26))=k3_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_13951, c_15971])).
% 7.90/2.97  tff(c_16016, plain, (![A_26]: (k5_xboole_0('#skF_6', A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_16010])).
% 7.90/2.97  tff(c_16018, plain, (![A_721, B_722, C_723]: (k5_xboole_0(k5_xboole_0(A_721, B_722), C_723)=k5_xboole_0(A_721, k5_xboole_0(B_722, C_723)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.90/2.97  tff(c_16072, plain, (![A_26, C_723]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_723))=k5_xboole_0('#skF_6', C_723))), inference(superposition, [status(thm), theory('equality')], [c_13951, c_16018])).
% 7.90/2.97  tff(c_16299, plain, (![A_26, C_723]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_723))=C_723)), inference(demodulation, [status(thm), theory('equality')], [c_16016, c_16072])).
% 7.90/2.97  tff(c_13950, plain, (![A_19]: (k5_xboole_0(A_19, '#skF_6')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_13946, c_22])).
% 7.90/2.97  tff(c_16043, plain, (![A_721, B_722]: (k5_xboole_0(A_721, k5_xboole_0(B_722, k5_xboole_0(A_721, B_722)))='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_16018, c_13951])).
% 7.90/2.97  tff(c_16300, plain, (![A_734, C_735]: (k5_xboole_0(A_734, k5_xboole_0(A_734, C_735))=C_735)), inference(demodulation, [status(thm), theory('equality')], [c_16016, c_16072])).
% 7.90/2.97  tff(c_16343, plain, (![B_722, A_721]: (k5_xboole_0(B_722, k5_xboole_0(A_721, B_722))=k5_xboole_0(A_721, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16043, c_16300])).
% 7.90/2.97  tff(c_16393, plain, (![B_736, A_737]: (k5_xboole_0(B_736, k5_xboole_0(A_737, B_736))=A_737)), inference(demodulation, [status(thm), theory('equality')], [c_13950, c_16343])).
% 7.90/2.97  tff(c_16429, plain, (![A_26, C_723]: (k5_xboole_0(k5_xboole_0(A_26, C_723), C_723)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_16299, c_16393])).
% 7.90/2.97  tff(c_14707, plain, (![A_674, B_675]: (k5_xboole_0(k5_xboole_0(A_674, B_675), k2_xboole_0(A_674, B_675))=k3_xboole_0(A_674, B_675))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_14740, plain, (![A_26]: (k5_xboole_0('#skF_6', k2_xboole_0(A_26, A_26))=k3_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_13951, c_14707])).
% 7.90/2.97  tff(c_14746, plain, (![A_26]: (k5_xboole_0('#skF_6', A_26)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_14740])).
% 7.90/2.97  tff(c_14853, plain, (![A_681, B_682, C_683]: (k5_xboole_0(k5_xboole_0(A_681, B_682), C_683)=k5_xboole_0(A_681, k5_xboole_0(B_682, C_683)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.90/2.97  tff(c_14910, plain, (![A_26, C_683]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_683))=k5_xboole_0('#skF_6', C_683))), inference(superposition, [status(thm), theory('equality')], [c_13951, c_14853])).
% 7.90/2.97  tff(c_14923, plain, (![A_26, C_683]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_683))=C_683)), inference(demodulation, [status(thm), theory('equality')], [c_14746, c_14910])).
% 7.90/2.97  tff(c_15039, plain, (![A_687, B_688]: (k5_xboole_0(A_687, k5_xboole_0(B_688, k5_xboole_0(A_687, B_688)))='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_14853, c_13951])).
% 7.90/2.97  tff(c_15047, plain, (![B_688, A_687]: (k5_xboole_0(B_688, k5_xboole_0(A_687, B_688))=k5_xboole_0(A_687, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15039, c_14923])).
% 7.90/2.97  tff(c_15140, plain, (![B_689, A_690]: (k5_xboole_0(B_689, k5_xboole_0(A_690, B_689))=A_690)), inference(demodulation, [status(thm), theory('equality')], [c_13950, c_15047])).
% 7.90/2.97  tff(c_15179, plain, (![A_26, C_683]: (k5_xboole_0(k5_xboole_0(A_26, C_683), C_683)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_14923, c_15140])).
% 7.90/2.97  tff(c_14096, plain, (![A_631, B_632]: (k5_xboole_0(A_631, k3_xboole_0(A_631, B_632))=k4_xboole_0(A_631, B_632))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.90/2.97  tff(c_14105, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_14096])).
% 7.90/2.97  tff(c_14108, plain, (![A_8]: (k4_xboole_0(A_8, A_8)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13951, c_14105])).
% 7.90/2.97  tff(c_72, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.90/2.97  tff(c_14295, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13946, c_13946, c_72])).
% 7.90/2.97  tff(c_14296, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_14295])).
% 7.90/2.97  tff(c_14306, plain, (![A_19]: (k5_xboole_0(A_19, '#skF_3')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_14296, c_13950])).
% 7.90/2.97  tff(c_14307, plain, (![A_26]: (k5_xboole_0(A_26, A_26)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14296, c_13951])).
% 7.90/2.97  tff(c_13952, plain, (r1_xboole_0('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13946, c_13946, c_24])).
% 7.90/2.97  tff(c_14167, plain, (![A_638, B_639, C_640]: (~r1_xboole_0(A_638, B_639) | ~r2_hidden(C_640, B_639) | ~r2_hidden(C_640, A_638))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.90/2.97  tff(c_14171, plain, (![C_641]: (~r2_hidden(C_641, '#skF_6'))), inference(resolution, [status(thm)], [c_13952, c_14167])).
% 7.90/2.97  tff(c_14200, plain, (![B_643]: (r1_tarski('#skF_6', B_643))), inference(resolution, [status(thm)], [c_6, c_14171])).
% 7.90/2.97  tff(c_14204, plain, (![B_643]: (k2_xboole_0('#skF_6', B_643)=B_643)), inference(resolution, [status(thm)], [c_14200, c_20])).
% 7.90/2.97  tff(c_14297, plain, (![B_643]: (k2_xboole_0('#skF_3', B_643)=B_643)), inference(demodulation, [status(thm), theory('equality')], [c_14296, c_14204])).
% 7.90/2.97  tff(c_14467, plain, (![A_665, B_666]: (k5_xboole_0(k5_xboole_0(A_665, B_666), k2_xboole_0(A_665, B_666))=k3_xboole_0(A_665, B_666))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.90/2.97  tff(c_14488, plain, (![A_26]: (k5_xboole_0('#skF_3', k2_xboole_0(A_26, A_26))=k3_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_14307, c_14467])).
% 7.90/2.97  tff(c_14508, plain, (![A_667]: (k5_xboole_0('#skF_3', A_667)=A_667)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_14488])).
% 7.90/2.97  tff(c_14514, plain, (![A_667]: (k5_xboole_0(A_667, k2_xboole_0('#skF_3', A_667))=k3_xboole_0('#skF_3', A_667))), inference(superposition, [status(thm), theory('equality')], [c_14508, c_34])).
% 7.90/2.97  tff(c_14550, plain, (![A_668]: (k3_xboole_0('#skF_3', A_668)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14307, c_14297, c_14514])).
% 7.90/2.97  tff(c_14555, plain, (![A_668]: (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', A_668))), inference(superposition, [status(thm), theory('equality')], [c_14550, c_18])).
% 7.90/2.97  tff(c_14567, plain, (![A_668]: (k4_xboole_0('#skF_3', A_668)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14306, c_14555])).
% 7.90/2.97  tff(c_13945, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 7.90/2.97  tff(c_14003, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_13946, c_13945])).
% 7.90/2.97  tff(c_14303, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14296, c_14003])).
% 7.90/2.97  tff(c_14644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14567, c_14303])).
% 7.90/2.97  tff(c_14645, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_14295])).
% 7.90/2.97  tff(c_14680, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_14645])).
% 7.90/2.97  tff(c_14681, plain, (k4_xboole_0('#skF_3', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_14680, c_14003])).
% 7.90/2.97  tff(c_14684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14108, c_14681])).
% 7.90/2.97  tff(c_14685, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_14645])).
% 7.90/2.97  tff(c_14687, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_14685])).
% 7.90/2.97  tff(c_14014, plain, (![A_615, B_616]: (k2_xboole_0(A_615, B_616)=B_616 | ~r1_tarski(A_615, B_616))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.90/2.97  tff(c_14034, plain, (![B_45, C_46]: (k2_xboole_0(k1_tarski(B_45), k2_tarski(B_45, C_46))=k2_tarski(B_45, C_46))), inference(resolution, [status(thm)], [c_52, c_14014])).
% 7.90/2.97  tff(c_15773, plain, (![C_711]: (k2_xboole_0('#skF_3', k2_tarski('#skF_4', C_711))=k2_tarski('#skF_4', C_711))), inference(superposition, [status(thm), theory('equality')], [c_14687, c_14034])).
% 7.90/2.97  tff(c_15783, plain, (![C_711]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski('#skF_4', C_711)), k2_tarski('#skF_4', C_711))=k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_711)))), inference(superposition, [status(thm), theory('equality')], [c_15773, c_34])).
% 7.90/2.97  tff(c_15825, plain, (![C_713]: (k3_xboole_0('#skF_3', k2_tarski('#skF_4', C_713))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15179, c_15783])).
% 7.90/2.97  tff(c_15833, plain, (![C_713]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_713))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_15825, c_18])).
% 7.90/2.97  tff(c_15845, plain, (![C_713]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', C_713))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13951, c_15833])).
% 7.90/2.97  tff(c_15867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15845, c_14003])).
% 7.90/2.97  tff(c_15868, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_14685])).
% 7.90/2.97  tff(c_14033, plain, (![C_46, B_45]: (k2_xboole_0(k1_tarski(C_46), k2_tarski(B_45, C_46))=k2_tarski(B_45, C_46))), inference(resolution, [status(thm)], [c_50, c_14014])).
% 7.90/2.97  tff(c_15876, plain, (![B_45]: (k2_xboole_0('#skF_3', k2_tarski(B_45, '#skF_5'))=k2_tarski(B_45, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15868, c_14033])).
% 7.90/2.97  tff(c_15986, plain, (![B_45]: (k5_xboole_0(k5_xboole_0('#skF_3', k2_tarski(B_45, '#skF_5')), k2_tarski(B_45, '#skF_5'))=k3_xboole_0('#skF_3', k2_tarski(B_45, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_15876, c_15971])).
% 7.90/2.97  tff(c_16841, plain, (![B_749]: (k3_xboole_0('#skF_3', k2_tarski(B_749, '#skF_5'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16429, c_15986])).
% 7.90/2.97  tff(c_16846, plain, (![B_749]: (k4_xboole_0('#skF_3', k2_tarski(B_749, '#skF_5'))=k5_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16841, c_18])).
% 7.90/2.97  tff(c_16854, plain, (![B_749]: (k4_xboole_0('#skF_3', k2_tarski(B_749, '#skF_5'))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13951, c_16846])).
% 7.90/2.97  tff(c_16859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16854, c_14003])).
% 7.90/2.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.97  
% 7.90/2.97  Inference rules
% 7.90/2.97  ----------------------
% 7.90/2.97  #Ref     : 0
% 7.90/2.97  #Sup     : 4042
% 7.90/2.97  #Fact    : 0
% 7.90/2.97  #Define  : 0
% 7.90/2.97  #Split   : 28
% 7.90/2.97  #Chain   : 0
% 7.90/2.97  #Close   : 0
% 7.90/2.97  
% 7.90/2.97  Ordering : KBO
% 7.90/2.97  
% 7.90/2.97  Simplification rules
% 7.90/2.97  ----------------------
% 7.90/2.97  #Subsume      : 67
% 7.90/2.97  #Demod        : 3172
% 7.90/2.97  #Tautology    : 2827
% 7.90/2.97  #SimpNegUnit  : 33
% 7.90/2.97  #BackRed      : 122
% 7.90/2.97  
% 7.90/2.97  #Partial instantiations: 0
% 7.90/2.97  #Strategies tried      : 1
% 7.90/2.97  
% 7.90/2.97  Timing (in seconds)
% 7.90/2.97  ----------------------
% 7.90/2.98  Preprocessing        : 0.35
% 7.90/2.98  Parsing              : 0.18
% 7.90/2.98  CNF conversion       : 0.03
% 7.90/2.98  Main loop            : 1.79
% 7.90/2.98  Inferencing          : 0.58
% 7.90/2.98  Reduction            : 0.74
% 7.90/2.98  Demodulation         : 0.58
% 7.90/2.98  BG Simplification    : 0.07
% 7.90/2.98  Subsumption          : 0.25
% 7.90/2.98  Abstraction          : 0.09
% 7.90/2.98  MUC search           : 0.00
% 7.90/2.98  Cooper               : 0.00
% 7.90/2.98  Total                : 2.24
% 7.90/2.98  Index Insertion      : 0.00
% 7.90/2.98  Index Deletion       : 0.00
% 7.90/2.98  Index Matching       : 0.00
% 7.90/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
