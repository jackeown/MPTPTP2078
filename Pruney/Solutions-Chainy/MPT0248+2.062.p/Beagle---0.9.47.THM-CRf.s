%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:12 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 281 expanded)
%              Number of leaves         :   34 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :   98 ( 401 expanded)
%              Number of equality atoms :   86 ( 386 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_72,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_123,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_70,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_111,plain,(
    k1_tarski('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_36])).

tff(c_836,plain,(
    ! [B_119,A_120] :
      ( k1_tarski(B_119) = A_120
      | k1_xboole_0 = A_120
      | ~ r1_tarski(A_120,k1_tarski(B_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_843,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_127,c_836])).

tff(c_852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_111,c_843])).

tff(c_853,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_854,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_34,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_856,plain,(
    ! [A_20] : k5_xboole_0(A_20,'#skF_3') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_34])).

tff(c_44,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_857,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_44])).

tff(c_30,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_855,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_854,c_30])).

tff(c_1160,plain,(
    ! [A_152,B_153] : k5_xboole_0(A_152,k3_xboole_0(A_152,B_153)) = k4_xboole_0(A_152,B_153) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1187,plain,(
    ! [A_17] : k5_xboole_0(A_17,'#skF_3') = k4_xboole_0(A_17,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_855,c_1160])).

tff(c_1196,plain,(
    ! [A_156] : k4_xboole_0(A_156,'#skF_3') = A_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_1187])).

tff(c_46,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1202,plain,(
    ! [A_156] : k5_xboole_0('#skF_3',A_156) = k2_xboole_0('#skF_3',A_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_1196,c_46])).

tff(c_1694,plain,(
    ! [A_185,B_186,C_187] : k5_xboole_0(k5_xboole_0(A_185,B_186),C_187) = k5_xboole_0(A_185,k5_xboole_0(B_186,C_187)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1760,plain,(
    ! [A_28,C_187] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_187)) = k5_xboole_0('#skF_3',C_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_1694])).

tff(c_1984,plain,(
    ! [A_197,C_198] : k5_xboole_0(A_197,k5_xboole_0(A_197,C_198)) = k2_xboole_0('#skF_3',C_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_1760])).

tff(c_2066,plain,(
    ! [A_28] : k5_xboole_0(A_28,'#skF_3') = k2_xboole_0('#skF_3',A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_1984])).

tff(c_2082,plain,(
    ! [A_28] : k2_xboole_0('#skF_3',A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_2066])).

tff(c_2086,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2082,c_76])).

tff(c_2089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_853,c_2086])).

tff(c_2090,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2091,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2132,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2091,c_2091,c_74])).

tff(c_2096,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2091,c_76])).

tff(c_2425,plain,(
    ! [A_228,B_229] : k5_xboole_0(A_228,k3_xboole_0(A_228,B_229)) = k4_xboole_0(A_228,B_229) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2458,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2425])).

tff(c_2480,plain,(
    ! [A_232] : k4_xboole_0(A_232,k1_xboole_0) = A_232 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2458])).

tff(c_2486,plain,(
    ! [A_232] : k5_xboole_0(k1_xboole_0,A_232) = k2_xboole_0(k1_xboole_0,A_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_46])).

tff(c_3020,plain,(
    ! [A_264,B_265,C_266] : k5_xboole_0(k5_xboole_0(A_264,B_265),C_266) = k5_xboole_0(A_264,k5_xboole_0(B_265,C_266)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3086,plain,(
    ! [A_28,C_266] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_266)) = k5_xboole_0(k1_xboole_0,C_266) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3020])).

tff(c_3258,plain,(
    ! [A_277,C_278] : k5_xboole_0(A_277,k5_xboole_0(A_277,C_278)) = k2_xboole_0(k1_xboole_0,C_278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_3086])).

tff(c_3334,plain,(
    ! [A_28] : k5_xboole_0(A_28,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3258])).

tff(c_3349,plain,(
    ! [A_28] : k2_xboole_0(k1_xboole_0,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3334])).

tff(c_3099,plain,(
    ! [A_28,C_266] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_266)) = k2_xboole_0(k1_xboole_0,C_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_3086])).

tff(c_3543,plain,(
    ! [A_285,C_286] : k5_xboole_0(A_285,k5_xboole_0(A_285,C_286)) = C_286 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3349,c_3099])).

tff(c_4306,plain,(
    ! [A_321,B_322] : k5_xboole_0(A_321,k2_xboole_0(A_321,B_322)) = k4_xboole_0(B_322,A_321) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3543])).

tff(c_4370,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2096,c_4306])).

tff(c_4380,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4370])).

tff(c_26,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3613,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3543])).

tff(c_4384,plain,(
    k5_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4380,c_3613])).

tff(c_4402,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4384])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2452,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2425])).

tff(c_4411,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4402,c_2452])).

tff(c_3046,plain,(
    ! [A_264,B_265] : k5_xboole_0(A_264,k5_xboole_0(B_265,k5_xboole_0(A_264,B_265))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3020,c_44])).

tff(c_3593,plain,(
    ! [B_265,A_264] : k5_xboole_0(B_265,k5_xboole_0(A_264,B_265)) = k5_xboole_0(A_264,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3046,c_3543])).

tff(c_3632,plain,(
    ! [B_265,A_264] : k5_xboole_0(B_265,k5_xboole_0(A_264,B_265)) = A_264 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3593])).

tff(c_4449,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4411,c_3632])).

tff(c_4657,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4449,c_46])).

tff(c_4686,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4657,c_36])).

tff(c_2988,plain,(
    ! [B_261,A_262] :
      ( k1_tarski(B_261) = A_262
      | k1_xboole_0 = A_262
      | ~ r1_tarski(A_262,k1_tarski(B_261)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2995,plain,(
    ! [A_262] :
      ( k1_tarski('#skF_2') = A_262
      | k1_xboole_0 = A_262
      | ~ r1_tarski(A_262,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2091,c_2988])).

tff(c_3001,plain,(
    ! [A_262] :
      ( A_262 = '#skF_3'
      | k1_xboole_0 = A_262
      | ~ r1_tarski(A_262,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2091,c_2995])).

tff(c_4696,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4686,c_3001])).

tff(c_4703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2090,c_2132,c_4696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.97  
% 4.71/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.71/1.98  
% 4.71/1.98  %Foreground sorts:
% 4.71/1.98  
% 4.71/1.98  
% 4.71/1.98  %Background operators:
% 4.71/1.98  
% 4.71/1.98  
% 4.71/1.98  %Foreground operators:
% 4.71/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.71/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.71/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.71/1.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.71/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.71/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.71/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.71/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.71/1.98  tff('#skF_2', type, '#skF_2': $i).
% 4.71/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.71/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.71/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.71/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.71/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.71/1.98  
% 5.02/1.99  tff(f_110, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.02/1.99  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.02/1.99  tff(f_89, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.02/1.99  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.02/1.99  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.02/1.99  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.02/1.99  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.02/1.99  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.02/1.99  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.02/1.99  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.02/1.99  tff(c_72, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.02/1.99  tff(c_123, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_72])).
% 5.02/1.99  tff(c_70, plain, (k1_xboole_0!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.02/1.99  tff(c_111, plain, (k1_tarski('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_70])).
% 5.02/1.99  tff(c_76, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.02/1.99  tff(c_36, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.02/1.99  tff(c_127, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_36])).
% 5.02/1.99  tff(c_836, plain, (![B_119, A_120]: (k1_tarski(B_119)=A_120 | k1_xboole_0=A_120 | ~r1_tarski(A_120, k1_tarski(B_119)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.02/1.99  tff(c_843, plain, (k1_tarski('#skF_2')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_127, c_836])).
% 5.02/1.99  tff(c_852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_111, c_843])).
% 5.02/1.99  tff(c_853, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(splitRight, [status(thm)], [c_72])).
% 5.02/1.99  tff(c_854, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 5.02/1.99  tff(c_34, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.99  tff(c_856, plain, (![A_20]: (k5_xboole_0(A_20, '#skF_3')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_854, c_34])).
% 5.02/1.99  tff(c_44, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.02/1.99  tff(c_857, plain, (![A_28]: (k5_xboole_0(A_28, A_28)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_854, c_44])).
% 5.02/1.99  tff(c_30, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.02/1.99  tff(c_855, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_854, c_854, c_30])).
% 5.02/1.99  tff(c_1160, plain, (![A_152, B_153]: (k5_xboole_0(A_152, k3_xboole_0(A_152, B_153))=k4_xboole_0(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.02/1.99  tff(c_1187, plain, (![A_17]: (k5_xboole_0(A_17, '#skF_3')=k4_xboole_0(A_17, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_855, c_1160])).
% 5.02/1.99  tff(c_1196, plain, (![A_156]: (k4_xboole_0(A_156, '#skF_3')=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_856, c_1187])).
% 5.02/1.99  tff(c_46, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.02/1.99  tff(c_1202, plain, (![A_156]: (k5_xboole_0('#skF_3', A_156)=k2_xboole_0('#skF_3', A_156))), inference(superposition, [status(thm), theory('equality')], [c_1196, c_46])).
% 5.02/1.99  tff(c_1694, plain, (![A_185, B_186, C_187]: (k5_xboole_0(k5_xboole_0(A_185, B_186), C_187)=k5_xboole_0(A_185, k5_xboole_0(B_186, C_187)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.02/1.99  tff(c_1760, plain, (![A_28, C_187]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_187))=k5_xboole_0('#skF_3', C_187))), inference(superposition, [status(thm), theory('equality')], [c_857, c_1694])).
% 5.02/1.99  tff(c_1984, plain, (![A_197, C_198]: (k5_xboole_0(A_197, k5_xboole_0(A_197, C_198))=k2_xboole_0('#skF_3', C_198))), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_1760])).
% 5.02/1.99  tff(c_2066, plain, (![A_28]: (k5_xboole_0(A_28, '#skF_3')=k2_xboole_0('#skF_3', A_28))), inference(superposition, [status(thm), theory('equality')], [c_857, c_1984])).
% 5.02/1.99  tff(c_2082, plain, (![A_28]: (k2_xboole_0('#skF_3', A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_856, c_2066])).
% 5.02/1.99  tff(c_2086, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2082, c_76])).
% 5.02/1.99  tff(c_2089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_853, c_2086])).
% 5.02/1.99  tff(c_2090, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 5.02/1.99  tff(c_2091, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 5.02/1.99  tff(c_74, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.02/1.99  tff(c_2132, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2091, c_2091, c_74])).
% 5.02/1.99  tff(c_2096, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2091, c_76])).
% 5.02/1.99  tff(c_2425, plain, (![A_228, B_229]: (k5_xboole_0(A_228, k3_xboole_0(A_228, B_229))=k4_xboole_0(A_228, B_229))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.02/1.99  tff(c_2458, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2425])).
% 5.02/1.99  tff(c_2480, plain, (![A_232]: (k4_xboole_0(A_232, k1_xboole_0)=A_232)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2458])).
% 5.02/1.99  tff(c_2486, plain, (![A_232]: (k5_xboole_0(k1_xboole_0, A_232)=k2_xboole_0(k1_xboole_0, A_232))), inference(superposition, [status(thm), theory('equality')], [c_2480, c_46])).
% 5.02/1.99  tff(c_3020, plain, (![A_264, B_265, C_266]: (k5_xboole_0(k5_xboole_0(A_264, B_265), C_266)=k5_xboole_0(A_264, k5_xboole_0(B_265, C_266)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.02/1.99  tff(c_3086, plain, (![A_28, C_266]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_266))=k5_xboole_0(k1_xboole_0, C_266))), inference(superposition, [status(thm), theory('equality')], [c_44, c_3020])).
% 5.02/1.99  tff(c_3258, plain, (![A_277, C_278]: (k5_xboole_0(A_277, k5_xboole_0(A_277, C_278))=k2_xboole_0(k1_xboole_0, C_278))), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_3086])).
% 5.02/1.99  tff(c_3334, plain, (![A_28]: (k5_xboole_0(A_28, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_28))), inference(superposition, [status(thm), theory('equality')], [c_44, c_3258])).
% 5.02/1.99  tff(c_3349, plain, (![A_28]: (k2_xboole_0(k1_xboole_0, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3334])).
% 5.02/1.99  tff(c_3099, plain, (![A_28, C_266]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_266))=k2_xboole_0(k1_xboole_0, C_266))), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_3086])).
% 5.02/1.99  tff(c_3543, plain, (![A_285, C_286]: (k5_xboole_0(A_285, k5_xboole_0(A_285, C_286))=C_286)), inference(demodulation, [status(thm), theory('equality')], [c_3349, c_3099])).
% 5.02/1.99  tff(c_4306, plain, (![A_321, B_322]: (k5_xboole_0(A_321, k2_xboole_0(A_321, B_322))=k4_xboole_0(B_322, A_321))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3543])).
% 5.02/1.99  tff(c_4370, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2096, c_4306])).
% 5.02/1.99  tff(c_4380, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4370])).
% 5.02/1.99  tff(c_26, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.02/1.99  tff(c_3613, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3543])).
% 5.02/1.99  tff(c_4384, plain, (k5_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4380, c_3613])).
% 5.02/1.99  tff(c_4402, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4384])).
% 5.02/1.99  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.02/1.99  tff(c_2452, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2425])).
% 5.02/1.99  tff(c_4411, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4402, c_2452])).
% 5.02/1.99  tff(c_3046, plain, (![A_264, B_265]: (k5_xboole_0(A_264, k5_xboole_0(B_265, k5_xboole_0(A_264, B_265)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3020, c_44])).
% 5.02/1.99  tff(c_3593, plain, (![B_265, A_264]: (k5_xboole_0(B_265, k5_xboole_0(A_264, B_265))=k5_xboole_0(A_264, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3046, c_3543])).
% 5.02/1.99  tff(c_3632, plain, (![B_265, A_264]: (k5_xboole_0(B_265, k5_xboole_0(A_264, B_265))=A_264)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3593])).
% 5.02/1.99  tff(c_4449, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4411, c_3632])).
% 5.02/1.99  tff(c_4657, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4449, c_46])).
% 5.02/1.99  tff(c_4686, plain, (r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4657, c_36])).
% 5.02/1.99  tff(c_2988, plain, (![B_261, A_262]: (k1_tarski(B_261)=A_262 | k1_xboole_0=A_262 | ~r1_tarski(A_262, k1_tarski(B_261)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.02/1.99  tff(c_2995, plain, (![A_262]: (k1_tarski('#skF_2')=A_262 | k1_xboole_0=A_262 | ~r1_tarski(A_262, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2091, c_2988])).
% 5.02/1.99  tff(c_3001, plain, (![A_262]: (A_262='#skF_3' | k1_xboole_0=A_262 | ~r1_tarski(A_262, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2091, c_2995])).
% 5.02/1.99  tff(c_4696, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4686, c_3001])).
% 5.02/1.99  tff(c_4703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2090, c_2132, c_4696])).
% 5.02/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.99  
% 5.02/1.99  Inference rules
% 5.02/1.99  ----------------------
% 5.02/1.99  #Ref     : 0
% 5.02/1.99  #Sup     : 1128
% 5.02/1.99  #Fact    : 0
% 5.02/1.99  #Define  : 0
% 5.02/1.99  #Split   : 3
% 5.02/1.99  #Chain   : 0
% 5.02/1.99  #Close   : 0
% 5.02/1.99  
% 5.02/1.99  Ordering : KBO
% 5.02/1.99  
% 5.02/1.99  Simplification rules
% 5.02/1.99  ----------------------
% 5.02/1.99  #Subsume      : 17
% 5.02/1.99  #Demod        : 668
% 5.02/1.99  #Tautology    : 780
% 5.02/1.99  #SimpNegUnit  : 10
% 5.02/1.99  #BackRed      : 26
% 5.02/1.99  
% 5.02/1.99  #Partial instantiations: 0
% 5.02/1.99  #Strategies tried      : 1
% 5.02/1.99  
% 5.02/1.99  Timing (in seconds)
% 5.02/1.99  ----------------------
% 5.02/2.00  Preprocessing        : 0.37
% 5.02/2.00  Parsing              : 0.20
% 5.02/2.00  CNF conversion       : 0.02
% 5.02/2.00  Main loop            : 0.80
% 5.02/2.00  Inferencing          : 0.28
% 5.02/2.00  Reduction            : 0.29
% 5.02/2.00  Demodulation         : 0.23
% 5.02/2.00  BG Simplification    : 0.04
% 5.02/2.00  Subsumption          : 0.13
% 5.02/2.00  Abstraction          : 0.04
% 5.02/2.00  MUC search           : 0.00
% 5.02/2.00  Cooper               : 0.00
% 5.02/2.00  Total                : 1.21
% 5.02/2.00  Index Insertion      : 0.00
% 5.02/2.00  Index Deletion       : 0.00
% 5.02/2.00  Index Matching       : 0.00
% 5.02/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
