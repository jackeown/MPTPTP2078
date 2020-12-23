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
% DateTime   : Thu Dec  3 09:50:51 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 125 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 173 expanded)
%              Number of equality atoms :   49 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_62,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2312,plain,(
    ! [A_242,B_243,C_244] :
      ( r2_hidden('#skF_2'(A_242,B_243,C_244),A_242)
      | r2_hidden('#skF_3'(A_242,B_243,C_244),C_244)
      | k4_xboole_0(A_242,B_243) = C_244 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2457,plain,(
    ! [A_251,C_252] :
      ( r2_hidden('#skF_3'(A_251,A_251,C_252),C_252)
      | k4_xboole_0(A_251,A_251) = C_252 ) ),
    inference(resolution,[status(thm)],[c_2312,c_22])).

tff(c_44,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_637,plain,(
    ! [A_112,B_113,C_114] :
      ( r1_tarski(k2_tarski(A_112,B_113),C_114)
      | ~ r2_hidden(B_113,C_114)
      | ~ r2_hidden(A_112,C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_670,plain,(
    ! [A_115,C_116] :
      ( r1_tarski(k1_tarski(A_115),C_116)
      | ~ r2_hidden(A_115,C_116)
      | ~ r2_hidden(A_115,C_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_637])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_750,plain,(
    ! [A_124,C_125] :
      ( k1_tarski(A_124) = C_125
      | ~ r1_tarski(C_125,k1_tarski(A_124))
      | ~ r2_hidden(A_124,C_125) ) ),
    inference(resolution,[status(thm)],[c_670,c_26])).

tff(c_769,plain,(
    ! [A_124] :
      ( k1_tarski(A_124) = k1_xboole_0
      | ~ r2_hidden(A_124,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_750])).

tff(c_2488,plain,(
    ! [A_253] :
      ( k1_tarski('#skF_3'(A_253,A_253,k1_xboole_0)) = k1_xboole_0
      | k4_xboole_0(A_253,A_253) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2457,c_769])).

tff(c_399,plain,(
    ! [B_77,C_78,A_79] :
      ( r2_hidden(B_77,C_78)
      | ~ r1_tarski(k2_tarski(A_79,B_77),C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_408,plain,(
    ! [A_24,C_78] :
      ( r2_hidden(A_24,C_78)
      | ~ r1_tarski(k1_tarski(A_24),C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_399])).

tff(c_2505,plain,(
    ! [A_253,C_78] :
      ( r2_hidden('#skF_3'(A_253,A_253,k1_xboole_0),C_78)
      | ~ r1_tarski(k1_xboole_0,C_78)
      | k4_xboole_0(A_253,A_253) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2488,c_408])).

tff(c_2516,plain,(
    ! [A_253,C_78] :
      ( r2_hidden('#skF_3'(A_253,A_253,k1_xboole_0),C_78)
      | k4_xboole_0(A_253,A_253) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2505])).

tff(c_42,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_117,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_196,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(B_55,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_117])).

tff(c_52,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_223,plain,(
    ! [B_56,A_57] : k2_xboole_0(B_56,A_57) = k2_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_52])).

tff(c_239,plain,(
    ! [A_57] : k2_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_34])).

tff(c_279,plain,(
    ! [A_60] : k2_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_34])).

tff(c_40,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_286,plain,(
    ! [B_21] : k4_xboole_0(B_21,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_40])).

tff(c_317,plain,(
    ! [B_21] : k4_xboole_0(B_21,k1_xboole_0) = B_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_286])).

tff(c_367,plain,(
    ! [D_65,B_66,A_67] :
      ( ~ r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k4_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_370,plain,(
    ! [D_65,B_21] :
      ( ~ r2_hidden(D_65,k1_xboole_0)
      | ~ r2_hidden(D_65,B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_367])).

tff(c_2549,plain,(
    ! [A_256,B_257] :
      ( ~ r2_hidden('#skF_3'(A_256,A_256,k1_xboole_0),B_257)
      | k4_xboole_0(A_256,A_256) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2457,c_370])).

tff(c_2572,plain,(
    ! [A_253] : k4_xboole_0(A_253,A_253) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2516,c_2549])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_161,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_169,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_161])).

tff(c_455,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_464,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_455])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_690,plain,(
    ! [A_117,C_118] :
      ( k3_xboole_0(k1_tarski(A_117),C_118) = k1_tarski(A_117)
      | ~ r2_hidden(A_117,C_118) ) ),
    inference(resolution,[status(thm)],[c_670,c_36])).

tff(c_32,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_696,plain,(
    ! [A_117,C_118] :
      ( k5_xboole_0(k1_tarski(A_117),k1_tarski(A_117)) = k4_xboole_0(k1_tarski(A_117),C_118)
      | ~ r2_hidden(A_117,C_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_32])).

tff(c_709,plain,(
    ! [A_117,C_118] :
      ( k4_xboole_0(k1_tarski(A_117),k1_tarski(A_117)) = k4_xboole_0(k1_tarski(A_117),C_118)
      | ~ r2_hidden(A_117,C_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_696])).

tff(c_2975,plain,(
    ! [A_291,C_292] :
      ( k4_xboole_0(k1_tarski(A_291),C_292) = k1_xboole_0
      | ~ r2_hidden(A_291,C_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2572,c_709])).

tff(c_3021,plain,(
    ! [C_292,A_291] :
      ( k2_xboole_0(C_292,k1_tarski(A_291)) = k2_xboole_0(C_292,k1_xboole_0)
      | ~ r2_hidden(A_291,C_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2975,c_40])).

tff(c_3046,plain,(
    ! [C_293,A_294] :
      ( k2_xboole_0(C_293,k1_tarski(A_294)) = C_293
      | ~ r2_hidden(A_294,C_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3021])).

tff(c_202,plain,(
    ! [B_55,A_54] : k2_xboole_0(B_55,A_54) = k2_xboole_0(A_54,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_52])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_222,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_60])).

tff(c_3056,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3046,c_222])).

tff(c_3093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:23:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.78  
% 4.58/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.78  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.60/1.78  
% 4.60/1.78  %Foreground sorts:
% 4.60/1.78  
% 4.60/1.78  
% 4.60/1.78  %Background operators:
% 4.60/1.78  
% 4.60/1.78  
% 4.60/1.78  %Foreground operators:
% 4.60/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.60/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.60/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.60/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.60/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.60/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.60/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.60/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.60/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.60/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.60/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.60/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.60/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.60/1.78  
% 4.60/1.80  tff(f_83, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.60/1.80  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.60/1.80  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.60/1.80  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.60/1.80  tff(f_64, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.60/1.80  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.60/1.80  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.60/1.80  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.60/1.80  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.60/1.80  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.60/1.80  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.60/1.80  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.60/1.80  tff(c_62, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.60/1.80  tff(c_34, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.60/1.80  tff(c_38, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.60/1.80  tff(c_2312, plain, (![A_242, B_243, C_244]: (r2_hidden('#skF_2'(A_242, B_243, C_244), A_242) | r2_hidden('#skF_3'(A_242, B_243, C_244), C_244) | k4_xboole_0(A_242, B_243)=C_244)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.60/1.80  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.60/1.80  tff(c_2457, plain, (![A_251, C_252]: (r2_hidden('#skF_3'(A_251, A_251, C_252), C_252) | k4_xboole_0(A_251, A_251)=C_252)), inference(resolution, [status(thm)], [c_2312, c_22])).
% 4.60/1.80  tff(c_44, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.60/1.80  tff(c_637, plain, (![A_112, B_113, C_114]: (r1_tarski(k2_tarski(A_112, B_113), C_114) | ~r2_hidden(B_113, C_114) | ~r2_hidden(A_112, C_114))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.60/1.80  tff(c_670, plain, (![A_115, C_116]: (r1_tarski(k1_tarski(A_115), C_116) | ~r2_hidden(A_115, C_116) | ~r2_hidden(A_115, C_116))), inference(superposition, [status(thm), theory('equality')], [c_44, c_637])).
% 4.60/1.80  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.80  tff(c_750, plain, (![A_124, C_125]: (k1_tarski(A_124)=C_125 | ~r1_tarski(C_125, k1_tarski(A_124)) | ~r2_hidden(A_124, C_125))), inference(resolution, [status(thm)], [c_670, c_26])).
% 4.60/1.80  tff(c_769, plain, (![A_124]: (k1_tarski(A_124)=k1_xboole_0 | ~r2_hidden(A_124, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_750])).
% 4.60/1.80  tff(c_2488, plain, (![A_253]: (k1_tarski('#skF_3'(A_253, A_253, k1_xboole_0))=k1_xboole_0 | k4_xboole_0(A_253, A_253)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2457, c_769])).
% 4.60/1.80  tff(c_399, plain, (![B_77, C_78, A_79]: (r2_hidden(B_77, C_78) | ~r1_tarski(k2_tarski(A_79, B_77), C_78))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.60/1.80  tff(c_408, plain, (![A_24, C_78]: (r2_hidden(A_24, C_78) | ~r1_tarski(k1_tarski(A_24), C_78))), inference(superposition, [status(thm), theory('equality')], [c_44, c_399])).
% 4.60/1.80  tff(c_2505, plain, (![A_253, C_78]: (r2_hidden('#skF_3'(A_253, A_253, k1_xboole_0), C_78) | ~r1_tarski(k1_xboole_0, C_78) | k4_xboole_0(A_253, A_253)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2488, c_408])).
% 4.60/1.80  tff(c_2516, plain, (![A_253, C_78]: (r2_hidden('#skF_3'(A_253, A_253, k1_xboole_0), C_78) | k4_xboole_0(A_253, A_253)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2505])).
% 4.60/1.80  tff(c_42, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.60/1.80  tff(c_117, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.80  tff(c_196, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(B_55, A_54))), inference(superposition, [status(thm), theory('equality')], [c_42, c_117])).
% 4.60/1.80  tff(c_52, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.80  tff(c_223, plain, (![B_56, A_57]: (k2_xboole_0(B_56, A_57)=k2_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_196, c_52])).
% 4.60/1.80  tff(c_239, plain, (![A_57]: (k2_xboole_0(k1_xboole_0, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_223, c_34])).
% 4.60/1.80  tff(c_279, plain, (![A_60]: (k2_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_223, c_34])).
% 4.60/1.80  tff(c_40, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.60/1.80  tff(c_286, plain, (![B_21]: (k4_xboole_0(B_21, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_21))), inference(superposition, [status(thm), theory('equality')], [c_279, c_40])).
% 4.60/1.80  tff(c_317, plain, (![B_21]: (k4_xboole_0(B_21, k1_xboole_0)=B_21)), inference(demodulation, [status(thm), theory('equality')], [c_239, c_286])).
% 4.60/1.80  tff(c_367, plain, (![D_65, B_66, A_67]: (~r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k4_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.60/1.80  tff(c_370, plain, (![D_65, B_21]: (~r2_hidden(D_65, k1_xboole_0) | ~r2_hidden(D_65, B_21))), inference(superposition, [status(thm), theory('equality')], [c_317, c_367])).
% 4.60/1.80  tff(c_2549, plain, (![A_256, B_257]: (~r2_hidden('#skF_3'(A_256, A_256, k1_xboole_0), B_257) | k4_xboole_0(A_256, A_256)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2457, c_370])).
% 4.60/1.80  tff(c_2572, plain, (![A_253]: (k4_xboole_0(A_253, A_253)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2516, c_2549])).
% 4.60/1.80  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.80  tff(c_161, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.60/1.80  tff(c_169, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_161])).
% 4.60/1.80  tff(c_455, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.60/1.80  tff(c_464, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_169, c_455])).
% 4.60/1.80  tff(c_36, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.60/1.80  tff(c_690, plain, (![A_117, C_118]: (k3_xboole_0(k1_tarski(A_117), C_118)=k1_tarski(A_117) | ~r2_hidden(A_117, C_118))), inference(resolution, [status(thm)], [c_670, c_36])).
% 4.60/1.80  tff(c_32, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.60/1.80  tff(c_696, plain, (![A_117, C_118]: (k5_xboole_0(k1_tarski(A_117), k1_tarski(A_117))=k4_xboole_0(k1_tarski(A_117), C_118) | ~r2_hidden(A_117, C_118))), inference(superposition, [status(thm), theory('equality')], [c_690, c_32])).
% 4.60/1.80  tff(c_709, plain, (![A_117, C_118]: (k4_xboole_0(k1_tarski(A_117), k1_tarski(A_117))=k4_xboole_0(k1_tarski(A_117), C_118) | ~r2_hidden(A_117, C_118))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_696])).
% 4.60/1.80  tff(c_2975, plain, (![A_291, C_292]: (k4_xboole_0(k1_tarski(A_291), C_292)=k1_xboole_0 | ~r2_hidden(A_291, C_292))), inference(demodulation, [status(thm), theory('equality')], [c_2572, c_709])).
% 4.60/1.80  tff(c_3021, plain, (![C_292, A_291]: (k2_xboole_0(C_292, k1_tarski(A_291))=k2_xboole_0(C_292, k1_xboole_0) | ~r2_hidden(A_291, C_292))), inference(superposition, [status(thm), theory('equality')], [c_2975, c_40])).
% 4.60/1.80  tff(c_3046, plain, (![C_293, A_294]: (k2_xboole_0(C_293, k1_tarski(A_294))=C_293 | ~r2_hidden(A_294, C_293))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3021])).
% 4.60/1.80  tff(c_202, plain, (![B_55, A_54]: (k2_xboole_0(B_55, A_54)=k2_xboole_0(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_196, c_52])).
% 4.60/1.80  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.60/1.80  tff(c_222, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_60])).
% 4.60/1.80  tff(c_3056, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3046, c_222])).
% 4.60/1.80  tff(c_3093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_3056])).
% 4.60/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.80  
% 4.60/1.80  Inference rules
% 4.60/1.80  ----------------------
% 4.60/1.80  #Ref     : 0
% 4.60/1.80  #Sup     : 700
% 4.60/1.80  #Fact    : 0
% 4.60/1.80  #Define  : 0
% 4.60/1.80  #Split   : 4
% 4.60/1.80  #Chain   : 0
% 4.60/1.80  #Close   : 0
% 4.60/1.80  
% 4.60/1.80  Ordering : KBO
% 4.60/1.80  
% 4.60/1.80  Simplification rules
% 4.60/1.80  ----------------------
% 4.60/1.80  #Subsume      : 152
% 4.60/1.80  #Demod        : 257
% 4.60/1.80  #Tautology    : 267
% 4.60/1.80  #SimpNegUnit  : 7
% 4.60/1.80  #BackRed      : 8
% 4.60/1.80  
% 4.60/1.80  #Partial instantiations: 0
% 4.60/1.80  #Strategies tried      : 1
% 4.60/1.80  
% 4.60/1.80  Timing (in seconds)
% 4.60/1.80  ----------------------
% 4.60/1.80  Preprocessing        : 0.32
% 4.60/1.80  Parsing              : 0.16
% 4.60/1.80  CNF conversion       : 0.02
% 4.60/1.80  Main loop            : 0.73
% 4.60/1.80  Inferencing          : 0.25
% 4.60/1.80  Reduction            : 0.23
% 4.60/1.80  Demodulation         : 0.17
% 4.60/1.80  BG Simplification    : 0.03
% 4.60/1.80  Subsumption          : 0.17
% 4.60/1.80  Abstraction          : 0.03
% 4.60/1.80  MUC search           : 0.00
% 4.60/1.80  Cooper               : 0.00
% 4.60/1.80  Total                : 1.08
% 4.60/1.80  Index Insertion      : 0.00
% 4.60/1.80  Index Deletion       : 0.00
% 4.60/1.80  Index Matching       : 0.00
% 4.60/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
