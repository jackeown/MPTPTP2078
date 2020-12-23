%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:50 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.65s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 197 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :   54 ( 187 expanded)
%              Number of equality atoms :   43 ( 172 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_60,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    ! [C_90,A_88,B_89] :
      ( k4_xboole_0(C_90,k2_tarski(A_88,B_89)) = C_90
      | r2_hidden(B_89,C_90)
      | r2_hidden(A_88,C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_862,plain,(
    ! [A_136,B_137] : k5_xboole_0(k5_xboole_0(A_136,B_137),k2_xboole_0(A_136,B_137)) = k3_xboole_0(A_136,B_137) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_935,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_862])).

tff(c_944,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20,c_935])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] : k5_xboole_0(k5_xboole_0(A_17,B_18),C_19) = k5_xboole_0(A_17,k5_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4234,plain,(
    ! [A_259,B_260] : k5_xboole_0(A_259,k5_xboole_0(B_260,k2_xboole_0(A_259,B_260))) = k3_xboole_0(A_259,B_260) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_18])).

tff(c_611,plain,(
    ! [A_128,B_129,C_130] : k5_xboole_0(k5_xboole_0(A_128,B_129),C_130) = k5_xboole_0(A_128,k5_xboole_0(B_129,C_130)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_661,plain,(
    ! [A_20,C_130] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_130)) = k5_xboole_0(k1_xboole_0,C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_611])).

tff(c_947,plain,(
    ! [A_20,C_130] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_130)) = C_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_661])).

tff(c_4252,plain,(
    ! [B_260,A_259] : k5_xboole_0(B_260,k2_xboole_0(A_259,B_260)) = k5_xboole_0(A_259,k3_xboole_0(A_259,B_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4234,c_947])).

tff(c_4350,plain,(
    ! [B_260,A_259] : k5_xboole_0(B_260,k2_xboole_0(A_259,B_260)) = k4_xboole_0(A_259,B_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4252])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_5157,plain,(
    ! [C_273,A_274,B_275] : k5_xboole_0(C_273,k5_xboole_0(A_274,B_275)) = k5_xboole_0(A_274,k5_xboole_0(B_275,C_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_2])).

tff(c_5706,plain,(
    ! [A_276,C_277] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_276,C_277)) = k5_xboole_0(C_277,A_276) ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_5157])).

tff(c_5788,plain,(
    ! [A_259,B_260] : k5_xboole_0(k2_xboole_0(A_259,B_260),B_260) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_259,B_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4350,c_5706])).

tff(c_5891,plain,(
    ! [A_259,B_260] : k5_xboole_0(k2_xboole_0(A_259,B_260),B_260) = k4_xboole_0(A_259,B_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_5788])).

tff(c_4370,plain,(
    ! [B_261,A_262] : k5_xboole_0(B_261,k2_xboole_0(A_262,B_261)) = k4_xboole_0(A_262,B_261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4252])).

tff(c_1249,plain,(
    ! [A_148,C_149] : k5_xboole_0(A_148,k5_xboole_0(A_148,C_149)) = C_149 ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_661])).

tff(c_1322,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1249])).

tff(c_4389,plain,(
    ! [A_262,B_261] : k5_xboole_0(k2_xboole_0(A_262,B_261),k4_xboole_0(A_262,B_261)) = B_261 ),
    inference(superposition,[status(thm),theory(equality)],[c_4370,c_1322])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_xboole_0(A_12,B_13),C_14) = k2_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6275,plain,(
    ! [A_280,B_281] : k5_xboole_0(k2_xboole_0(A_280,B_281),B_281) = k4_xboole_0(A_280,B_281) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_5788])).

tff(c_22,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k2_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6327,plain,(
    ! [A_280,B_281] : k5_xboole_0(k4_xboole_0(A_280,B_281),k2_xboole_0(k2_xboole_0(A_280,B_281),B_281)) = k3_xboole_0(k2_xboole_0(A_280,B_281),B_281) ),
    inference(superposition,[status(thm),theory(equality)],[c_6275,c_22])).

tff(c_6445,plain,(
    ! [A_282,B_283] : k3_xboole_0(k2_xboole_0(A_282,B_283),B_283) = B_283 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4389,c_2,c_4,c_14,c_6327])).

tff(c_6468,plain,(
    ! [A_282,B_283] : k5_xboole_0(k2_xboole_0(A_282,B_283),B_283) = k4_xboole_0(k2_xboole_0(A_282,B_283),B_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_6445,c_8])).

tff(c_6538,plain,(
    ! [A_282,B_283] : k4_xboole_0(k2_xboole_0(A_282,B_283),B_283) = k4_xboole_0(A_282,B_283) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5891,c_6468])).

tff(c_56,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7555,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6538,c_56])).

tff(c_7692,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_7555])).

tff(c_7696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_7692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.36  
% 6.27/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.36  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.27/2.36  
% 6.27/2.36  %Foreground sorts:
% 6.27/2.36  
% 6.27/2.36  
% 6.27/2.36  %Background operators:
% 6.27/2.36  
% 6.27/2.36  
% 6.27/2.36  %Foreground operators:
% 6.27/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.27/2.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.27/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.27/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.27/2.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.27/2.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.27/2.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.27/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.27/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.27/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.27/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.27/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.27/2.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.27/2.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.27/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.27/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.27/2.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.27/2.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.27/2.36  
% 6.65/2.38  tff(f_98, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 6.65/2.38  tff(f_87, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 6.65/2.38  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.65/2.38  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.65/2.38  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.65/2.38  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 6.65/2.38  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.65/2.38  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.65/2.38  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.65/2.38  tff(f_39, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.65/2.38  tff(c_60, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.65/2.38  tff(c_58, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.65/2.38  tff(c_54, plain, (![C_90, A_88, B_89]: (k4_xboole_0(C_90, k2_tarski(A_88, B_89))=C_90 | r2_hidden(B_89, C_90) | r2_hidden(A_88, C_90))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.65/2.38  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.65/2.38  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.65/2.38  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.65/2.38  tff(c_862, plain, (![A_136, B_137]: (k5_xboole_0(k5_xboole_0(A_136, B_137), k2_xboole_0(A_136, B_137))=k3_xboole_0(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.65/2.38  tff(c_935, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_862])).
% 6.65/2.38  tff(c_944, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20, c_935])).
% 6.65/2.38  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.65/2.38  tff(c_18, plain, (![A_17, B_18, C_19]: (k5_xboole_0(k5_xboole_0(A_17, B_18), C_19)=k5_xboole_0(A_17, k5_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.65/2.38  tff(c_4234, plain, (![A_259, B_260]: (k5_xboole_0(A_259, k5_xboole_0(B_260, k2_xboole_0(A_259, B_260)))=k3_xboole_0(A_259, B_260))), inference(superposition, [status(thm), theory('equality')], [c_862, c_18])).
% 6.65/2.38  tff(c_611, plain, (![A_128, B_129, C_130]: (k5_xboole_0(k5_xboole_0(A_128, B_129), C_130)=k5_xboole_0(A_128, k5_xboole_0(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.65/2.38  tff(c_661, plain, (![A_20, C_130]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_130))=k5_xboole_0(k1_xboole_0, C_130))), inference(superposition, [status(thm), theory('equality')], [c_20, c_611])).
% 6.65/2.38  tff(c_947, plain, (![A_20, C_130]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_130))=C_130)), inference(demodulation, [status(thm), theory('equality')], [c_944, c_661])).
% 6.65/2.38  tff(c_4252, plain, (![B_260, A_259]: (k5_xboole_0(B_260, k2_xboole_0(A_259, B_260))=k5_xboole_0(A_259, k3_xboole_0(A_259, B_260)))), inference(superposition, [status(thm), theory('equality')], [c_4234, c_947])).
% 6.65/2.38  tff(c_4350, plain, (![B_260, A_259]: (k5_xboole_0(B_260, k2_xboole_0(A_259, B_260))=k4_xboole_0(A_259, B_260))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4252])).
% 6.65/2.38  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.65/2.38  tff(c_5157, plain, (![C_273, A_274, B_275]: (k5_xboole_0(C_273, k5_xboole_0(A_274, B_275))=k5_xboole_0(A_274, k5_xboole_0(B_275, C_273)))), inference(superposition, [status(thm), theory('equality')], [c_611, c_2])).
% 6.65/2.38  tff(c_5706, plain, (![A_276, C_277]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_276, C_277))=k5_xboole_0(C_277, A_276))), inference(superposition, [status(thm), theory('equality')], [c_944, c_5157])).
% 6.65/2.38  tff(c_5788, plain, (![A_259, B_260]: (k5_xboole_0(k2_xboole_0(A_259, B_260), B_260)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_259, B_260)))), inference(superposition, [status(thm), theory('equality')], [c_4350, c_5706])).
% 6.65/2.38  tff(c_5891, plain, (![A_259, B_260]: (k5_xboole_0(k2_xboole_0(A_259, B_260), B_260)=k4_xboole_0(A_259, B_260))), inference(demodulation, [status(thm), theory('equality')], [c_944, c_5788])).
% 6.65/2.38  tff(c_4370, plain, (![B_261, A_262]: (k5_xboole_0(B_261, k2_xboole_0(A_262, B_261))=k4_xboole_0(A_262, B_261))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4252])).
% 6.65/2.38  tff(c_1249, plain, (![A_148, C_149]: (k5_xboole_0(A_148, k5_xboole_0(A_148, C_149))=C_149)), inference(demodulation, [status(thm), theory('equality')], [c_944, c_661])).
% 6.65/2.38  tff(c_1322, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1249])).
% 6.65/2.38  tff(c_4389, plain, (![A_262, B_261]: (k5_xboole_0(k2_xboole_0(A_262, B_261), k4_xboole_0(A_262, B_261))=B_261)), inference(superposition, [status(thm), theory('equality')], [c_4370, c_1322])).
% 6.65/2.38  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k2_xboole_0(A_12, B_13), C_14)=k2_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.65/2.38  tff(c_6275, plain, (![A_280, B_281]: (k5_xboole_0(k2_xboole_0(A_280, B_281), B_281)=k4_xboole_0(A_280, B_281))), inference(demodulation, [status(thm), theory('equality')], [c_944, c_5788])).
% 6.65/2.38  tff(c_22, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k2_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.65/2.38  tff(c_6327, plain, (![A_280, B_281]: (k5_xboole_0(k4_xboole_0(A_280, B_281), k2_xboole_0(k2_xboole_0(A_280, B_281), B_281))=k3_xboole_0(k2_xboole_0(A_280, B_281), B_281))), inference(superposition, [status(thm), theory('equality')], [c_6275, c_22])).
% 6.65/2.38  tff(c_6445, plain, (![A_282, B_283]: (k3_xboole_0(k2_xboole_0(A_282, B_283), B_283)=B_283)), inference(demodulation, [status(thm), theory('equality')], [c_4389, c_2, c_4, c_14, c_6327])).
% 6.65/2.38  tff(c_6468, plain, (![A_282, B_283]: (k5_xboole_0(k2_xboole_0(A_282, B_283), B_283)=k4_xboole_0(k2_xboole_0(A_282, B_283), B_283))), inference(superposition, [status(thm), theory('equality')], [c_6445, c_8])).
% 6.65/2.38  tff(c_6538, plain, (![A_282, B_283]: (k4_xboole_0(k2_xboole_0(A_282, B_283), B_283)=k4_xboole_0(A_282, B_283))), inference(demodulation, [status(thm), theory('equality')], [c_5891, c_6468])).
% 6.65/2.38  tff(c_56, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.65/2.38  tff(c_7555, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6538, c_56])).
% 6.65/2.38  tff(c_7692, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_54, c_7555])).
% 6.65/2.38  tff(c_7696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_7692])).
% 6.65/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.38  
% 6.65/2.38  Inference rules
% 6.65/2.38  ----------------------
% 6.65/2.38  #Ref     : 0
% 6.65/2.38  #Sup     : 1914
% 6.65/2.38  #Fact    : 0
% 6.65/2.38  #Define  : 0
% 6.65/2.38  #Split   : 1
% 6.65/2.38  #Chain   : 0
% 6.65/2.38  #Close   : 0
% 6.65/2.38  
% 6.65/2.38  Ordering : KBO
% 6.65/2.38  
% 6.65/2.38  Simplification rules
% 6.65/2.38  ----------------------
% 6.65/2.38  #Subsume      : 83
% 6.65/2.38  #Demod        : 1960
% 6.65/2.38  #Tautology    : 1164
% 6.65/2.38  #SimpNegUnit  : 1
% 6.65/2.38  #BackRed      : 5
% 6.65/2.38  
% 6.65/2.38  #Partial instantiations: 0
% 6.65/2.38  #Strategies tried      : 1
% 6.65/2.38  
% 6.65/2.38  Timing (in seconds)
% 6.65/2.38  ----------------------
% 6.65/2.38  Preprocessing        : 0.37
% 6.65/2.38  Parsing              : 0.20
% 6.65/2.38  CNF conversion       : 0.03
% 6.65/2.38  Main loop            : 1.19
% 6.65/2.38  Inferencing          : 0.34
% 6.65/2.38  Reduction            : 0.58
% 6.65/2.38  Demodulation         : 0.50
% 6.65/2.38  BG Simplification    : 0.05
% 6.65/2.38  Subsumption          : 0.15
% 6.65/2.38  Abstraction          : 0.07
% 6.65/2.38  MUC search           : 0.00
% 6.65/2.38  Cooper               : 0.00
% 6.65/2.38  Total                : 1.59
% 6.65/2.38  Index Insertion      : 0.00
% 6.65/2.38  Index Deletion       : 0.00
% 6.65/2.38  Index Matching       : 0.00
% 6.65/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
