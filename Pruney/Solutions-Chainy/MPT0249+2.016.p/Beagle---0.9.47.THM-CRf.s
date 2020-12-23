%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:25 EST 2020

% Result     : Theorem 9.54s
% Output     : CNFRefutation 9.62s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 147 expanded)
%              Number of leaves         :   37 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 224 expanded)
%              Number of equality atoms :   54 ( 128 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_58,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1081,plain,(
    ! [A_128,B_129,C_130] :
      ( r1_tarski(k2_tarski(A_128,B_129),C_130)
      | ~ r2_hidden(B_129,C_130)
      | ~ r2_hidden(A_128,C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6726,plain,(
    ! [A_196,C_197] :
      ( r1_tarski(k1_tarski(A_196),C_197)
      | ~ r2_hidden(A_196,C_197)
      | ~ r2_hidden(A_196,C_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1081])).

tff(c_60,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_206,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_213,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_206])).

tff(c_219,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_6739,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6726,c_219])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1806,plain,(
    ! [A_145,B_146,C_147] :
      ( k1_xboole_0 = A_145
      | ~ r1_xboole_0(B_146,C_147)
      | ~ r1_tarski(A_145,C_147)
      | ~ r1_tarski(A_145,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9979,plain,(
    ! [A_222,B_223,A_224] :
      ( k1_xboole_0 = A_222
      | ~ r1_tarski(A_222,B_223)
      | ~ r1_tarski(A_222,k1_tarski(A_224))
      | r2_hidden(A_224,B_223) ) ),
    inference(resolution,[status(thm)],[c_44,c_1806])).

tff(c_9998,plain,(
    ! [B_226,A_227] :
      ( k1_xboole_0 = B_226
      | ~ r1_tarski(B_226,k1_tarski(A_227))
      | r2_hidden(A_227,B_226) ) ),
    inference(resolution,[status(thm)],[c_16,c_9979])).

tff(c_10009,plain,
    ( k1_xboole_0 = '#skF_2'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_9998])).

tff(c_10019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6739,c_56,c_10009])).

tff(c_10020,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_10024,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10020,c_60])).

tff(c_196,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = k1_xboole_0
      | ~ r1_xboole_0(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10879,plain,(
    ! [A_277,B_278] :
      ( k3_xboole_0(k1_tarski(A_277),B_278) = k1_xboole_0
      | r2_hidden(A_277,B_278) ) ),
    inference(resolution,[status(thm)],[c_44,c_196])).

tff(c_10900,plain,(
    ! [B_278] :
      ( k3_xboole_0('#skF_2',B_278) = k1_xboole_0
      | r2_hidden('#skF_1',B_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10020,c_10879])).

tff(c_10759,plain,(
    ! [A_270,B_271,C_272] :
      ( r1_tarski(k2_tarski(A_270,B_271),C_272)
      | ~ r2_hidden(B_271,C_272)
      | ~ r2_hidden(A_270,C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14400,plain,(
    ! [A_339,C_340] :
      ( r1_tarski(k1_tarski(A_339),C_340)
      | ~ r2_hidden(A_339,C_340)
      | ~ r2_hidden(A_339,C_340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_10759])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14415,plain,(
    ! [A_341,C_342] :
      ( k2_xboole_0(k1_tarski(A_341),C_342) = C_342
      | ~ r2_hidden(A_341,C_342) ) ),
    inference(resolution,[status(thm)],[c_14400,c_18])).

tff(c_14816,plain,(
    ! [C_348] :
      ( k2_xboole_0('#skF_2',C_348) = C_348
      | ~ r2_hidden('#skF_1',C_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10020,c_14415])).

tff(c_15056,plain,(
    ! [B_358] :
      ( k2_xboole_0('#skF_2',B_358) = B_358
      | k3_xboole_0('#skF_2',B_358) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10900,c_14816])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10135,plain,(
    ! [A_249,B_250] : k5_xboole_0(k5_xboole_0(A_249,B_250),k2_xboole_0(A_249,B_250)) = k3_xboole_0(A_249,B_250) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10171,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,A_5),A_5) = k3_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_10135])).

tff(c_10178,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10,c_10171])).

tff(c_10297,plain,(
    ! [A_259,B_260,C_261] : k5_xboole_0(k5_xboole_0(A_259,B_260),C_261) = k5_xboole_0(A_259,k5_xboole_0(B_260,C_261)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10366,plain,(
    ! [A_21,C_261] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_261)) = k5_xboole_0(k1_xboole_0,C_261) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_10297])).

tff(c_10381,plain,(
    ! [A_262,C_263] : k5_xboole_0(A_262,k5_xboole_0(A_262,C_263)) = C_263 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10178,c_10366])).

tff(c_10433,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10381])).

tff(c_10156,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10024,c_10135])).

tff(c_10177,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_10156])).

tff(c_10452,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10433,c_10177])).

tff(c_15097,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_15056,c_10452])).

tff(c_15136,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10024,c_15097])).

tff(c_15138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_15136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:14:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.54/3.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.63  
% 9.62/3.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.62/3.63  
% 9.62/3.63  %Foreground sorts:
% 9.62/3.63  
% 9.62/3.63  
% 9.62/3.63  %Background operators:
% 9.62/3.63  
% 9.62/3.63  
% 9.62/3.63  %Foreground operators:
% 9.62/3.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.62/3.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.62/3.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.62/3.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.62/3.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.62/3.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.62/3.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.62/3.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.62/3.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.62/3.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.62/3.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.62/3.63  tff('#skF_2', type, '#skF_2': $i).
% 9.62/3.63  tff('#skF_3', type, '#skF_3': $i).
% 9.62/3.63  tff('#skF_1', type, '#skF_1': $i).
% 9.62/3.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.62/3.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.62/3.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.62/3.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.62/3.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.62/3.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.62/3.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.62/3.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.62/3.63  
% 9.62/3.65  tff(f_101, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 9.62/3.65  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.62/3.65  tff(f_88, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 9.62/3.65  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.62/3.65  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.62/3.65  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.62/3.65  tff(f_53, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 9.62/3.65  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.62/3.65  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.62/3.65  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.62/3.65  tff(f_59, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.62/3.65  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.62/3.65  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.62/3.65  tff(f_61, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.62/3.65  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.62/3.65  tff(c_58, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.62/3.65  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.62/3.65  tff(c_30, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.62/3.65  tff(c_1081, plain, (![A_128, B_129, C_130]: (r1_tarski(k2_tarski(A_128, B_129), C_130) | ~r2_hidden(B_129, C_130) | ~r2_hidden(A_128, C_130))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.62/3.65  tff(c_6726, plain, (![A_196, C_197]: (r1_tarski(k1_tarski(A_196), C_197) | ~r2_hidden(A_196, C_197) | ~r2_hidden(A_196, C_197))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1081])).
% 9.62/3.65  tff(c_60, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.62/3.65  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.62/3.65  tff(c_96, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_22])).
% 9.62/3.65  tff(c_206, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.62/3.65  tff(c_213, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_96, c_206])).
% 9.62/3.65  tff(c_219, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_213])).
% 9.62/3.65  tff(c_6739, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6726, c_219])).
% 9.62/3.65  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.62/3.65  tff(c_16, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.62/3.65  tff(c_44, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.62/3.65  tff(c_1806, plain, (![A_145, B_146, C_147]: (k1_xboole_0=A_145 | ~r1_xboole_0(B_146, C_147) | ~r1_tarski(A_145, C_147) | ~r1_tarski(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.62/3.65  tff(c_9979, plain, (![A_222, B_223, A_224]: (k1_xboole_0=A_222 | ~r1_tarski(A_222, B_223) | ~r1_tarski(A_222, k1_tarski(A_224)) | r2_hidden(A_224, B_223))), inference(resolution, [status(thm)], [c_44, c_1806])).
% 9.62/3.65  tff(c_9998, plain, (![B_226, A_227]: (k1_xboole_0=B_226 | ~r1_tarski(B_226, k1_tarski(A_227)) | r2_hidden(A_227, B_226))), inference(resolution, [status(thm)], [c_16, c_9979])).
% 9.62/3.65  tff(c_10009, plain, (k1_xboole_0='#skF_2' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_9998])).
% 9.62/3.65  tff(c_10019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6739, c_56, c_10009])).
% 9.62/3.65  tff(c_10020, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_213])).
% 9.62/3.65  tff(c_10024, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10020, c_60])).
% 9.62/3.65  tff(c_196, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=k1_xboole_0 | ~r1_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.62/3.65  tff(c_10879, plain, (![A_277, B_278]: (k3_xboole_0(k1_tarski(A_277), B_278)=k1_xboole_0 | r2_hidden(A_277, B_278))), inference(resolution, [status(thm)], [c_44, c_196])).
% 9.62/3.65  tff(c_10900, plain, (![B_278]: (k3_xboole_0('#skF_2', B_278)=k1_xboole_0 | r2_hidden('#skF_1', B_278))), inference(superposition, [status(thm), theory('equality')], [c_10020, c_10879])).
% 9.62/3.65  tff(c_10759, plain, (![A_270, B_271, C_272]: (r1_tarski(k2_tarski(A_270, B_271), C_272) | ~r2_hidden(B_271, C_272) | ~r2_hidden(A_270, C_272))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.62/3.65  tff(c_14400, plain, (![A_339, C_340]: (r1_tarski(k1_tarski(A_339), C_340) | ~r2_hidden(A_339, C_340) | ~r2_hidden(A_339, C_340))), inference(superposition, [status(thm), theory('equality')], [c_30, c_10759])).
% 9.62/3.65  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.62/3.65  tff(c_14415, plain, (![A_341, C_342]: (k2_xboole_0(k1_tarski(A_341), C_342)=C_342 | ~r2_hidden(A_341, C_342))), inference(resolution, [status(thm)], [c_14400, c_18])).
% 9.62/3.65  tff(c_14816, plain, (![C_348]: (k2_xboole_0('#skF_2', C_348)=C_348 | ~r2_hidden('#skF_1', C_348))), inference(superposition, [status(thm), theory('equality')], [c_10020, c_14415])).
% 9.62/3.65  tff(c_15056, plain, (![B_358]: (k2_xboole_0('#skF_2', B_358)=B_358 | k3_xboole_0('#skF_2', B_358)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10900, c_14816])).
% 9.62/3.65  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.62/3.65  tff(c_26, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.62/3.65  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.62/3.65  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.62/3.65  tff(c_10135, plain, (![A_249, B_250]: (k5_xboole_0(k5_xboole_0(A_249, B_250), k2_xboole_0(A_249, B_250))=k3_xboole_0(A_249, B_250))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.62/3.65  tff(c_10171, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, A_5), A_5)=k3_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_10135])).
% 9.62/3.65  tff(c_10178, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10, c_10171])).
% 9.62/3.65  tff(c_10297, plain, (![A_259, B_260, C_261]: (k5_xboole_0(k5_xboole_0(A_259, B_260), C_261)=k5_xboole_0(A_259, k5_xboole_0(B_260, C_261)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.62/3.65  tff(c_10366, plain, (![A_21, C_261]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_261))=k5_xboole_0(k1_xboole_0, C_261))), inference(superposition, [status(thm), theory('equality')], [c_26, c_10297])).
% 9.62/3.65  tff(c_10381, plain, (![A_262, C_263]: (k5_xboole_0(A_262, k5_xboole_0(A_262, C_263))=C_263)), inference(demodulation, [status(thm), theory('equality')], [c_10178, c_10366])).
% 9.62/3.65  tff(c_10433, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_10381])).
% 9.62/3.65  tff(c_10156, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10024, c_10135])).
% 9.62/3.65  tff(c_10177, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_10156])).
% 9.62/3.65  tff(c_10452, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10433, c_10177])).
% 9.62/3.65  tff(c_15097, plain, (k1_xboole_0='#skF_3' | k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_15056, c_10452])).
% 9.62/3.65  tff(c_15136, plain, (k1_xboole_0='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10024, c_15097])).
% 9.62/3.65  tff(c_15138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_15136])).
% 9.62/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.65  
% 9.62/3.65  Inference rules
% 9.62/3.65  ----------------------
% 9.62/3.65  #Ref     : 0
% 9.62/3.65  #Sup     : 3892
% 9.62/3.65  #Fact    : 0
% 9.62/3.65  #Define  : 0
% 9.62/3.65  #Split   : 2
% 9.62/3.65  #Chain   : 0
% 9.62/3.65  #Close   : 0
% 9.62/3.65  
% 9.62/3.65  Ordering : KBO
% 9.62/3.65  
% 9.62/3.65  Simplification rules
% 9.62/3.65  ----------------------
% 9.62/3.65  #Subsume      : 177
% 9.62/3.65  #Demod        : 3909
% 9.62/3.65  #Tautology    : 1811
% 9.62/3.65  #SimpNegUnit  : 11
% 9.62/3.65  #BackRed      : 6
% 9.62/3.65  
% 9.62/3.65  #Partial instantiations: 0
% 9.62/3.65  #Strategies tried      : 1
% 9.62/3.65  
% 9.62/3.65  Timing (in seconds)
% 9.62/3.65  ----------------------
% 9.62/3.65  Preprocessing        : 0.33
% 9.62/3.65  Parsing              : 0.18
% 9.62/3.65  CNF conversion       : 0.02
% 9.62/3.65  Main loop            : 2.56
% 9.62/3.65  Inferencing          : 0.54
% 9.62/3.65  Reduction            : 1.48
% 9.62/3.65  Demodulation         : 1.32
% 9.62/3.65  BG Simplification    : 0.08
% 9.62/3.65  Subsumption          : 0.34
% 9.62/3.65  Abstraction          : 0.10
% 9.62/3.65  MUC search           : 0.00
% 9.62/3.65  Cooper               : 0.00
% 9.62/3.65  Total                : 2.93
% 9.62/3.65  Index Insertion      : 0.00
% 9.62/3.65  Index Deletion       : 0.00
% 9.62/3.65  Index Matching       : 0.00
% 9.62/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
