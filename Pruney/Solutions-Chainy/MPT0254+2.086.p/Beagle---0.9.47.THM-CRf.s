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
% DateTime   : Thu Dec  3 09:51:30 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 240 expanded)
%              Number of leaves         :   32 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 ( 248 expanded)
%              Number of equality atoms :   51 ( 215 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_417,plain,(
    ! [A_87,B_88,C_89] : k5_xboole_0(k5_xboole_0(A_87,B_88),C_89) = k5_xboole_0(A_87,k5_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2892,plain,(
    ! [A_152,B_153,C_154] : k5_xboole_0(k5_xboole_0(A_152,B_153),C_154) = k5_xboole_0(B_153,k5_xboole_0(A_152,C_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_417])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2961,plain,(
    ! [B_153,A_152] : k5_xboole_0(B_153,k5_xboole_0(A_152,k3_xboole_0(A_152,B_153))) = k2_xboole_0(A_152,B_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_2892,c_24])).

tff(c_3216,plain,(
    ! [B_155,A_156] : k5_xboole_0(B_155,k4_xboole_0(A_156,B_155)) = k2_xboole_0(A_156,B_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2961])).

tff(c_130,plain,(
    ! [B_59,A_60] : k5_xboole_0(B_59,A_60) = k5_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_146,plain,(
    ! [A_60] : k5_xboole_0(k1_xboole_0,A_60) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_18])).

tff(c_22,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_481,plain,(
    ! [A_17,C_89] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_89)) = k5_xboole_0(k1_xboole_0,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_417])).

tff(c_494,plain,(
    ! [A_17,C_89] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_89)) = C_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_481])).

tff(c_4714,plain,(
    ! [B_178,A_179] : k5_xboole_0(B_178,k2_xboole_0(A_179,B_178)) = k4_xboole_0(A_179,B_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_3216,c_494])).

tff(c_4802,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4714])).

tff(c_4817,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4802])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4851,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4817,c_16])).

tff(c_4861,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4851])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_274,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_297,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_274])).

tff(c_300,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_297])).

tff(c_42,plain,(
    ! [B_51] : k4_xboole_0(k1_tarski(B_51),k1_tarski(B_51)) != k1_tarski(B_51) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_310,plain,(
    ! [B_51] : k1_tarski(B_51) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_42])).

tff(c_4887,plain,(
    ! [B_51] : k1_tarski(B_51) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4861,c_310])).

tff(c_4892,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_2') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4861,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_990,plain,(
    ! [B_111,A_112] : k5_xboole_0(B_111,k3_xboole_0(A_112,B_111)) = k4_xboole_0(B_111,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_274])).

tff(c_1008,plain,(
    ! [B_111,A_112] : k5_xboole_0(B_111,k4_xboole_0(B_111,A_112)) = k3_xboole_0(A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_494])).

tff(c_4845,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k3_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4817,c_1008])).

tff(c_5561,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4892,c_4845])).

tff(c_329,plain,(
    ! [B_80] : k4_xboole_0(k1_xboole_0,B_80) = k3_xboole_0(k1_xboole_0,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_274])).

tff(c_339,plain,(
    ! [B_80] :
      ( k1_xboole_0 = B_80
      | ~ r1_tarski(B_80,k3_xboole_0(k1_xboole_0,B_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_16])).

tff(c_6535,plain,(
    ! [B_198] :
      ( B_198 = '#skF_2'
      | ~ r1_tarski(B_198,k3_xboole_0('#skF_2',B_198)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4861,c_4861,c_339])).

tff(c_6538,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5561,c_6535])).

tff(c_6552,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6538])).

tff(c_6554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4887,c_6552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.27  
% 5.89/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.27  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.89/2.27  
% 5.89/2.27  %Foreground sorts:
% 5.89/2.27  
% 5.89/2.27  
% 5.89/2.27  %Background operators:
% 5.89/2.27  
% 5.89/2.27  
% 5.89/2.27  %Foreground operators:
% 5.89/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.89/2.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.89/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.89/2.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.89/2.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.89/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.89/2.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.89/2.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.89/2.27  tff('#skF_2', type, '#skF_2': $i).
% 5.89/2.27  tff('#skF_1', type, '#skF_1': $i).
% 5.89/2.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.89/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.89/2.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.89/2.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.27  
% 5.89/2.28  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.89/2.28  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.89/2.28  tff(f_76, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.89/2.28  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.89/2.28  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.89/2.28  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.89/2.28  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.89/2.28  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.89/2.28  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 5.89/2.28  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.89/2.28  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 5.89/2.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.89/2.28  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.89/2.28  tff(c_18, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.89/2.28  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.89/2.28  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.89/2.28  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.89/2.28  tff(c_417, plain, (![A_87, B_88, C_89]: (k5_xboole_0(k5_xboole_0(A_87, B_88), C_89)=k5_xboole_0(A_87, k5_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.89/2.28  tff(c_2892, plain, (![A_152, B_153, C_154]: (k5_xboole_0(k5_xboole_0(A_152, B_153), C_154)=k5_xboole_0(B_153, k5_xboole_0(A_152, C_154)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_417])).
% 5.89/2.28  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.89/2.28  tff(c_2961, plain, (![B_153, A_152]: (k5_xboole_0(B_153, k5_xboole_0(A_152, k3_xboole_0(A_152, B_153)))=k2_xboole_0(A_152, B_153))), inference(superposition, [status(thm), theory('equality')], [c_2892, c_24])).
% 5.89/2.28  tff(c_3216, plain, (![B_155, A_156]: (k5_xboole_0(B_155, k4_xboole_0(A_156, B_155))=k2_xboole_0(A_156, B_155))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2961])).
% 5.89/2.28  tff(c_130, plain, (![B_59, A_60]: (k5_xboole_0(B_59, A_60)=k5_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.89/2.28  tff(c_146, plain, (![A_60]: (k5_xboole_0(k1_xboole_0, A_60)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_130, c_18])).
% 5.89/2.28  tff(c_22, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.89/2.28  tff(c_481, plain, (![A_17, C_89]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_89))=k5_xboole_0(k1_xboole_0, C_89))), inference(superposition, [status(thm), theory('equality')], [c_22, c_417])).
% 5.89/2.28  tff(c_494, plain, (![A_17, C_89]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_89))=C_89)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_481])).
% 5.89/2.28  tff(c_4714, plain, (![B_178, A_179]: (k5_xboole_0(B_178, k2_xboole_0(A_179, B_178))=k4_xboole_0(A_179, B_178))), inference(superposition, [status(thm), theory('equality')], [c_3216, c_494])).
% 5.89/2.28  tff(c_4802, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_4714])).
% 5.89/2.28  tff(c_4817, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4802])).
% 5.89/2.28  tff(c_16, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.89/2.28  tff(c_4851, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4817, c_16])).
% 5.89/2.28  tff(c_4861, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4851])).
% 5.89/2.28  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.89/2.28  tff(c_274, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.89/2.28  tff(c_297, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_274])).
% 5.89/2.28  tff(c_300, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_297])).
% 5.89/2.28  tff(c_42, plain, (![B_51]: (k4_xboole_0(k1_tarski(B_51), k1_tarski(B_51))!=k1_tarski(B_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.89/2.28  tff(c_310, plain, (![B_51]: (k1_tarski(B_51)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_300, c_42])).
% 5.89/2.28  tff(c_4887, plain, (![B_51]: (k1_tarski(B_51)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4861, c_310])).
% 5.89/2.28  tff(c_4892, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_2')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_4861, c_18])).
% 5.89/2.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.89/2.28  tff(c_990, plain, (![B_111, A_112]: (k5_xboole_0(B_111, k3_xboole_0(A_112, B_111))=k4_xboole_0(B_111, A_112))), inference(superposition, [status(thm), theory('equality')], [c_2, c_274])).
% 5.89/2.28  tff(c_1008, plain, (![B_111, A_112]: (k5_xboole_0(B_111, k4_xboole_0(B_111, A_112))=k3_xboole_0(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_990, c_494])).
% 5.89/2.28  tff(c_4845, plain, (k5_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k3_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4817, c_1008])).
% 5.89/2.28  tff(c_5561, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4892, c_4845])).
% 5.89/2.28  tff(c_329, plain, (![B_80]: (k4_xboole_0(k1_xboole_0, B_80)=k3_xboole_0(k1_xboole_0, B_80))), inference(superposition, [status(thm), theory('equality')], [c_146, c_274])).
% 5.89/2.28  tff(c_339, plain, (![B_80]: (k1_xboole_0=B_80 | ~r1_tarski(B_80, k3_xboole_0(k1_xboole_0, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_329, c_16])).
% 5.89/2.28  tff(c_6535, plain, (![B_198]: (B_198='#skF_2' | ~r1_tarski(B_198, k3_xboole_0('#skF_2', B_198)))), inference(demodulation, [status(thm), theory('equality')], [c_4861, c_4861, c_339])).
% 5.89/2.28  tff(c_6538, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5561, c_6535])).
% 5.89/2.28  tff(c_6552, plain, (k1_tarski('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6538])).
% 5.89/2.28  tff(c_6554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4887, c_6552])).
% 5.89/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.28  
% 5.89/2.28  Inference rules
% 5.89/2.28  ----------------------
% 5.89/2.28  #Ref     : 0
% 5.89/2.28  #Sup     : 1625
% 5.89/2.28  #Fact    : 0
% 5.89/2.28  #Define  : 0
% 5.89/2.28  #Split   : 0
% 5.89/2.28  #Chain   : 0
% 5.89/2.28  #Close   : 0
% 5.89/2.28  
% 5.89/2.28  Ordering : KBO
% 5.89/2.28  
% 5.89/2.28  Simplification rules
% 5.89/2.28  ----------------------
% 5.89/2.28  #Subsume      : 86
% 5.89/2.28  #Demod        : 1242
% 5.89/2.28  #Tautology    : 834
% 5.89/2.28  #SimpNegUnit  : 8
% 5.89/2.28  #BackRed      : 33
% 5.89/2.28  
% 5.89/2.28  #Partial instantiations: 0
% 5.89/2.28  #Strategies tried      : 1
% 5.89/2.28  
% 5.89/2.28  Timing (in seconds)
% 5.89/2.28  ----------------------
% 5.89/2.29  Preprocessing        : 0.33
% 5.89/2.29  Parsing              : 0.18
% 5.89/2.29  CNF conversion       : 0.02
% 5.89/2.29  Main loop            : 1.18
% 5.89/2.29  Inferencing          : 0.33
% 5.89/2.29  Reduction            : 0.59
% 5.89/2.29  Demodulation         : 0.52
% 5.89/2.29  BG Simplification    : 0.05
% 5.89/2.29  Subsumption          : 0.15
% 5.89/2.29  Abstraction          : 0.06
% 5.89/2.29  MUC search           : 0.00
% 5.89/2.29  Cooper               : 0.00
% 5.89/2.29  Total                : 1.54
% 5.89/2.29  Index Insertion      : 0.00
% 5.89/2.29  Index Deletion       : 0.00
% 5.89/2.29  Index Matching       : 0.00
% 5.89/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
