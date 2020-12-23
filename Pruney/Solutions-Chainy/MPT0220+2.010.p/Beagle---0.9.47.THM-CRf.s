%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:05 EST 2020

% Result     : Theorem 6.56s
% Output     : CNFRefutation 6.76s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 170 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :   46 ( 181 expanded)
%              Number of equality atoms :   38 ( 141 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_147,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_135])).

tff(c_175,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k4_xboole_0(B_69,A_68)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_187,plain,(
    ! [B_8] : k5_xboole_0(B_8,k1_xboole_0) = k2_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_175])).

tff(c_192,plain,(
    ! [B_70] : k5_xboole_0(B_70,k1_xboole_0) = B_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_187])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_198,plain,(
    ! [B_70] : k5_xboole_0(k1_xboole_0,B_70) = B_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_4])).

tff(c_40,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,(
    ! [A_48,B_49] : k4_xboole_0(k1_tarski(A_48),k2_tarski(A_48,B_49)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_135])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_547,plain,(
    ! [A_89,B_90,C_91] : k5_xboole_0(k5_xboole_0(A_89,B_90),C_91) = k5_xboole_0(A_89,k5_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1463,plain,(
    ! [A_136,A_134,B_135] : k5_xboole_0(A_136,k5_xboole_0(A_134,B_135)) = k5_xboole_0(A_134,k5_xboole_0(B_135,A_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_547])).

tff(c_1926,plain,(
    ! [B_139,A_140] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_139,A_140)) = k5_xboole_0(A_140,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_1463])).

tff(c_2034,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1926])).

tff(c_2506,plain,(
    ! [B_148,A_149] : k5_xboole_0(k4_xboole_0(B_148,A_149),A_149) = k2_xboole_0(A_149,B_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_2034])).

tff(c_2578,plain,(
    ! [A_48,B_49] : k2_xboole_0(k2_tarski(A_48,B_49),k1_tarski(A_48)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_2506])).

tff(c_8982,plain,(
    ! [A_234,B_235] : k2_xboole_0(k2_tarski(A_234,B_235),k1_tarski(A_234)) = k2_tarski(A_234,B_235) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_2578])).

tff(c_2068,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_2034])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_284,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_301,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_284])).

tff(c_2019,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_1926])).

tff(c_2064,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_2019])).

tff(c_18,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4724,plain,(
    ! [A_187,B_188,C_189] : k5_xboole_0(A_187,k5_xboole_0(k3_xboole_0(A_187,B_188),C_189)) = k5_xboole_0(k4_xboole_0(A_187,B_188),C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_547])).

tff(c_4839,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2064,c_4724])).

tff(c_4936,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2068,c_24,c_4839])).

tff(c_9012,plain,(
    ! [A_234,B_235] : k2_xboole_0(k1_tarski(A_234),k2_tarski(A_234,B_235)) = k2_tarski(A_234,B_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_8982,c_4936])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9012,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.56/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.56  
% 6.56/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.56  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.56/2.56  
% 6.56/2.56  %Foreground sorts:
% 6.56/2.56  
% 6.56/2.56  
% 6.56/2.56  %Background operators:
% 6.56/2.56  
% 6.56/2.56  
% 6.56/2.56  %Foreground operators:
% 6.56/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.56/2.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.56/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.56/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.56/2.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.56/2.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.56/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.56/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.56/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.56/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.56/2.56  tff('#skF_2', type, '#skF_2': $i).
% 6.56/2.56  tff('#skF_1', type, '#skF_1': $i).
% 6.56/2.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.56/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.56/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.56/2.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.56/2.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.56  
% 6.76/2.57  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.76/2.57  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.76/2.57  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.76/2.57  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.76/2.57  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.76/2.57  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 6.76/2.57  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.76/2.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.76/2.57  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.76/2.57  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 6.76/2.57  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.76/2.57  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.76/2.57  tff(c_135, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.76/2.57  tff(c_147, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_135])).
% 6.76/2.57  tff(c_175, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k4_xboole_0(B_69, A_68))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.76/2.57  tff(c_187, plain, (![B_8]: (k5_xboole_0(B_8, k1_xboole_0)=k2_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_147, c_175])).
% 6.76/2.57  tff(c_192, plain, (![B_70]: (k5_xboole_0(B_70, k1_xboole_0)=B_70)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_187])).
% 6.76/2.57  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.76/2.57  tff(c_198, plain, (![B_70]: (k5_xboole_0(k1_xboole_0, B_70)=B_70)), inference(superposition, [status(thm), theory('equality')], [c_192, c_4])).
% 6.76/2.57  tff(c_40, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.76/2.57  tff(c_146, plain, (![A_48, B_49]: (k4_xboole_0(k1_tarski(A_48), k2_tarski(A_48, B_49))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_135])).
% 6.76/2.57  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.76/2.57  tff(c_547, plain, (![A_89, B_90, C_91]: (k5_xboole_0(k5_xboole_0(A_89, B_90), C_91)=k5_xboole_0(A_89, k5_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.76/2.57  tff(c_1463, plain, (![A_136, A_134, B_135]: (k5_xboole_0(A_136, k5_xboole_0(A_134, B_135))=k5_xboole_0(A_134, k5_xboole_0(B_135, A_136)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_547])).
% 6.76/2.57  tff(c_1926, plain, (![B_139, A_140]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_139, A_140))=k5_xboole_0(A_140, B_139))), inference(superposition, [status(thm), theory('equality')], [c_198, c_1463])).
% 6.76/2.57  tff(c_2034, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1926])).
% 6.76/2.57  tff(c_2506, plain, (![B_148, A_149]: (k5_xboole_0(k4_xboole_0(B_148, A_149), A_149)=k2_xboole_0(A_149, B_148))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_2034])).
% 6.76/2.57  tff(c_2578, plain, (![A_48, B_49]: (k2_xboole_0(k2_tarski(A_48, B_49), k1_tarski(A_48))=k5_xboole_0(k1_xboole_0, k2_tarski(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_2506])).
% 6.76/2.57  tff(c_8982, plain, (![A_234, B_235]: (k2_xboole_0(k2_tarski(A_234, B_235), k1_tarski(A_234))=k2_tarski(A_234, B_235))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_2578])).
% 6.76/2.57  tff(c_2068, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_2034])).
% 6.76/2.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.76/2.57  tff(c_284, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.76/2.57  tff(c_301, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_284])).
% 6.76/2.57  tff(c_2019, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_301, c_1926])).
% 6.76/2.57  tff(c_2064, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_2019])).
% 6.76/2.57  tff(c_18, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.76/2.57  tff(c_4724, plain, (![A_187, B_188, C_189]: (k5_xboole_0(A_187, k5_xboole_0(k3_xboole_0(A_187, B_188), C_189))=k5_xboole_0(k4_xboole_0(A_187, B_188), C_189))), inference(superposition, [status(thm), theory('equality')], [c_18, c_547])).
% 6.76/2.57  tff(c_4839, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2064, c_4724])).
% 6.76/2.57  tff(c_4936, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2068, c_24, c_4839])).
% 6.76/2.57  tff(c_9012, plain, (![A_234, B_235]: (k2_xboole_0(k1_tarski(A_234), k2_tarski(A_234, B_235))=k2_tarski(A_234, B_235))), inference(superposition, [status(thm), theory('equality')], [c_8982, c_4936])).
% 6.76/2.57  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.76/2.57  tff(c_9051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9012, c_42])).
% 6.76/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.57  
% 6.76/2.57  Inference rules
% 6.76/2.57  ----------------------
% 6.76/2.57  #Ref     : 0
% 6.76/2.57  #Sup     : 2242
% 6.76/2.57  #Fact    : 0
% 6.76/2.57  #Define  : 0
% 6.76/2.57  #Split   : 0
% 6.76/2.57  #Chain   : 0
% 6.76/2.57  #Close   : 0
% 6.76/2.57  
% 6.76/2.57  Ordering : KBO
% 6.76/2.57  
% 6.76/2.57  Simplification rules
% 6.76/2.57  ----------------------
% 6.76/2.57  #Subsume      : 108
% 6.76/2.57  #Demod        : 2436
% 6.76/2.57  #Tautology    : 1248
% 6.76/2.57  #SimpNegUnit  : 0
% 6.76/2.57  #BackRed      : 9
% 6.76/2.57  
% 6.76/2.57  #Partial instantiations: 0
% 6.76/2.57  #Strategies tried      : 1
% 6.76/2.57  
% 6.76/2.57  Timing (in seconds)
% 6.76/2.57  ----------------------
% 6.76/2.57  Preprocessing        : 0.31
% 6.76/2.57  Parsing              : 0.16
% 6.76/2.57  CNF conversion       : 0.02
% 6.76/2.57  Main loop            : 1.47
% 6.76/2.57  Inferencing          : 0.36
% 6.76/2.57  Reduction            : 0.83
% 6.76/2.57  Demodulation         : 0.74
% 6.76/2.57  BG Simplification    : 0.05
% 6.76/2.57  Subsumption          : 0.17
% 6.76/2.57  Abstraction          : 0.08
% 6.76/2.57  MUC search           : 0.00
% 6.76/2.57  Cooper               : 0.00
% 6.76/2.58  Total                : 1.81
% 6.76/2.58  Index Insertion      : 0.00
% 6.76/2.58  Index Deletion       : 0.00
% 6.76/2.58  Index Matching       : 0.00
% 6.76/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
