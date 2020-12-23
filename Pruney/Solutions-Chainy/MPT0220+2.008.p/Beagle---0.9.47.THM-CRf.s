%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:04 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.19s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_319,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_337,plain,(
    ! [B_8] : k5_xboole_0(B_8,k1_xboole_0) = k2_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_319])).

tff(c_342,plain,(
    ! [B_82] : k5_xboole_0(B_82,k1_xboole_0) = B_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_337])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_348,plain,(
    ! [B_82] : k5_xboole_0(k1_xboole_0,B_82) = B_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_4])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_458,plain,(
    ! [A_88,B_89,C_90] : k5_xboole_0(k5_xboole_0(A_88,B_89),C_90) = k5_xboole_0(A_88,k5_xboole_0(B_89,C_90)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_861,plain,(
    ! [A_120,A_118,B_119] : k5_xboole_0(A_120,k5_xboole_0(A_118,B_119)) = k5_xboole_0(A_118,k5_xboole_0(B_119,A_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_458])).

tff(c_1047,plain,(
    ! [B_121,A_122] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_121,A_122)) = k5_xboole_0(A_122,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_861])).

tff(c_1109,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1047])).

tff(c_1135,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_1109])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_304,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_316,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_304])).

tff(c_1094,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_1047])).

tff(c_1132,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_1094])).

tff(c_18,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3693,plain,(
    ! [A_165,B_166,C_167] : k5_xboole_0(A_165,k5_xboole_0(k3_xboole_0(A_165,B_166),C_167)) = k5_xboole_0(k4_xboole_0(A_165,B_166),C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_458])).

tff(c_3842,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_3693])).

tff(c_3933,plain,(
    ! [B_168,A_169] : k2_xboole_0(B_168,A_169) = k2_xboole_0(A_169,B_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_24,c_3842])).

tff(c_40,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_159,plain,(
    ! [A_48,B_49] : k4_xboole_0(k1_tarski(A_48),k2_tarski(A_48,B_49)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_145])).

tff(c_1148,plain,(
    ! [B_130,A_131] : k5_xboole_0(k4_xboole_0(B_130,A_131),A_131) = k2_xboole_0(A_131,B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_1109])).

tff(c_1202,plain,(
    ! [A_48,B_49] : k2_xboole_0(k2_tarski(A_48,B_49),k1_tarski(A_48)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_1148])).

tff(c_1230,plain,(
    ! [A_48,B_49] : k2_xboole_0(k2_tarski(A_48,B_49),k1_tarski(A_48)) = k2_tarski(A_48,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_1202])).

tff(c_3948,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),k2_tarski(A_48,B_49)) = k2_tarski(A_48,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_3933,c_1230])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3948,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.20  
% 5.19/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.20  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.19/2.20  
% 5.19/2.20  %Foreground sorts:
% 5.19/2.20  
% 5.19/2.20  
% 5.19/2.20  %Background operators:
% 5.19/2.20  
% 5.19/2.20  
% 5.19/2.20  %Foreground operators:
% 5.19/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.19/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.19/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/2.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.19/2.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.19/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/2.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.19/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.19/2.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.19/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.19/2.20  tff('#skF_1', type, '#skF_1': $i).
% 5.19/2.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.19/2.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.19/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.19/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.19/2.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.19/2.20  
% 5.19/2.22  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.19/2.22  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.19/2.22  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.19/2.22  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.19/2.22  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.19/2.22  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.19/2.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.19/2.22  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.19/2.22  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 5.19/2.22  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 5.19/2.22  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.19/2.22  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.19/2.22  tff(c_145, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.19/2.22  tff(c_161, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_145])).
% 5.19/2.22  tff(c_319, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.19/2.22  tff(c_337, plain, (![B_8]: (k5_xboole_0(B_8, k1_xboole_0)=k2_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_161, c_319])).
% 5.19/2.22  tff(c_342, plain, (![B_82]: (k5_xboole_0(B_82, k1_xboole_0)=B_82)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_337])).
% 5.19/2.22  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.19/2.22  tff(c_348, plain, (![B_82]: (k5_xboole_0(k1_xboole_0, B_82)=B_82)), inference(superposition, [status(thm), theory('equality')], [c_342, c_4])).
% 5.19/2.22  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.19/2.22  tff(c_458, plain, (![A_88, B_89, C_90]: (k5_xboole_0(k5_xboole_0(A_88, B_89), C_90)=k5_xboole_0(A_88, k5_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.22  tff(c_861, plain, (![A_120, A_118, B_119]: (k5_xboole_0(A_120, k5_xboole_0(A_118, B_119))=k5_xboole_0(A_118, k5_xboole_0(B_119, A_120)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_458])).
% 5.19/2.22  tff(c_1047, plain, (![B_121, A_122]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_121, A_122))=k5_xboole_0(A_122, B_121))), inference(superposition, [status(thm), theory('equality')], [c_348, c_861])).
% 5.19/2.22  tff(c_1109, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1047])).
% 5.19/2.22  tff(c_1135, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_1109])).
% 5.19/2.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.19/2.22  tff(c_304, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.19/2.22  tff(c_316, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_304])).
% 5.19/2.22  tff(c_1094, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_316, c_1047])).
% 5.19/2.22  tff(c_1132, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_1094])).
% 5.19/2.22  tff(c_18, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.19/2.22  tff(c_3693, plain, (![A_165, B_166, C_167]: (k5_xboole_0(A_165, k5_xboole_0(k3_xboole_0(A_165, B_166), C_167))=k5_xboole_0(k4_xboole_0(A_165, B_166), C_167))), inference(superposition, [status(thm), theory('equality')], [c_18, c_458])).
% 5.19/2.22  tff(c_3842, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_1132, c_3693])).
% 5.19/2.22  tff(c_3933, plain, (![B_168, A_169]: (k2_xboole_0(B_168, A_169)=k2_xboole_0(A_169, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_1135, c_24, c_3842])).
% 5.19/2.22  tff(c_40, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.19/2.22  tff(c_159, plain, (![A_48, B_49]: (k4_xboole_0(k1_tarski(A_48), k2_tarski(A_48, B_49))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_145])).
% 5.19/2.22  tff(c_1148, plain, (![B_130, A_131]: (k5_xboole_0(k4_xboole_0(B_130, A_131), A_131)=k2_xboole_0(A_131, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_1109])).
% 5.19/2.22  tff(c_1202, plain, (![A_48, B_49]: (k2_xboole_0(k2_tarski(A_48, B_49), k1_tarski(A_48))=k5_xboole_0(k1_xboole_0, k2_tarski(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_1148])).
% 5.19/2.22  tff(c_1230, plain, (![A_48, B_49]: (k2_xboole_0(k2_tarski(A_48, B_49), k1_tarski(A_48))=k2_tarski(A_48, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_1202])).
% 5.19/2.22  tff(c_3948, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), k2_tarski(A_48, B_49))=k2_tarski(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_3933, c_1230])).
% 5.19/2.22  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.19/2.22  tff(c_4016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3948, c_42])).
% 5.19/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/2.22  
% 5.19/2.22  Inference rules
% 5.19/2.22  ----------------------
% 5.19/2.22  #Ref     : 0
% 5.19/2.22  #Sup     : 997
% 5.19/2.22  #Fact    : 0
% 5.19/2.22  #Define  : 0
% 5.19/2.22  #Split   : 0
% 5.19/2.22  #Chain   : 0
% 5.19/2.22  #Close   : 0
% 5.19/2.22  
% 5.19/2.22  Ordering : KBO
% 5.19/2.22  
% 5.19/2.22  Simplification rules
% 5.19/2.22  ----------------------
% 5.19/2.22  #Subsume      : 128
% 5.19/2.22  #Demod        : 595
% 5.19/2.22  #Tautology    : 353
% 5.19/2.22  #SimpNegUnit  : 0
% 5.19/2.22  #BackRed      : 1
% 5.19/2.22  
% 5.19/2.22  #Partial instantiations: 0
% 5.19/2.22  #Strategies tried      : 1
% 5.19/2.22  
% 5.19/2.22  Timing (in seconds)
% 5.19/2.22  ----------------------
% 5.34/2.22  Preprocessing        : 0.32
% 5.34/2.22  Parsing              : 0.15
% 5.34/2.22  CNF conversion       : 0.02
% 5.34/2.22  Main loop            : 1.05
% 5.34/2.22  Inferencing          : 0.26
% 5.34/2.22  Reduction            : 0.59
% 5.34/2.22  Demodulation         : 0.53
% 5.34/2.22  BG Simplification    : 0.04
% 5.34/2.22  Subsumption          : 0.11
% 5.34/2.22  Abstraction          : 0.06
% 5.34/2.22  MUC search           : 0.00
% 5.34/2.22  Cooper               : 0.00
% 5.34/2.22  Total                : 1.41
% 5.34/2.22  Index Insertion      : 0.00
% 5.34/2.22  Index Deletion       : 0.00
% 5.34/2.22  Index Matching       : 0.00
% 5.34/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
