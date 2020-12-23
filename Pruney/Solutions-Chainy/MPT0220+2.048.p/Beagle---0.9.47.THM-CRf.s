%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:10 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   42 (  90 expanded)
%              Number of equality atoms :   34 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_28,plain,(
    ! [A_14] : k2_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_127,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_127])).

tff(c_208,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k4_xboole_0(B_74,A_73)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_220,plain,(
    ! [B_17] : k5_xboole_0(B_17,k1_xboole_0) = k2_xboole_0(B_17,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_208])).

tff(c_225,plain,(
    ! [B_75] : k5_xboole_0(B_75,k1_xboole_0) = B_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_220])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_231,plain,(
    ! [B_75] : k5_xboole_0(k1_xboole_0,B_75) = B_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_2])).

tff(c_56,plain,(
    ! [A_39,B_40] : r1_tarski(k1_tarski(A_39),k2_tarski(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_138,plain,(
    ! [A_39,B_40] : k4_xboole_0(k1_tarski(A_39),k2_tarski(A_39,B_40)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_127])).

tff(c_46,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_443,plain,(
    ! [A_90,B_91,C_92] : k5_xboole_0(k5_xboole_0(A_90,B_91),C_92) = k5_xboole_0(A_90,k5_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1185,plain,(
    ! [A_135,A_133,B_134] : k5_xboole_0(A_135,k5_xboole_0(A_133,B_134)) = k5_xboole_0(A_133,k5_xboole_0(B_134,A_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_443])).

tff(c_1411,plain,(
    ! [B_136,A_137] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_136,A_137)) = k5_xboole_0(A_137,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_1185])).

tff(c_1496,plain,(
    ! [B_28,A_27] : k5_xboole_0(k4_xboole_0(B_28,A_27),A_27) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1411])).

tff(c_1613,plain,(
    ! [B_139,A_140] : k5_xboole_0(k4_xboole_0(B_139,A_140),A_140) = k2_xboole_0(A_140,B_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_1496])).

tff(c_1676,plain,(
    ! [A_39,B_40] : k2_xboole_0(k2_tarski(A_39,B_40),k1_tarski(A_39)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_1613])).

tff(c_1841,plain,(
    ! [A_146,B_147] : k2_xboole_0(k2_tarski(A_146,B_147),k1_tarski(A_146)) = k2_tarski(A_146,B_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_1676])).

tff(c_40,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_619,plain,(
    ! [A_98,B_99] : k5_xboole_0(k5_xboole_0(A_98,B_99),k3_xboole_0(A_98,B_99)) = k2_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_889,plain,(
    ! [B_119,A_120] : k5_xboole_0(k5_xboole_0(B_119,A_120),k3_xboole_0(A_120,B_119)) = k2_xboole_0(A_120,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_619])).

tff(c_42,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_908,plain,(
    ! [B_119,A_120] : k5_xboole_0(B_119,k5_xboole_0(A_120,k3_xboole_0(A_120,B_119))) = k2_xboole_0(A_120,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_42])).

tff(c_967,plain,(
    ! [B_119,A_120] : k2_xboole_0(B_119,A_120) = k2_xboole_0(A_120,B_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_908])).

tff(c_1847,plain,(
    ! [A_146,B_147] : k2_xboole_0(k1_tarski(A_146),k2_tarski(A_146,B_147)) = k2_tarski(A_146,B_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_1841,c_967])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_4','#skF_5')) != k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.65  
% 3.63/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.65  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.63/1.65  
% 3.63/1.65  %Foreground sorts:
% 3.63/1.65  
% 3.63/1.65  
% 3.63/1.65  %Background operators:
% 3.63/1.65  
% 3.63/1.65  
% 3.63/1.65  %Foreground operators:
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.63/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.63/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.63/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.63/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.63/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.63/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.63/1.65  
% 3.63/1.67  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.63/1.67  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.63/1.67  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.63/1.67  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.63/1.67  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.63/1.67  tff(f_74, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.63/1.67  tff(f_60, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.63/1.67  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.63/1.67  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.63/1.67  tff(f_77, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 3.63/1.67  tff(c_28, plain, (![A_14]: (k2_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.63/1.67  tff(c_34, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.63/1.67  tff(c_127, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.63/1.67  tff(c_139, plain, (![B_17]: (k4_xboole_0(B_17, B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_127])).
% 3.63/1.67  tff(c_208, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k4_xboole_0(B_74, A_73))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.63/1.67  tff(c_220, plain, (![B_17]: (k5_xboole_0(B_17, k1_xboole_0)=k2_xboole_0(B_17, B_17))), inference(superposition, [status(thm), theory('equality')], [c_139, c_208])).
% 3.63/1.67  tff(c_225, plain, (![B_75]: (k5_xboole_0(B_75, k1_xboole_0)=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_220])).
% 3.63/1.67  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.63/1.67  tff(c_231, plain, (![B_75]: (k5_xboole_0(k1_xboole_0, B_75)=B_75)), inference(superposition, [status(thm), theory('equality')], [c_225, c_2])).
% 3.63/1.67  tff(c_56, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), k2_tarski(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.63/1.67  tff(c_138, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), k2_tarski(A_39, B_40))=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_127])).
% 3.63/1.67  tff(c_46, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.63/1.67  tff(c_443, plain, (![A_90, B_91, C_92]: (k5_xboole_0(k5_xboole_0(A_90, B_91), C_92)=k5_xboole_0(A_90, k5_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.63/1.67  tff(c_1185, plain, (![A_135, A_133, B_134]: (k5_xboole_0(A_135, k5_xboole_0(A_133, B_134))=k5_xboole_0(A_133, k5_xboole_0(B_134, A_135)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_443])).
% 3.63/1.67  tff(c_1411, plain, (![B_136, A_137]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_136, A_137))=k5_xboole_0(A_137, B_136))), inference(superposition, [status(thm), theory('equality')], [c_231, c_1185])).
% 3.63/1.67  tff(c_1496, plain, (![B_28, A_27]: (k5_xboole_0(k4_xboole_0(B_28, A_27), A_27)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1411])).
% 3.63/1.67  tff(c_1613, plain, (![B_139, A_140]: (k5_xboole_0(k4_xboole_0(B_139, A_140), A_140)=k2_xboole_0(A_140, B_139))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_1496])).
% 3.63/1.67  tff(c_1676, plain, (![A_39, B_40]: (k2_xboole_0(k2_tarski(A_39, B_40), k1_tarski(A_39))=k5_xboole_0(k1_xboole_0, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_1613])).
% 3.63/1.67  tff(c_1841, plain, (![A_146, B_147]: (k2_xboole_0(k2_tarski(A_146, B_147), k1_tarski(A_146))=k2_tarski(A_146, B_147))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_1676])).
% 3.63/1.67  tff(c_40, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.63/1.67  tff(c_619, plain, (![A_98, B_99]: (k5_xboole_0(k5_xboole_0(A_98, B_99), k3_xboole_0(A_98, B_99))=k2_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.63/1.67  tff(c_889, plain, (![B_119, A_120]: (k5_xboole_0(k5_xboole_0(B_119, A_120), k3_xboole_0(A_120, B_119))=k2_xboole_0(A_120, B_119))), inference(superposition, [status(thm), theory('equality')], [c_2, c_619])).
% 3.63/1.67  tff(c_42, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.63/1.67  tff(c_908, plain, (![B_119, A_120]: (k5_xboole_0(B_119, k5_xboole_0(A_120, k3_xboole_0(A_120, B_119)))=k2_xboole_0(A_120, B_119))), inference(superposition, [status(thm), theory('equality')], [c_889, c_42])).
% 3.63/1.67  tff(c_967, plain, (![B_119, A_120]: (k2_xboole_0(B_119, A_120)=k2_xboole_0(A_120, B_119))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_908])).
% 3.63/1.67  tff(c_1847, plain, (![A_146, B_147]: (k2_xboole_0(k1_tarski(A_146), k2_tarski(A_146, B_147))=k2_tarski(A_146, B_147))), inference(superposition, [status(thm), theory('equality')], [c_1841, c_967])).
% 3.63/1.67  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_4', '#skF_5'))!=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.63/1.67  tff(c_1868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1847, c_58])).
% 3.63/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.67  
% 3.63/1.67  Inference rules
% 3.63/1.67  ----------------------
% 3.63/1.67  #Ref     : 0
% 3.63/1.67  #Sup     : 434
% 3.63/1.67  #Fact    : 0
% 3.63/1.67  #Define  : 0
% 3.63/1.67  #Split   : 0
% 3.63/1.67  #Chain   : 0
% 3.63/1.67  #Close   : 0
% 3.63/1.67  
% 3.63/1.67  Ordering : KBO
% 3.63/1.67  
% 3.63/1.67  Simplification rules
% 3.63/1.67  ----------------------
% 3.63/1.67  #Subsume      : 35
% 3.63/1.67  #Demod        : 245
% 3.63/1.67  #Tautology    : 220
% 3.63/1.67  #SimpNegUnit  : 0
% 3.63/1.67  #BackRed      : 3
% 3.63/1.67  
% 3.63/1.67  #Partial instantiations: 0
% 3.63/1.67  #Strategies tried      : 1
% 3.63/1.67  
% 3.63/1.67  Timing (in seconds)
% 3.63/1.67  ----------------------
% 3.63/1.67  Preprocessing        : 0.35
% 3.63/1.67  Parsing              : 0.18
% 3.63/1.67  CNF conversion       : 0.02
% 3.63/1.67  Main loop            : 0.54
% 3.63/1.67  Inferencing          : 0.18
% 3.63/1.67  Reduction            : 0.22
% 3.63/1.67  Demodulation         : 0.18
% 3.63/1.67  BG Simplification    : 0.03
% 3.63/1.67  Subsumption          : 0.08
% 3.63/1.67  Abstraction          : 0.03
% 3.63/1.67  MUC search           : 0.00
% 3.63/1.67  Cooper               : 0.00
% 3.63/1.67  Total                : 0.92
% 3.63/1.67  Index Insertion      : 0.00
% 3.63/1.67  Index Deletion       : 0.00
% 3.63/1.67  Index Matching       : 0.00
% 3.63/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
