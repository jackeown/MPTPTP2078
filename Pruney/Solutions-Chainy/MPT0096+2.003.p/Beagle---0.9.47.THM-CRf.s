%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:35 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  33 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_xboole_1)).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_195,plain,(
    ! [A_37,B_38] : r1_tarski(k3_xboole_0(A_37,B_38),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_14])).

tff(c_269,plain,(
    ! [A_42] : r1_tarski(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_195])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_273,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_269,c_12])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3564,plain,(
    ! [A_125,B_126,C_127] : k4_xboole_0(k4_xboole_0(A_125,B_126),k4_xboole_0(A_125,k2_xboole_0(B_126,C_127))) = k3_xboole_0(k4_xboole_0(A_125,B_126),C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_18])).

tff(c_3774,plain,(
    ! [A_125,A_3] : k4_xboole_0(k4_xboole_0(A_125,A_3),k4_xboole_0(A_125,A_3)) = k3_xboole_0(k4_xboole_0(A_125,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3564])).

tff(c_3835,plain,(
    ! [A_128,A_129] : k3_xboole_0(k4_xboole_0(A_128,A_129),A_129) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_3774])).

tff(c_3964,plain,(
    ! [A_14,B_15] : k3_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3835])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_20])).

tff(c_4367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3964,c_49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:28:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.76  
% 3.86/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.76  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.86/1.76  
% 3.86/1.76  %Foreground sorts:
% 3.86/1.76  
% 3.86/1.76  
% 3.86/1.76  %Background operators:
% 3.86/1.76  
% 3.86/1.76  
% 3.86/1.76  %Foreground operators:
% 3.86/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.86/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.86/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.86/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.86/1.76  
% 3.86/1.77  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.86/1.77  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.86/1.77  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.86/1.77  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.86/1.77  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.86/1.77  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.86/1.77  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.86/1.77  tff(f_46, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_xboole_1)).
% 3.86/1.77  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.86/1.77  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.86/1.77  tff(c_133, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.86/1.77  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.86/1.77  tff(c_195, plain, (![A_37, B_38]: (r1_tarski(k3_xboole_0(A_37, B_38), A_37))), inference(superposition, [status(thm), theory('equality')], [c_133, c_14])).
% 3.86/1.77  tff(c_269, plain, (![A_42]: (r1_tarski(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_8, c_195])).
% 3.86/1.77  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.86/1.77  tff(c_273, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_269, c_12])).
% 3.86/1.77  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.77  tff(c_207, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.86/1.77  tff(c_3564, plain, (![A_125, B_126, C_127]: (k4_xboole_0(k4_xboole_0(A_125, B_126), k4_xboole_0(A_125, k2_xboole_0(B_126, C_127)))=k3_xboole_0(k4_xboole_0(A_125, B_126), C_127))), inference(superposition, [status(thm), theory('equality')], [c_207, c_18])).
% 3.86/1.77  tff(c_3774, plain, (![A_125, A_3]: (k4_xboole_0(k4_xboole_0(A_125, A_3), k4_xboole_0(A_125, A_3))=k3_xboole_0(k4_xboole_0(A_125, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3564])).
% 3.86/1.77  tff(c_3835, plain, (![A_128, A_129]: (k3_xboole_0(k4_xboole_0(A_128, A_129), A_129)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_3774])).
% 3.86/1.77  tff(c_3964, plain, (![A_14, B_15]: (k3_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_3835])).
% 3.86/1.77  tff(c_42, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.86/1.77  tff(c_20, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.86/1.77  tff(c_49, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_20])).
% 3.86/1.77  tff(c_4367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3964, c_49])).
% 3.86/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.77  
% 3.86/1.77  Inference rules
% 3.86/1.77  ----------------------
% 3.86/1.77  #Ref     : 0
% 3.86/1.77  #Sup     : 1057
% 3.86/1.77  #Fact    : 0
% 3.86/1.77  #Define  : 0
% 3.86/1.77  #Split   : 0
% 3.86/1.77  #Chain   : 0
% 3.86/1.77  #Close   : 0
% 3.86/1.77  
% 3.86/1.77  Ordering : KBO
% 3.86/1.77  
% 3.86/1.77  Simplification rules
% 3.86/1.77  ----------------------
% 3.86/1.77  #Subsume      : 0
% 3.86/1.77  #Demod        : 922
% 3.86/1.77  #Tautology    : 744
% 3.86/1.77  #SimpNegUnit  : 0
% 3.86/1.77  #BackRed      : 2
% 3.86/1.77  
% 3.86/1.77  #Partial instantiations: 0
% 3.86/1.77  #Strategies tried      : 1
% 3.86/1.77  
% 3.86/1.77  Timing (in seconds)
% 3.86/1.77  ----------------------
% 3.86/1.77  Preprocessing        : 0.31
% 3.86/1.77  Parsing              : 0.19
% 3.86/1.77  CNF conversion       : 0.02
% 3.86/1.77  Main loop            : 0.69
% 3.86/1.77  Inferencing          : 0.25
% 3.86/1.77  Reduction            : 0.28
% 3.86/1.77  Demodulation         : 0.23
% 3.86/1.77  BG Simplification    : 0.03
% 3.86/1.77  Subsumption          : 0.09
% 3.86/1.77  Abstraction          : 0.04
% 3.86/1.77  MUC search           : 0.00
% 3.86/1.77  Cooper               : 0.00
% 3.86/1.77  Total                : 1.03
% 3.86/1.77  Index Insertion      : 0.00
% 3.86/1.77  Index Deletion       : 0.00
% 3.86/1.77  Index Matching       : 0.00
% 3.86/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
