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
% DateTime   : Thu Dec  3 09:44:51 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_221,plain,(
    ! [A_39,B_40] : r1_tarski(k3_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_6])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_316,plain,(
    ! [A_47,B_48] : k4_xboole_0(k3_xboole_0(A_47,B_48),A_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_221,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k3_xboole_0(A_9,B_10),C_11) = k3_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_321,plain,(
    ! [A_47,B_48] : k3_xboole_0(A_47,k4_xboole_0(B_48,A_47)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_12])).

tff(c_354,plain,(
    ! [A_49,B_50] : k5_xboole_0(k5_xboole_0(A_49,B_50),k3_xboole_0(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k5_xboole_0(k5_xboole_0(A_13,B_14),C_15) = k5_xboole_0(A_13,k5_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1108,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k5_xboole_0(B_82,k3_xboole_0(A_81,B_82))) = k2_xboole_0(A_81,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_16])).

tff(c_1154,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k5_xboole_0(k4_xboole_0(B_48,A_47),k1_xboole_0)) = k2_xboole_0(A_47,k4_xboole_0(B_48,A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_1108])).

tff(c_1177,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k4_xboole_0(B_48,A_47)) = k2_xboole_0(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_1154])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:01:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.78  
% 3.05/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.78  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.05/1.78  
% 3.05/1.78  %Foreground sorts:
% 3.05/1.78  
% 3.05/1.78  
% 3.05/1.78  %Background operators:
% 3.05/1.78  
% 3.05/1.78  
% 3.05/1.78  %Foreground operators:
% 3.05/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.05/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.78  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.78  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.05/1.78  
% 3.05/1.79  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.05/1.79  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.05/1.79  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.05/1.79  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.05/1.79  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.05/1.79  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.05/1.79  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.05/1.79  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.05/1.79  tff(f_46, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.05/1.79  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.79  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.79  tff(c_135, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.79  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.79  tff(c_221, plain, (![A_39, B_40]: (r1_tarski(k3_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_135, c_6])).
% 3.05/1.79  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.05/1.79  tff(c_316, plain, (![A_47, B_48]: (k4_xboole_0(k3_xboole_0(A_47, B_48), A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_221, c_4])).
% 3.05/1.79  tff(c_12, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k3_xboole_0(A_9, B_10), C_11)=k3_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.79  tff(c_321, plain, (![A_47, B_48]: (k3_xboole_0(A_47, k4_xboole_0(B_48, A_47))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_316, c_12])).
% 3.05/1.79  tff(c_354, plain, (![A_49, B_50]: (k5_xboole_0(k5_xboole_0(A_49, B_50), k3_xboole_0(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.79  tff(c_16, plain, (![A_13, B_14, C_15]: (k5_xboole_0(k5_xboole_0(A_13, B_14), C_15)=k5_xboole_0(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.79  tff(c_1108, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k5_xboole_0(B_82, k3_xboole_0(A_81, B_82)))=k2_xboole_0(A_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_354, c_16])).
% 3.05/1.79  tff(c_1154, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k5_xboole_0(k4_xboole_0(B_48, A_47), k1_xboole_0))=k2_xboole_0(A_47, k4_xboole_0(B_48, A_47)))), inference(superposition, [status(thm), theory('equality')], [c_321, c_1108])).
% 3.05/1.79  tff(c_1177, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k4_xboole_0(B_48, A_47))=k2_xboole_0(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_1154])).
% 3.05/1.79  tff(c_20, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.05/1.79  tff(c_1181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1177, c_20])).
% 3.05/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.79  
% 3.05/1.79  Inference rules
% 3.05/1.79  ----------------------
% 3.05/1.79  #Ref     : 0
% 3.05/1.79  #Sup     : 290
% 3.05/1.79  #Fact    : 0
% 3.05/1.79  #Define  : 0
% 3.05/1.79  #Split   : 0
% 3.05/1.79  #Chain   : 0
% 3.05/1.79  #Close   : 0
% 3.05/1.79  
% 3.05/1.79  Ordering : KBO
% 3.05/1.79  
% 3.05/1.79  Simplification rules
% 3.05/1.79  ----------------------
% 3.05/1.79  #Subsume      : 0
% 3.05/1.79  #Demod        : 239
% 3.05/1.79  #Tautology    : 213
% 3.05/1.79  #SimpNegUnit  : 0
% 3.05/1.79  #BackRed      : 3
% 3.05/1.79  
% 3.05/1.79  #Partial instantiations: 0
% 3.05/1.79  #Strategies tried      : 1
% 3.05/1.79  
% 3.05/1.79  Timing (in seconds)
% 3.05/1.79  ----------------------
% 3.05/1.79  Preprocessing        : 0.43
% 3.05/1.79  Parsing              : 0.22
% 3.05/1.79  CNF conversion       : 0.03
% 3.05/1.79  Main loop            : 0.45
% 3.12/1.79  Inferencing          : 0.18
% 3.12/1.79  Reduction            : 0.17
% 3.12/1.79  Demodulation         : 0.13
% 3.12/1.79  BG Simplification    : 0.02
% 3.12/1.79  Subsumption          : 0.06
% 3.12/1.79  Abstraction          : 0.03
% 3.12/1.79  MUC search           : 0.00
% 3.12/1.79  Cooper               : 0.00
% 3.12/1.79  Total                : 0.92
% 3.12/1.79  Index Insertion      : 0.00
% 3.12/1.79  Index Deletion       : 0.00
% 3.12/1.79  Index Matching       : 0.00
% 3.12/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
