%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:32 EST 2020

% Result     : Theorem 11.55s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  37 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_283,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4822,plain,(
    ! [A_120,B_121,C_122] : k4_xboole_0(k3_xboole_0(A_120,B_121),C_122) = k3_xboole_0(B_121,k4_xboole_0(A_120,C_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_283])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4876,plain,(
    ! [B_121,A_120,C_122] : k3_xboole_0(B_121,k4_xboole_0(A_120,C_122)) = k3_xboole_0(A_120,k4_xboole_0(B_121,C_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4822,c_18])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [A_12,B_13] : k3_xboole_0(k3_xboole_0(A_12,B_13),A_12) = k3_xboole_0(A_12,B_13) ),
    inference(resolution,[status(thm)],[c_14,c_97])).

tff(c_157,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1142,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(B_78,A_77)) = k4_xboole_0(A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_157])).

tff(c_1167,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1142])).

tff(c_2627,plain,(
    ! [A_100,B_101] : k4_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1167])).

tff(c_2706,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2627])).

tff(c_24,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_26,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_25])).

tff(c_3346,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2706,c_26])).

tff(c_33515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4876,c_3346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:12:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.55/5.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.55/5.11  
% 11.55/5.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.55/5.11  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.55/5.11  
% 11.55/5.11  %Foreground sorts:
% 11.55/5.11  
% 11.55/5.11  
% 11.55/5.11  %Background operators:
% 11.55/5.11  
% 11.55/5.11  
% 11.55/5.11  %Foreground operators:
% 11.55/5.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.55/5.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.55/5.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.55/5.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.55/5.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.55/5.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.55/5.11  tff('#skF_2', type, '#skF_2': $i).
% 11.55/5.11  tff('#skF_3', type, '#skF_3': $i).
% 11.55/5.11  tff('#skF_1', type, '#skF_1': $i).
% 11.55/5.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.55/5.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.55/5.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.55/5.11  
% 11.65/5.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.65/5.12  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.65/5.12  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.65/5.12  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.65/5.12  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.65/5.12  tff(f_52, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_xboole_1)).
% 11.65/5.12  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.65/5.12  tff(c_283, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.65/5.12  tff(c_4822, plain, (![A_120, B_121, C_122]: (k4_xboole_0(k3_xboole_0(A_120, B_121), C_122)=k3_xboole_0(B_121, k4_xboole_0(A_120, C_122)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_283])).
% 11.65/5.12  tff(c_18, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.65/5.12  tff(c_4876, plain, (![B_121, A_120, C_122]: (k3_xboole_0(B_121, k4_xboole_0(A_120, C_122))=k3_xboole_0(A_120, k4_xboole_0(B_121, C_122)))), inference(superposition, [status(thm), theory('equality')], [c_4822, c_18])).
% 11.65/5.12  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.65/5.12  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.65/5.12  tff(c_97, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.65/5.12  tff(c_113, plain, (![A_12, B_13]: (k3_xboole_0(k3_xboole_0(A_12, B_13), A_12)=k3_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_14, c_97])).
% 11.65/5.12  tff(c_157, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.65/5.12  tff(c_1142, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(B_78, A_77))=k4_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_2, c_157])).
% 11.65/5.12  tff(c_1167, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, k3_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_1142])).
% 11.65/5.12  tff(c_2627, plain, (![A_100, B_101]: (k4_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1167])).
% 11.65/5.12  tff(c_2706, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2627])).
% 11.65/5.12  tff(c_24, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.65/5.12  tff(c_25, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 11.65/5.12  tff(c_26, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_25])).
% 11.65/5.12  tff(c_3346, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2706, c_26])).
% 11.65/5.12  tff(c_33515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4876, c_3346])).
% 11.65/5.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.65/5.12  
% 11.65/5.12  Inference rules
% 11.65/5.12  ----------------------
% 11.65/5.12  #Ref     : 0
% 11.65/5.12  #Sup     : 8298
% 11.65/5.12  #Fact    : 0
% 11.65/5.12  #Define  : 0
% 11.65/5.12  #Split   : 0
% 11.65/5.12  #Chain   : 0
% 11.65/5.12  #Close   : 0
% 11.65/5.12  
% 11.65/5.12  Ordering : KBO
% 11.65/5.12  
% 11.65/5.12  Simplification rules
% 11.65/5.12  ----------------------
% 11.65/5.12  #Subsume      : 82
% 11.65/5.12  #Demod        : 10803
% 11.65/5.12  #Tautology    : 5537
% 11.65/5.12  #SimpNegUnit  : 0
% 11.65/5.12  #BackRed      : 24
% 11.65/5.12  
% 11.65/5.12  #Partial instantiations: 0
% 11.65/5.12  #Strategies tried      : 1
% 11.65/5.12  
% 11.65/5.12  Timing (in seconds)
% 11.65/5.12  ----------------------
% 11.65/5.12  Preprocessing        : 0.28
% 11.65/5.12  Parsing              : 0.15
% 11.65/5.12  CNF conversion       : 0.02
% 11.65/5.12  Main loop            : 4.09
% 11.65/5.12  Inferencing          : 0.65
% 11.65/5.12  Reduction            : 2.66
% 11.65/5.12  Demodulation         : 2.47
% 11.65/5.12  BG Simplification    : 0.08
% 11.65/5.12  Subsumption          : 0.49
% 11.65/5.12  Abstraction          : 0.14
% 11.65/5.12  MUC search           : 0.00
% 11.65/5.12  Cooper               : 0.00
% 11.65/5.12  Total                : 4.39
% 11.65/5.12  Index Insertion      : 0.00
% 11.65/5.12  Index Deletion       : 0.00
% 11.65/5.12  Index Matching       : 0.00
% 11.65/5.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
