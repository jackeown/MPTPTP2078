%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:52 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   22 (  22 expanded)
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

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_148,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_3,B_4] : k4_xboole_0(k4_xboole_0(A_3,B_4),A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_34])).

tff(c_332,plain,(
    ! [A_50,B_51] : k4_xboole_0(k3_xboole_0(A_50,B_51),A_50) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_42])).

tff(c_363,plain,(
    ! [C_13,B_12] : k3_xboole_0(C_13,k4_xboole_0(B_12,C_13)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_332])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_375,plain,(
    ! [A_52,B_53,C_54] : k5_xboole_0(k5_xboole_0(A_52,B_53),C_54) = k5_xboole_0(A_52,k5_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1973,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k5_xboole_0(B_100,k3_xboole_0(A_99,B_100))) = k2_xboole_0(A_99,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_375])).

tff(c_2025,plain,(
    ! [C_13,B_12] : k5_xboole_0(C_13,k5_xboole_0(k4_xboole_0(B_12,C_13),k1_xboole_0)) = k2_xboole_0(C_13,k4_xboole_0(B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_1973])).

tff(c_2050,plain,(
    ! [C_13,B_12] : k5_xboole_0(C_13,k4_xboole_0(B_12,C_13)) = k2_xboole_0(C_13,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16,c_2025])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2050,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.56  
% 3.52/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.56  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.52/1.56  
% 3.52/1.56  %Foreground sorts:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Background operators:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Foreground operators:
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.52/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.56  
% 3.52/1.57  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.52/1.57  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.52/1.57  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.52/1.57  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.52/1.57  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.52/1.57  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.52/1.57  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.52/1.57  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.52/1.57  tff(f_50, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.52/1.57  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.52/1.57  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.52/1.57  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.52/1.57  tff(c_148, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.52/1.57  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.57  tff(c_34, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.57  tff(c_42, plain, (![A_3, B_4]: (k4_xboole_0(k4_xboole_0(A_3, B_4), A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_34])).
% 3.52/1.57  tff(c_332, plain, (![A_50, B_51]: (k4_xboole_0(k3_xboole_0(A_50, B_51), A_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_42])).
% 3.52/1.57  tff(c_363, plain, (![C_13, B_12]: (k3_xboole_0(C_13, k4_xboole_0(B_12, C_13))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_332])).
% 3.52/1.57  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.52/1.57  tff(c_375, plain, (![A_52, B_53, C_54]: (k5_xboole_0(k5_xboole_0(A_52, B_53), C_54)=k5_xboole_0(A_52, k5_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.57  tff(c_1973, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k5_xboole_0(B_100, k3_xboole_0(A_99, B_100)))=k2_xboole_0(A_99, B_100))), inference(superposition, [status(thm), theory('equality')], [c_20, c_375])).
% 3.52/1.57  tff(c_2025, plain, (![C_13, B_12]: (k5_xboole_0(C_13, k5_xboole_0(k4_xboole_0(B_12, C_13), k1_xboole_0))=k2_xboole_0(C_13, k4_xboole_0(B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_363, c_1973])).
% 3.52/1.57  tff(c_2050, plain, (![C_13, B_12]: (k5_xboole_0(C_13, k4_xboole_0(B_12, C_13))=k2_xboole_0(C_13, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16, c_2025])).
% 3.52/1.57  tff(c_22, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.52/1.57  tff(c_2314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2050, c_22])).
% 3.52/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.57  
% 3.52/1.57  Inference rules
% 3.52/1.57  ----------------------
% 3.52/1.57  #Ref     : 1
% 3.52/1.57  #Sup     : 555
% 3.52/1.57  #Fact    : 0
% 3.52/1.57  #Define  : 0
% 3.52/1.57  #Split   : 0
% 3.52/1.57  #Chain   : 0
% 3.52/1.57  #Close   : 0
% 3.52/1.57  
% 3.52/1.57  Ordering : KBO
% 3.52/1.57  
% 3.52/1.57  Simplification rules
% 3.52/1.57  ----------------------
% 3.52/1.57  #Subsume      : 5
% 3.52/1.57  #Demod        : 517
% 3.52/1.57  #Tautology    : 392
% 3.52/1.57  #SimpNegUnit  : 0
% 3.52/1.57  #BackRed      : 3
% 3.52/1.57  
% 3.52/1.57  #Partial instantiations: 0
% 3.52/1.57  #Strategies tried      : 1
% 3.52/1.57  
% 3.52/1.57  Timing (in seconds)
% 3.52/1.58  ----------------------
% 3.52/1.58  Preprocessing        : 0.29
% 3.52/1.58  Parsing              : 0.15
% 3.52/1.58  CNF conversion       : 0.02
% 3.52/1.58  Main loop            : 0.54
% 3.52/1.58  Inferencing          : 0.19
% 3.52/1.58  Reduction            : 0.21
% 3.52/1.58  Demodulation         : 0.17
% 3.52/1.58  BG Simplification    : 0.02
% 3.52/1.58  Subsumption          : 0.07
% 3.52/1.58  Abstraction          : 0.03
% 3.52/1.58  MUC search           : 0.00
% 3.52/1.58  Cooper               : 0.00
% 3.52/1.58  Total                : 0.86
% 3.52/1.58  Index Insertion      : 0.00
% 3.52/1.58  Index Deletion       : 0.00
% 3.52/1.58  Index Matching       : 0.00
% 3.52/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
