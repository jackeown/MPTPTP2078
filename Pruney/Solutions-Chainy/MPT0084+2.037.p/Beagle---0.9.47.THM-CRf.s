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
% DateTime   : Thu Dec  3 09:44:09 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(c_112,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_123,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_28])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_55,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_55])).

tff(c_267,plain,(
    ! [A_52,B_53,C_54] : k2_xboole_0(k4_xboole_0(A_52,B_53),k4_xboole_0(A_52,C_54)) = k4_xboole_0(A_52,k3_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_297,plain,(
    ! [B_53] : k4_xboole_0('#skF_1',k3_xboole_0(B_53,'#skF_3')) = k2_xboole_0(k4_xboole_0('#skF_1',B_53),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_267])).

tff(c_321,plain,(
    ! [B_57] : k4_xboole_0('#skF_1',k3_xboole_0(B_57,'#skF_3')) = k4_xboole_0('#skF_1',B_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_297])).

tff(c_339,plain,(
    ! [B_57] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',B_57)) = k3_xboole_0('#skF_1',k3_xboole_0(B_57,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_18])).

tff(c_645,plain,(
    ! [B_67] : k3_xboole_0('#skF_1',k3_xboole_0(B_67,'#skF_3')) = k3_xboole_0('#skF_1',B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_339])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_73,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_656,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_88])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.38  
% 2.55/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.38  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.55/1.38  
% 2.55/1.38  %Foreground sorts:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Background operators:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Foreground operators:
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.38  
% 2.55/1.39  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.55/1.39  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.55/1.39  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.55/1.39  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.55/1.39  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.55/1.39  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 2.55/1.39  tff(c_112, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.39  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.39  tff(c_123, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_112, c_28])).
% 2.55/1.39  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.39  tff(c_16, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.39  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.39  tff(c_55, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.55/1.39  tff(c_59, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_55])).
% 2.55/1.39  tff(c_267, plain, (![A_52, B_53, C_54]: (k2_xboole_0(k4_xboole_0(A_52, B_53), k4_xboole_0(A_52, C_54))=k4_xboole_0(A_52, k3_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.39  tff(c_297, plain, (![B_53]: (k4_xboole_0('#skF_1', k3_xboole_0(B_53, '#skF_3'))=k2_xboole_0(k4_xboole_0('#skF_1', B_53), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_59, c_267])).
% 2.55/1.39  tff(c_321, plain, (![B_57]: (k4_xboole_0('#skF_1', k3_xboole_0(B_57, '#skF_3'))=k4_xboole_0('#skF_1', B_57))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_297])).
% 2.55/1.39  tff(c_339, plain, (![B_57]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', B_57))=k3_xboole_0('#skF_1', k3_xboole_0(B_57, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_321, c_18])).
% 2.55/1.39  tff(c_645, plain, (![B_67]: (k3_xboole_0('#skF_1', k3_xboole_0(B_67, '#skF_3'))=k3_xboole_0('#skF_1', B_67))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_339])).
% 2.55/1.39  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.39  tff(c_73, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.39  tff(c_88, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_73])).
% 2.55/1.39  tff(c_656, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_645, c_88])).
% 2.55/1.39  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_656])).
% 2.55/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.39  
% 2.55/1.39  Inference rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Ref     : 0
% 2.55/1.39  #Sup     : 172
% 2.55/1.39  #Fact    : 0
% 2.55/1.39  #Define  : 0
% 2.55/1.39  #Split   : 0
% 2.55/1.39  #Chain   : 0
% 2.55/1.39  #Close   : 0
% 2.55/1.39  
% 2.55/1.39  Ordering : KBO
% 2.55/1.39  
% 2.55/1.39  Simplification rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Subsume      : 7
% 2.55/1.39  #Demod        : 94
% 2.55/1.39  #Tautology    : 85
% 2.55/1.39  #SimpNegUnit  : 1
% 2.55/1.39  #BackRed      : 3
% 2.55/1.39  
% 2.55/1.39  #Partial instantiations: 0
% 2.55/1.39  #Strategies tried      : 1
% 2.55/1.39  
% 2.55/1.39  Timing (in seconds)
% 2.55/1.39  ----------------------
% 2.55/1.39  Preprocessing        : 0.26
% 2.55/1.39  Parsing              : 0.15
% 2.55/1.39  CNF conversion       : 0.02
% 2.55/1.39  Main loop            : 0.31
% 2.55/1.39  Inferencing          : 0.12
% 2.55/1.39  Reduction            : 0.10
% 2.55/1.39  Demodulation         : 0.08
% 2.55/1.39  BG Simplification    : 0.01
% 2.55/1.39  Subsumption          : 0.05
% 2.55/1.39  Abstraction          : 0.01
% 2.55/1.39  MUC search           : 0.00
% 2.55/1.39  Cooper               : 0.00
% 2.55/1.39  Total                : 0.60
% 2.55/1.39  Index Insertion      : 0.00
% 2.55/1.39  Index Deletion       : 0.00
% 2.55/1.39  Index Matching       : 0.00
% 2.55/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
