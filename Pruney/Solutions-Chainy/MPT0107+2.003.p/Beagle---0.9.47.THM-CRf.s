%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:53 EST 2020

% Result     : Theorem 9.06s
% Output     : CNFRefutation 9.06s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_93,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_18,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1435,plain,(
    ! [A_135,B_136] : k4_xboole_0(A_135,k4_xboole_0(A_135,B_136)) = k3_xboole_0(A_135,B_136) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [A_25,B_26] : r1_tarski(k4_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1524,plain,(
    ! [A_137,B_138] : r1_tarski(k3_xboole_0(A_137,B_138),A_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_1435,c_26])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1559,plain,(
    ! [A_137,B_138] : k4_xboole_0(k3_xboole_0(A_137,B_138),A_137) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1524,c_30])).

tff(c_48,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2339,plain,(
    ! [A_165,B_166] : k2_xboole_0(k4_xboole_0(A_165,B_166),k4_xboole_0(B_166,A_165)) = k5_xboole_0(A_165,B_166) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2415,plain,(
    ! [A_45,B_46] : k2_xboole_0(k4_xboole_0(A_45,B_46),k4_xboole_0(k3_xboole_0(A_45,B_46),A_45)) = k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2339])).

tff(c_2476,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1559,c_2415])).

tff(c_68,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_21878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.06/3.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.06/3.73  
% 9.06/3.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.06/3.73  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 9.06/3.73  
% 9.06/3.73  %Foreground sorts:
% 9.06/3.73  
% 9.06/3.73  
% 9.06/3.73  %Background operators:
% 9.06/3.73  
% 9.06/3.73  
% 9.06/3.73  %Foreground operators:
% 9.06/3.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.06/3.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.06/3.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.06/3.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.06/3.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.06/3.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.06/3.73  tff('#skF_2', type, '#skF_2': $i).
% 9.06/3.73  tff('#skF_1', type, '#skF_1': $i).
% 9.06/3.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.06/3.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.06/3.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.06/3.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.06/3.73  
% 9.06/3.74  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.06/3.74  tff(f_93, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.06/3.74  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.06/3.74  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 9.06/3.74  tff(f_91, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.06/3.74  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 9.06/3.74  tff(f_126, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.06/3.74  tff(c_18, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.06/3.74  tff(c_1435, plain, (![A_135, B_136]: (k4_xboole_0(A_135, k4_xboole_0(A_135, B_136))=k3_xboole_0(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.06/3.74  tff(c_26, plain, (![A_25, B_26]: (r1_tarski(k4_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.06/3.74  tff(c_1524, plain, (![A_137, B_138]: (r1_tarski(k3_xboole_0(A_137, B_138), A_137))), inference(superposition, [status(thm), theory('equality')], [c_1435, c_26])).
% 9.06/3.74  tff(c_30, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.06/3.74  tff(c_1559, plain, (![A_137, B_138]: (k4_xboole_0(k3_xboole_0(A_137, B_138), A_137)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1524, c_30])).
% 9.06/3.74  tff(c_48, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.06/3.74  tff(c_2339, plain, (![A_165, B_166]: (k2_xboole_0(k4_xboole_0(A_165, B_166), k4_xboole_0(B_166, A_165))=k5_xboole_0(A_165, B_166))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.06/3.74  tff(c_2415, plain, (![A_45, B_46]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k4_xboole_0(k3_xboole_0(A_45, B_46), A_45))=k5_xboole_0(A_45, k3_xboole_0(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2339])).
% 9.06/3.74  tff(c_2476, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1559, c_2415])).
% 9.06/3.74  tff(c_68, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.06/3.74  tff(c_21878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2476, c_68])).
% 9.06/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.06/3.74  
% 9.06/3.74  Inference rules
% 9.06/3.74  ----------------------
% 9.06/3.74  #Ref     : 2
% 9.06/3.74  #Sup     : 5574
% 9.06/3.74  #Fact    : 0
% 9.06/3.74  #Define  : 0
% 9.06/3.74  #Split   : 2
% 9.06/3.74  #Chain   : 0
% 9.06/3.74  #Close   : 0
% 9.06/3.74  
% 9.06/3.74  Ordering : KBO
% 9.06/3.74  
% 9.06/3.74  Simplification rules
% 9.06/3.74  ----------------------
% 9.06/3.74  #Subsume      : 667
% 9.06/3.74  #Demod        : 4609
% 9.06/3.74  #Tautology    : 3211
% 9.06/3.74  #SimpNegUnit  : 0
% 9.06/3.74  #BackRed      : 3
% 9.06/3.74  
% 9.06/3.74  #Partial instantiations: 0
% 9.06/3.74  #Strategies tried      : 1
% 9.06/3.74  
% 9.06/3.74  Timing (in seconds)
% 9.06/3.74  ----------------------
% 9.06/3.74  Preprocessing        : 0.34
% 9.06/3.74  Parsing              : 0.18
% 9.06/3.74  CNF conversion       : 0.02
% 9.06/3.74  Main loop            : 2.60
% 9.06/3.74  Inferencing          : 0.55
% 9.06/3.74  Reduction            : 1.38
% 9.06/3.74  Demodulation         : 1.19
% 9.06/3.74  BG Simplification    : 0.07
% 9.06/3.74  Subsumption          : 0.47
% 9.06/3.74  Abstraction          : 0.11
% 9.06/3.74  MUC search           : 0.00
% 9.06/3.74  Cooper               : 0.00
% 9.06/3.74  Total                : 2.96
% 9.06/3.74  Index Insertion      : 0.00
% 9.06/3.74  Index Deletion       : 0.00
% 9.06/3.74  Index Matching       : 0.00
% 9.06/3.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
