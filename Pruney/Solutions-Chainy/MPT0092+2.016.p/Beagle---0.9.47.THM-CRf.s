%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:30 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_58])).

tff(c_135,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_167,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_135])).

tff(c_174,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_167])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_37,plain,(
    ! [B_19,A_20] :
      ( r1_xboole_0(B_19,A_20)
      | ~ r1_xboole_0(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [B_12,A_11] : r1_xboole_0(B_12,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_14,c_37])).

tff(c_88,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ! [B_12,A_11] : k4_xboole_0(B_12,k4_xboole_0(A_11,B_12)) = B_12 ),
    inference(resolution,[status(thm)],[c_43,c_88])).

tff(c_187,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k3_xboole_0(A_36,B_37),C_38) = k3_xboole_0(A_36,k4_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_479,plain,(
    ! [A_48,B_49,C_50] : r1_xboole_0(k3_xboole_0(A_48,k4_xboole_0(B_49,C_50)),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_812,plain,(
    ! [C_63,A_64,B_65] : r1_xboole_0(C_63,k3_xboole_0(A_64,k4_xboole_0(B_65,C_63))) ),
    inference(resolution,[status(thm)],[c_479,c_2])).

tff(c_1075,plain,(
    ! [A_74,B_75,A_76] : r1_xboole_0(k4_xboole_0(A_74,B_75),k3_xboole_0(A_76,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_812])).

tff(c_1131,plain,(
    ! [A_77] : r1_xboole_0(k4_xboole_0(A_77,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_1075])).

tff(c_1157,plain,(
    ! [A_77] : r1_xboole_0('#skF_1',k4_xboole_0(A_77,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_1131,c_2])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.39  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.69/1.39  
% 2.69/1.39  %Foreground sorts:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Background operators:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Foreground operators:
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.39  
% 2.69/1.40  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.69/1.40  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.69/1.40  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.69/1.40  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.69/1.40  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.69/1.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.69/1.40  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.69/1.40  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.69/1.40  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.40  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.40  tff(c_58, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.40  tff(c_62, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_58])).
% 2.69/1.40  tff(c_135, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.40  tff(c_167, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_62, c_135])).
% 2.69/1.40  tff(c_174, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_167])).
% 2.69/1.40  tff(c_14, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.40  tff(c_37, plain, (![B_19, A_20]: (r1_xboole_0(B_19, A_20) | ~r1_xboole_0(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.40  tff(c_43, plain, (![B_12, A_11]: (r1_xboole_0(B_12, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_14, c_37])).
% 2.69/1.40  tff(c_88, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.40  tff(c_105, plain, (![B_12, A_11]: (k4_xboole_0(B_12, k4_xboole_0(A_11, B_12))=B_12)), inference(resolution, [status(thm)], [c_43, c_88])).
% 2.69/1.40  tff(c_187, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k3_xboole_0(A_36, B_37), C_38)=k3_xboole_0(A_36, k4_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.40  tff(c_479, plain, (![A_48, B_49, C_50]: (r1_xboole_0(k3_xboole_0(A_48, k4_xboole_0(B_49, C_50)), C_50))), inference(superposition, [status(thm), theory('equality')], [c_187, c_14])).
% 2.69/1.40  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.40  tff(c_812, plain, (![C_63, A_64, B_65]: (r1_xboole_0(C_63, k3_xboole_0(A_64, k4_xboole_0(B_65, C_63))))), inference(resolution, [status(thm)], [c_479, c_2])).
% 2.69/1.40  tff(c_1075, plain, (![A_74, B_75, A_76]: (r1_xboole_0(k4_xboole_0(A_74, B_75), k3_xboole_0(A_76, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_812])).
% 2.69/1.40  tff(c_1131, plain, (![A_77]: (r1_xboole_0(k4_xboole_0(A_77, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_1075])).
% 2.69/1.40  tff(c_1157, plain, (![A_77]: (r1_xboole_0('#skF_1', k4_xboole_0(A_77, '#skF_2')))), inference(resolution, [status(thm)], [c_1131, c_2])).
% 2.69/1.40  tff(c_20, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.40  tff(c_1165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1157, c_20])).
% 2.69/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  Inference rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Ref     : 0
% 2.69/1.40  #Sup     : 279
% 2.69/1.40  #Fact    : 0
% 2.69/1.40  #Define  : 0
% 2.69/1.40  #Split   : 0
% 2.69/1.40  #Chain   : 0
% 2.69/1.40  #Close   : 0
% 2.69/1.40  
% 2.69/1.40  Ordering : KBO
% 2.69/1.40  
% 2.69/1.40  Simplification rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Subsume      : 1
% 2.69/1.40  #Demod        : 174
% 2.69/1.40  #Tautology    : 185
% 2.69/1.40  #SimpNegUnit  : 0
% 2.69/1.40  #BackRed      : 1
% 2.69/1.40  
% 2.69/1.40  #Partial instantiations: 0
% 2.69/1.40  #Strategies tried      : 1
% 2.69/1.40  
% 2.69/1.40  Timing (in seconds)
% 2.69/1.40  ----------------------
% 2.69/1.40  Preprocessing        : 0.28
% 2.69/1.40  Parsing              : 0.15
% 2.69/1.40  CNF conversion       : 0.02
% 2.69/1.40  Main loop            : 0.35
% 2.69/1.40  Inferencing          : 0.13
% 2.69/1.40  Reduction            : 0.12
% 2.69/1.40  Demodulation         : 0.10
% 2.69/1.40  BG Simplification    : 0.02
% 2.69/1.40  Subsumption          : 0.05
% 2.69/1.40  Abstraction          : 0.02
% 2.69/1.40  MUC search           : 0.00
% 2.69/1.40  Cooper               : 0.00
% 2.69/1.40  Total                : 0.67
% 2.69/1.40  Index Insertion      : 0.00
% 2.69/1.40  Index Deletion       : 0.00
% 2.69/1.40  Index Matching       : 0.00
% 2.69/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
