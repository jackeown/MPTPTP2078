%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:30 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  35 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_31])).

tff(c_70,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_70])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(k4_xboole_0(A_30,B_31),C_32) = k4_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_188,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k2_xboole_0(B_36,k1_xboole_0)) = k4_xboole_0(A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_229,plain,(
    ! [A_35] : k4_xboole_0(A_35,k2_xboole_0('#skF_2','#skF_1')) = k4_xboole_0(A_35,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_188])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | k4_xboole_0(A_25,B_24) != A_25 ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_2'),'#skF_1') != k4_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_18])).

tff(c_96,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_1')) != k4_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:40:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.20  
% 1.93/1.21  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.93/1.21  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.93/1.21  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.93/1.21  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.93/1.21  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.93/1.21  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.93/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.93/1.21  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.21  tff(c_31, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.21  tff(c_35, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_31])).
% 1.93/1.21  tff(c_70, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.21  tff(c_79, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35, c_70])).
% 1.93/1.21  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.21  tff(c_97, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k4_xboole_0(A_30, B_31), C_32)=k4_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.21  tff(c_188, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k2_xboole_0(B_36, k1_xboole_0))=k4_xboole_0(A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_10, c_97])).
% 1.93/1.21  tff(c_229, plain, (![A_35]: (k4_xboole_0(A_35, k2_xboole_0('#skF_2', '#skF_1'))=k4_xboole_0(A_35, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_188])).
% 1.93/1.21  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.21  tff(c_36, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.21  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.21  tff(c_58, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | k4_xboole_0(A_25, B_24)!=A_25)), inference(resolution, [status(thm)], [c_36, c_2])).
% 1.93/1.21  tff(c_18, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.21  tff(c_69, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), '#skF_1')!=k4_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_18])).
% 1.93/1.21  tff(c_96, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_1'))!=k4_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_69])).
% 1.93/1.21  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_96])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 0
% 1.93/1.21  #Sup     : 68
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 1
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 2
% 1.93/1.21  #Demod        : 32
% 1.93/1.21  #Tautology    : 38
% 1.93/1.21  #SimpNegUnit  : 0
% 1.93/1.21  #BackRed      : 2
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 1.93/1.21  Preprocessing        : 0.26
% 1.93/1.22  Parsing              : 0.15
% 1.93/1.22  CNF conversion       : 0.02
% 1.93/1.22  Main loop            : 0.20
% 1.93/1.22  Inferencing          : 0.08
% 1.93/1.22  Reduction            : 0.06
% 1.93/1.22  Demodulation         : 0.05
% 1.93/1.22  BG Simplification    : 0.01
% 1.93/1.22  Subsumption          : 0.04
% 1.93/1.22  Abstraction          : 0.01
% 1.93/1.22  MUC search           : 0.00
% 1.93/1.22  Cooper               : 0.00
% 1.93/1.22  Total                : 0.49
% 1.93/1.22  Index Insertion      : 0.00
% 1.93/1.22  Index Deletion       : 0.00
% 1.93/1.22  Index Matching       : 0.00
% 1.93/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
