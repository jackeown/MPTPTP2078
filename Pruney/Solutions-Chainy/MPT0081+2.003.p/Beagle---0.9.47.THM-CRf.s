%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:57 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  41 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [B_16,A_17] : k3_xboole_0(B_16,A_17) = k3_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [A_17] : k3_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_139,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_139])).

tff(c_164,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_151])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_85])).

tff(c_546,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k3_xboole_0(A_38,B_39),C_40) = k3_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_613,plain,(
    ! [C_40] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_40)) = k4_xboole_0(k1_xboole_0,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_546])).

tff(c_764,plain,(
    ! [C_43] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_43)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_613])).

tff(c_990,plain,(
    ! [B_47] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_47)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_764])).

tff(c_1027,plain,(
    ! [A_1] : k3_xboole_0('#skF_1',k3_xboole_0(A_1,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_990])).

tff(c_128,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_136,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128,c_21])).

tff(c_1399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:31:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.38  
% 2.44/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.38  
% 2.75/1.38  %Foreground sorts:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Background operators:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Foreground operators:
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.38  
% 2.75/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.75/1.39  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.75/1.39  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.75/1.39  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.75/1.39  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.75/1.39  tff(f_48, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 2.75/1.39  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.75/1.39  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.75/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.39  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.39  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.39  tff(c_38, plain, (![B_16, A_17]: (k3_xboole_0(B_16, A_17)=k3_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.39  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.39  tff(c_54, plain, (![A_17]: (k3_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_8])).
% 2.75/1.39  tff(c_139, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.75/1.39  tff(c_151, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_17))), inference(superposition, [status(thm), theory('equality')], [c_54, c_139])).
% 2.75/1.39  tff(c_164, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_151])).
% 2.75/1.39  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.39  tff(c_85, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.39  tff(c_89, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_85])).
% 2.75/1.39  tff(c_546, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k3_xboole_0(A_38, B_39), C_40)=k3_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.39  tff(c_613, plain, (![C_40]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_40))=k4_xboole_0(k1_xboole_0, C_40))), inference(superposition, [status(thm), theory('equality')], [c_89, c_546])).
% 2.75/1.39  tff(c_764, plain, (![C_43]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_43))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_613])).
% 2.75/1.39  tff(c_990, plain, (![B_47]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_47))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_764])).
% 2.75/1.39  tff(c_1027, plain, (![A_1]: (k3_xboole_0('#skF_1', k3_xboole_0(A_1, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_990])).
% 2.75/1.39  tff(c_128, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.39  tff(c_20, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.39  tff(c_21, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 2.75/1.39  tff(c_136, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_128, c_21])).
% 2.75/1.39  tff(c_1399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1027, c_136])).
% 2.75/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  Inference rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Ref     : 0
% 2.75/1.39  #Sup     : 340
% 2.75/1.39  #Fact    : 0
% 2.75/1.39  #Define  : 0
% 2.75/1.39  #Split   : 0
% 2.75/1.39  #Chain   : 0
% 2.75/1.39  #Close   : 0
% 2.75/1.39  
% 2.75/1.39  Ordering : KBO
% 2.75/1.39  
% 2.75/1.39  Simplification rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Subsume      : 0
% 2.75/1.39  #Demod        : 254
% 2.75/1.39  #Tautology    : 262
% 2.75/1.39  #SimpNegUnit  : 0
% 2.75/1.39  #BackRed      : 1
% 2.75/1.39  
% 2.75/1.39  #Partial instantiations: 0
% 2.75/1.39  #Strategies tried      : 1
% 2.75/1.39  
% 2.75/1.39  Timing (in seconds)
% 2.75/1.39  ----------------------
% 2.75/1.39  Preprocessing        : 0.28
% 2.75/1.39  Parsing              : 0.15
% 2.75/1.39  CNF conversion       : 0.02
% 2.75/1.39  Main loop            : 0.35
% 2.75/1.39  Inferencing          : 0.12
% 2.75/1.39  Reduction            : 0.15
% 2.75/1.39  Demodulation         : 0.12
% 2.75/1.39  BG Simplification    : 0.01
% 2.75/1.39  Subsumption          : 0.05
% 2.75/1.39  Abstraction          : 0.02
% 2.75/1.39  MUC search           : 0.00
% 2.75/1.39  Cooper               : 0.00
% 2.75/1.39  Total                : 0.65
% 2.75/1.39  Index Insertion      : 0.00
% 2.75/1.39  Index Deletion       : 0.00
% 2.75/1.39  Index Matching       : 0.00
% 2.75/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
