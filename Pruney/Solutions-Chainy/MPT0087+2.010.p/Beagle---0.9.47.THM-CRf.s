%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:18 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_29])).

tff(c_59,plain,(
    ! [A_23,B_24] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k4_xboole_0(B_24,A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_59])).

tff(c_83,plain,(
    ! [B_6] : k4_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_114,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_127,plain,(
    ! [A_29,B_30,C_31] : k4_xboole_0(k3_xboole_0(A_29,B_30),C_31) = k3_xboole_0(A_29,k4_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,(
    ! [C_31] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_31)) = k4_xboole_0(k1_xboole_0,C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_127])).

tff(c_161,plain,(
    ! [C_31] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_31)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_150])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k3_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_16])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.12  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.71/1.12  
% 1.71/1.12  %Foreground sorts:
% 1.71/1.12  
% 1.71/1.12  
% 1.71/1.12  %Background operators:
% 1.71/1.12  
% 1.71/1.12  
% 1.71/1.12  %Foreground operators:
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.12  
% 1.71/1.13  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.71/1.13  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.71/1.13  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.71/1.13  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.71/1.13  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 1.71/1.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.71/1.13  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.71/1.13  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.13  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.13  tff(c_29, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.13  tff(c_39, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_29])).
% 1.71/1.13  tff(c_59, plain, (![A_23, B_24]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, k4_xboole_0(B_24, A_23)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.13  tff(c_72, plain, (![A_25]: (k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_39, c_59])).
% 1.71/1.13  tff(c_83, plain, (![B_6]: (k4_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_72])).
% 1.71/1.13  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.13  tff(c_114, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.13  tff(c_122, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_114])).
% 1.71/1.13  tff(c_127, plain, (![A_29, B_30, C_31]: (k4_xboole_0(k3_xboole_0(A_29, B_30), C_31)=k3_xboole_0(A_29, k4_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.71/1.13  tff(c_150, plain, (![C_31]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_31))=k4_xboole_0(k1_xboole_0, C_31))), inference(superposition, [status(thm), theory('equality')], [c_122, c_127])).
% 1.71/1.13  tff(c_161, plain, (![C_31]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_31))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_150])).
% 1.71/1.13  tff(c_42, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k3_xboole_0(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.13  tff(c_16, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.13  tff(c_46, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_16])).
% 1.71/1.13  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_46])).
% 1.71/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  Inference rules
% 1.71/1.13  ----------------------
% 1.71/1.13  #Ref     : 0
% 1.71/1.13  #Sup     : 36
% 1.71/1.13  #Fact    : 0
% 1.71/1.13  #Define  : 0
% 1.71/1.13  #Split   : 0
% 1.71/1.13  #Chain   : 0
% 1.71/1.13  #Close   : 0
% 1.71/1.13  
% 1.71/1.13  Ordering : KBO
% 1.71/1.13  
% 1.71/1.13  Simplification rules
% 1.71/1.13  ----------------------
% 1.71/1.13  #Subsume      : 2
% 1.71/1.13  #Demod        : 4
% 1.71/1.13  #Tautology    : 21
% 1.71/1.13  #SimpNegUnit  : 0
% 1.71/1.13  #BackRed      : 1
% 1.71/1.13  
% 1.71/1.13  #Partial instantiations: 0
% 1.71/1.13  #Strategies tried      : 1
% 1.71/1.13  
% 1.71/1.13  Timing (in seconds)
% 1.71/1.13  ----------------------
% 1.71/1.13  Preprocessing        : 0.26
% 1.71/1.13  Parsing              : 0.14
% 1.71/1.13  CNF conversion       : 0.02
% 1.71/1.13  Main loop            : 0.12
% 1.71/1.13  Inferencing          : 0.05
% 1.71/1.13  Reduction            : 0.04
% 1.71/1.13  Demodulation         : 0.03
% 1.71/1.13  BG Simplification    : 0.01
% 1.71/1.13  Subsumption          : 0.02
% 1.71/1.14  Abstraction          : 0.01
% 1.71/1.14  MUC search           : 0.00
% 1.71/1.14  Cooper               : 0.00
% 1.71/1.14  Total                : 0.40
% 1.71/1.14  Index Insertion      : 0.00
% 1.71/1.14  Index Deletion       : 0.00
% 1.71/1.14  Index Matching       : 0.00
% 1.71/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
