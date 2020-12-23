%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:34 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k3_xboole_0(B,C))
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(A_16,k2_xboole_0(C_17,B_18))
      | ~ r1_tarski(A_16,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_23,B_24,A_25] :
      ( r1_tarski(A_23,k2_xboole_0(B_24,A_25))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_203,plain,(
    ! [A_30,A_31,B_32] :
      ( r1_tarski(A_30,A_31)
      | ~ r1_tarski(A_30,k3_xboole_0(A_31,B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_115])).

tff(c_213,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:03:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.28  
% 1.92/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.28  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.92/1.28  
% 1.92/1.28  %Foreground sorts:
% 1.92/1.28  
% 1.92/1.28  
% 1.92/1.28  %Background operators:
% 1.92/1.28  
% 1.92/1.28  
% 1.92/1.28  %Foreground operators:
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.28  
% 1.92/1.29  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.92/1.29  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.92/1.29  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.92/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.92/1.29  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.92/1.29  tff(c_10, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.29  tff(c_12, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.29  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.29  tff(c_47, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.29  tff(c_54, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_47])).
% 1.92/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.29  tff(c_56, plain, (![A_16, C_17, B_18]: (r1_tarski(A_16, k2_xboole_0(C_17, B_18)) | ~r1_tarski(A_16, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.29  tff(c_115, plain, (![A_23, B_24, A_25]: (r1_tarski(A_23, k2_xboole_0(B_24, A_25)) | ~r1_tarski(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_2, c_56])).
% 1.92/1.29  tff(c_203, plain, (![A_30, A_31, B_32]: (r1_tarski(A_30, A_31) | ~r1_tarski(A_30, k3_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_115])).
% 1.92/1.29  tff(c_213, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_203])).
% 1.92/1.29  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_213])).
% 1.92/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.29  
% 1.92/1.29  Inference rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Ref     : 0
% 1.92/1.29  #Sup     : 53
% 1.92/1.29  #Fact    : 0
% 1.92/1.29  #Define  : 0
% 1.92/1.29  #Split   : 0
% 1.92/1.29  #Chain   : 0
% 1.92/1.29  #Close   : 0
% 1.92/1.29  
% 1.92/1.29  Ordering : KBO
% 1.92/1.29  
% 1.92/1.29  Simplification rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Subsume      : 5
% 1.92/1.29  #Demod        : 7
% 1.92/1.29  #Tautology    : 25
% 1.92/1.29  #SimpNegUnit  : 1
% 1.92/1.29  #BackRed      : 0
% 1.92/1.29  
% 1.92/1.29  #Partial instantiations: 0
% 1.92/1.29  #Strategies tried      : 1
% 1.92/1.29  
% 1.92/1.29  Timing (in seconds)
% 1.92/1.29  ----------------------
% 1.92/1.29  Preprocessing        : 0.27
% 1.92/1.29  Parsing              : 0.15
% 1.92/1.29  CNF conversion       : 0.02
% 1.92/1.29  Main loop            : 0.19
% 1.92/1.29  Inferencing          : 0.08
% 1.92/1.29  Reduction            : 0.06
% 1.92/1.29  Demodulation         : 0.05
% 1.92/1.29  BG Simplification    : 0.02
% 1.92/1.29  Subsumption          : 0.03
% 1.92/1.29  Abstraction          : 0.01
% 1.92/1.29  MUC search           : 0.00
% 1.92/1.29  Cooper               : 0.00
% 1.92/1.29  Total                : 0.49
% 1.92/1.29  Index Insertion      : 0.00
% 1.92/1.29  Index Deletion       : 0.00
% 1.92/1.29  Index Matching       : 0.00
% 1.92/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
