%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:12 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   12 (  13 expanded)
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

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_10,c_32])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_61,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k3_xboole_0(A_21,B_22),k3_xboole_0(A_21,C_23)) = k3_xboole_0(A_21,k2_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [C_23] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_23)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_61])).

tff(c_76,plain,(
    ! [C_23] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_23)) = k3_xboole_0('#skF_1',C_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_70])).

tff(c_14,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:21:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.18  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.71/1.18  
% 1.71/1.18  %Foreground sorts:
% 1.71/1.18  
% 1.71/1.18  
% 1.71/1.18  %Background operators:
% 1.71/1.18  
% 1.71/1.18  
% 1.71/1.18  %Foreground operators:
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.18  
% 1.71/1.19  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.71/1.19  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.71/1.19  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 1.71/1.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.71/1.19  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 1.71/1.19  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.19  tff(c_32, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.19  tff(c_36, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_10, c_32])).
% 1.71/1.19  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.19  tff(c_19, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.19  tff(c_27, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_19])).
% 1.71/1.19  tff(c_61, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k3_xboole_0(A_21, C_23))=k3_xboole_0(A_21, k2_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.19  tff(c_70, plain, (![C_23]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_23))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_23)))), inference(superposition, [status(thm), theory('equality')], [c_27, c_61])).
% 1.71/1.19  tff(c_76, plain, (![C_23]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_23))=k3_xboole_0('#skF_1', C_23))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_70])).
% 1.71/1.19  tff(c_14, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.19  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_14])).
% 1.71/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.19  
% 1.71/1.19  Inference rules
% 1.71/1.19  ----------------------
% 1.71/1.19  #Ref     : 0
% 1.71/1.19  #Sup     : 15
% 1.71/1.19  #Fact    : 0
% 1.71/1.19  #Define  : 0
% 1.71/1.19  #Split   : 0
% 1.71/1.19  #Chain   : 0
% 1.71/1.19  #Close   : 0
% 1.71/1.19  
% 1.71/1.19  Ordering : KBO
% 1.71/1.19  
% 1.71/1.19  Simplification rules
% 1.71/1.19  ----------------------
% 1.71/1.19  #Subsume      : 0
% 1.71/1.19  #Demod        : 2
% 1.71/1.19  #Tautology    : 9
% 1.71/1.19  #SimpNegUnit  : 0
% 1.71/1.19  #BackRed      : 1
% 1.71/1.19  
% 1.71/1.19  #Partial instantiations: 0
% 1.71/1.19  #Strategies tried      : 1
% 1.71/1.19  
% 1.71/1.19  Timing (in seconds)
% 1.71/1.19  ----------------------
% 1.76/1.19  Preprocessing        : 0.27
% 1.76/1.19  Parsing              : 0.15
% 1.76/1.19  CNF conversion       : 0.02
% 1.76/1.19  Main loop            : 0.10
% 1.76/1.19  Inferencing          : 0.05
% 1.76/1.19  Reduction            : 0.03
% 1.76/1.19  Demodulation         : 0.02
% 1.76/1.19  BG Simplification    : 0.01
% 1.76/1.19  Subsumption          : 0.01
% 1.76/1.19  Abstraction          : 0.00
% 1.76/1.19  MUC search           : 0.00
% 1.76/1.19  Cooper               : 0.00
% 1.76/1.19  Total                : 0.39
% 1.76/1.19  Index Insertion      : 0.00
% 1.76/1.19  Index Deletion       : 0.00
% 1.76/1.19  Index Matching       : 0.00
% 1.76/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
