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
% DateTime   : Thu Dec  3 09:43:04 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(k4_xboole_0(A_7,B_8),k3_xboole_0(A_7,B_8)) = A_7
      | ~ r1_tarski(k4_xboole_0(A_7,B_8),A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_77,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_73])).

tff(c_10,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:15:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.09  
% 1.56/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.09  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.56/1.09  
% 1.56/1.09  %Foreground sorts:
% 1.56/1.09  
% 1.56/1.09  
% 1.56/1.09  %Background operators:
% 1.56/1.09  
% 1.56/1.09  
% 1.56/1.09  %Foreground operators:
% 1.56/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.56/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.56/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.09  
% 1.68/1.10  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.68/1.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.68/1.10  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.68/1.10  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.68/1.10  tff(f_38, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.68/1.10  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.10  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.10  tff(c_64, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.10  tff(c_73, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), k3_xboole_0(A_7, B_8))=A_7 | ~r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 1.68/1.10  tff(c_77, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_73])).
% 1.68/1.10  tff(c_10, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.10  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_10])).
% 1.68/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.10  
% 1.68/1.10  Inference rules
% 1.68/1.10  ----------------------
% 1.68/1.10  #Ref     : 0
% 1.68/1.10  #Sup     : 16
% 1.68/1.10  #Fact    : 0
% 1.68/1.10  #Define  : 0
% 1.68/1.10  #Split   : 0
% 1.68/1.10  #Chain   : 0
% 1.68/1.10  #Close   : 0
% 1.68/1.10  
% 1.68/1.10  Ordering : KBO
% 1.68/1.10  
% 1.68/1.10  Simplification rules
% 1.68/1.10  ----------------------
% 1.68/1.10  #Subsume      : 0
% 1.68/1.10  #Demod        : 3
% 1.68/1.10  #Tautology    : 12
% 1.68/1.10  #SimpNegUnit  : 0
% 1.68/1.10  #BackRed      : 1
% 1.68/1.10  
% 1.68/1.10  #Partial instantiations: 0
% 1.68/1.10  #Strategies tried      : 1
% 1.68/1.10  
% 1.68/1.10  Timing (in seconds)
% 1.68/1.10  ----------------------
% 1.68/1.11  Preprocessing        : 0.25
% 1.68/1.11  Parsing              : 0.14
% 1.68/1.11  CNF conversion       : 0.01
% 1.68/1.11  Main loop            : 0.09
% 1.68/1.11  Inferencing          : 0.04
% 1.68/1.11  Reduction            : 0.03
% 1.68/1.11  Demodulation         : 0.03
% 1.68/1.11  BG Simplification    : 0.01
% 1.68/1.11  Subsumption          : 0.01
% 1.68/1.11  Abstraction          : 0.00
% 1.68/1.11  MUC search           : 0.00
% 1.68/1.11  Cooper               : 0.00
% 1.68/1.11  Total                : 0.36
% 1.68/1.11  Index Insertion      : 0.00
% 1.68/1.11  Index Deletion       : 0.00
% 1.68/1.11  Index Matching       : 0.00
% 1.68/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
