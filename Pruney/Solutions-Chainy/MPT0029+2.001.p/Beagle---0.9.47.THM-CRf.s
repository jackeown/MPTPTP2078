%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:35 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),A_13) = A_13 ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_8,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:29:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.07  
% 1.48/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.07  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.48/1.07  
% 1.48/1.07  %Foreground sorts:
% 1.48/1.07  
% 1.48/1.07  
% 1.48/1.07  %Background operators:
% 1.48/1.07  
% 1.48/1.07  
% 1.48/1.07  %Foreground operators:
% 1.48/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.48/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.48/1.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.48/1.07  
% 1.48/1.08  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.48/1.08  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.48/1.08  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.48/1.08  tff(f_36, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.48/1.08  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.48/1.08  tff(c_43, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.48/1.08  tff(c_48, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), A_13)=A_13)), inference(resolution, [status(thm)], [c_6, c_43])).
% 1.48/1.08  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.48/1.08  tff(c_54, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k3_xboole_0(A_13, B_14))=A_13)), inference(superposition, [status(thm), theory('equality')], [c_48, c_2])).
% 1.48/1.08  tff(c_8, plain, (k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.48/1.08  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 1.48/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.08  
% 1.48/1.08  Inference rules
% 1.48/1.08  ----------------------
% 1.48/1.08  #Ref     : 0
% 1.48/1.08  #Sup     : 15
% 1.48/1.08  #Fact    : 0
% 1.48/1.08  #Define  : 0
% 1.48/1.08  #Split   : 0
% 1.48/1.08  #Chain   : 0
% 1.48/1.08  #Close   : 0
% 1.48/1.08  
% 1.48/1.08  Ordering : KBO
% 1.48/1.08  
% 1.48/1.08  Simplification rules
% 1.48/1.08  ----------------------
% 1.48/1.08  #Subsume      : 0
% 1.48/1.08  #Demod        : 1
% 1.48/1.08  #Tautology    : 10
% 1.48/1.08  #SimpNegUnit  : 0
% 1.48/1.08  #BackRed      : 1
% 1.48/1.08  
% 1.48/1.08  #Partial instantiations: 0
% 1.48/1.08  #Strategies tried      : 1
% 1.48/1.08  
% 1.48/1.08  Timing (in seconds)
% 1.48/1.08  ----------------------
% 1.48/1.08  Preprocessing        : 0.23
% 1.48/1.08  Parsing              : 0.13
% 1.48/1.08  CNF conversion       : 0.01
% 1.48/1.08  Main loop            : 0.09
% 1.48/1.08  Inferencing          : 0.04
% 1.48/1.08  Reduction            : 0.02
% 1.48/1.08  Demodulation         : 0.02
% 1.48/1.08  BG Simplification    : 0.01
% 1.48/1.08  Subsumption          : 0.01
% 1.48/1.08  Abstraction          : 0.00
% 1.48/1.08  MUC search           : 0.00
% 1.48/1.08  Cooper               : 0.00
% 1.48/1.08  Total                : 0.34
% 1.48/1.08  Index Insertion      : 0.00
% 1.48/1.08  Index Deletion       : 0.00
% 1.48/1.08  Index Matching       : 0.00
% 1.48/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
