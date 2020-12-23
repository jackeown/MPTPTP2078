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
% DateTime   : Thu Dec  3 09:44:00 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_33,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k3_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_41,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_14])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_17,B_18,C_19] : k3_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k3_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_24])).

tff(c_66,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_28])).

tff(c_92,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:25:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.27  
% 1.84/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.27  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.84/1.27  
% 1.84/1.27  %Foreground sorts:
% 1.84/1.27  
% 1.84/1.27  
% 1.84/1.27  %Background operators:
% 1.84/1.27  
% 1.84/1.27  
% 1.84/1.27  %Foreground operators:
% 1.84/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.27  
% 1.84/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.84/1.28  tff(f_42, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 1.84/1.28  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.84/1.28  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.84/1.28  tff(c_33, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k3_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.28  tff(c_14, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.84/1.28  tff(c_41, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_14])).
% 1.84/1.28  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.28  tff(c_57, plain, (![A_17, B_18, C_19]: (k3_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k3_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.28  tff(c_12, plain, (r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.84/1.28  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.28  tff(c_28, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_24])).
% 1.84/1.28  tff(c_66, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_57, c_28])).
% 1.84/1.28  tff(c_92, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_66])).
% 1.84/1.28  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_92])).
% 1.84/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.28  
% 1.84/1.28  Inference rules
% 1.84/1.28  ----------------------
% 1.84/1.28  #Ref     : 0
% 1.84/1.28  #Sup     : 21
% 1.84/1.28  #Fact    : 0
% 1.84/1.28  #Define  : 0
% 1.84/1.28  #Split   : 0
% 1.84/1.28  #Chain   : 0
% 1.84/1.28  #Close   : 0
% 1.84/1.28  
% 1.84/1.28  Ordering : KBO
% 1.84/1.28  
% 1.84/1.28  Simplification rules
% 1.84/1.28  ----------------------
% 1.84/1.28  #Subsume      : 0
% 1.84/1.28  #Demod        : 4
% 1.84/1.28  #Tautology    : 9
% 1.84/1.28  #SimpNegUnit  : 1
% 1.84/1.28  #BackRed      : 0
% 1.84/1.28  
% 1.84/1.28  #Partial instantiations: 0
% 1.84/1.28  #Strategies tried      : 1
% 1.84/1.28  
% 1.84/1.28  Timing (in seconds)
% 1.84/1.28  ----------------------
% 1.84/1.28  Preprocessing        : 0.33
% 1.84/1.28  Parsing              : 0.18
% 1.84/1.28  CNF conversion       : 0.02
% 1.84/1.28  Main loop            : 0.13
% 1.84/1.28  Inferencing          : 0.06
% 1.84/1.28  Reduction            : 0.03
% 1.84/1.28  Demodulation         : 0.02
% 1.84/1.28  BG Simplification    : 0.01
% 1.84/1.28  Subsumption          : 0.02
% 1.84/1.28  Abstraction          : 0.01
% 1.84/1.28  MUC search           : 0.00
% 1.84/1.28  Cooper               : 0.00
% 1.84/1.28  Total                : 0.48
% 1.84/1.28  Index Insertion      : 0.00
% 1.84/1.28  Index Deletion       : 0.00
% 1.84/1.28  Index Matching       : 0.00
% 1.84/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
