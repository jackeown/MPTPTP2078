%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:35 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_14,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8])).

tff(c_10,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_57,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_xboole_0(A_19,B_20)
      | ~ r1_tarski(C_21,B_20)
      | ~ r1_tarski(C_21,A_19)
      | v1_xboole_0(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    ! [C_22] :
      ( ~ r1_tarski(C_22,'#skF_1')
      | ~ r1_tarski(C_22,'#skF_2')
      | v1_xboole_0(C_22) ) ),
    inference(resolution,[status(thm)],[c_10,c_57])).

tff(c_65,plain,
    ( ~ r1_tarski('#skF_2','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_68,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_65])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.46  
% 2.06/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.47  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 2.06/1.47  
% 2.06/1.47  %Foreground sorts:
% 2.06/1.47  
% 2.06/1.47  
% 2.06/1.47  %Background operators:
% 2.06/1.47  
% 2.06/1.47  
% 2.06/1.47  %Foreground operators:
% 2.06/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.47  
% 2.06/1.48  tff(f_50, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.06/1.48  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.06/1.48  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.06/1.48  tff(f_39, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.06/1.48  tff(c_14, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.48  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.48  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k3_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.48  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.48  tff(c_22, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8])).
% 2.06/1.48  tff(c_10, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.48  tff(c_57, plain, (![A_19, B_20, C_21]: (~r1_xboole_0(A_19, B_20) | ~r1_tarski(C_21, B_20) | ~r1_tarski(C_21, A_19) | v1_xboole_0(C_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.48  tff(c_61, plain, (![C_22]: (~r1_tarski(C_22, '#skF_1') | ~r1_tarski(C_22, '#skF_2') | v1_xboole_0(C_22))), inference(resolution, [status(thm)], [c_10, c_57])).
% 2.06/1.48  tff(c_65, plain, (~r1_tarski('#skF_2', '#skF_1') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_61])).
% 2.06/1.48  tff(c_68, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_65])).
% 2.06/1.48  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_68])).
% 2.06/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.48  
% 2.06/1.48  Inference rules
% 2.06/1.48  ----------------------
% 2.06/1.48  #Ref     : 0
% 2.06/1.48  #Sup     : 12
% 2.06/1.48  #Fact    : 0
% 2.06/1.48  #Define  : 0
% 2.06/1.48  #Split   : 0
% 2.06/1.48  #Chain   : 0
% 2.06/1.48  #Close   : 0
% 2.06/1.48  
% 2.06/1.48  Ordering : KBO
% 2.06/1.48  
% 2.06/1.48  Simplification rules
% 2.06/1.48  ----------------------
% 2.06/1.48  #Subsume      : 0
% 2.06/1.48  #Demod        : 2
% 2.06/1.48  #Tautology    : 7
% 2.06/1.48  #SimpNegUnit  : 1
% 2.06/1.48  #BackRed      : 0
% 2.06/1.48  
% 2.06/1.48  #Partial instantiations: 0
% 2.06/1.48  #Strategies tried      : 1
% 2.06/1.48  
% 2.06/1.48  Timing (in seconds)
% 2.06/1.48  ----------------------
% 2.06/1.49  Preprocessing        : 0.41
% 2.06/1.49  Parsing              : 0.22
% 2.06/1.49  CNF conversion       : 0.03
% 2.06/1.49  Main loop            : 0.17
% 2.06/1.49  Inferencing          : 0.09
% 2.06/1.49  Reduction            : 0.05
% 2.06/1.49  Demodulation         : 0.04
% 2.06/1.49  BG Simplification    : 0.01
% 2.06/1.49  Subsumption          : 0.02
% 2.06/1.49  Abstraction          : 0.01
% 2.06/1.49  MUC search           : 0.00
% 2.06/1.49  Cooper               : 0.00
% 2.06/1.49  Total                : 0.62
% 2.06/1.49  Index Insertion      : 0.00
% 2.06/1.49  Index Deletion       : 0.00
% 2.06/1.49  Index Matching       : 0.00
% 2.06/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
