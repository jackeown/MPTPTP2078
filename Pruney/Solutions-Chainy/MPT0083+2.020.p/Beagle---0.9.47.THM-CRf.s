%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:03 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  30 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_13,plain,(
    ! [B_11,A_12] : k3_xboole_0(B_11,A_12) = k3_xboole_0(A_12,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [B_11,A_12] : r1_tarski(k3_xboole_0(B_11,A_12),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_4])).

tff(c_10,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [A_15,C_16,B_17,D_18] :
      ( r1_xboole_0(A_15,C_16)
      | ~ r1_xboole_0(B_17,D_18)
      | ~ r1_tarski(C_16,D_18)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_19,C_20] :
      ( r1_xboole_0(A_19,C_20)
      | ~ r1_tarski(C_20,'#skF_2')
      | ~ r1_tarski(A_19,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_71,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_11])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.05  
% 1.53/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.05  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.53/1.05  
% 1.53/1.05  %Foreground sorts:
% 1.53/1.05  
% 1.53/1.05  
% 1.53/1.05  %Background operators:
% 1.53/1.05  
% 1.53/1.05  
% 1.53/1.05  %Foreground operators:
% 1.53/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.53/1.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.53/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.53/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.53/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.53/1.05  
% 1.53/1.06  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.53/1.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.53/1.06  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 1.53/1.06  tff(f_37, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 1.53/1.06  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.53/1.06  tff(c_13, plain, (![B_11, A_12]: (k3_xboole_0(B_11, A_12)=k3_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.53/1.06  tff(c_28, plain, (![B_11, A_12]: (r1_tarski(k3_xboole_0(B_11, A_12), A_12))), inference(superposition, [status(thm), theory('equality')], [c_13, c_4])).
% 1.53/1.06  tff(c_10, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.53/1.06  tff(c_62, plain, (![A_15, C_16, B_17, D_18]: (r1_xboole_0(A_15, C_16) | ~r1_xboole_0(B_17, D_18) | ~r1_tarski(C_16, D_18) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.53/1.06  tff(c_66, plain, (![A_19, C_20]: (r1_xboole_0(A_19, C_20) | ~r1_tarski(C_20, '#skF_2') | ~r1_tarski(A_19, '#skF_1'))), inference(resolution, [status(thm)], [c_10, c_62])).
% 1.53/1.06  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.53/1.06  tff(c_8, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.53/1.06  tff(c_11, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 1.53/1.06  tff(c_71, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_66, c_11])).
% 1.53/1.06  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_28, c_71])).
% 1.53/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.06  
% 1.53/1.06  Inference rules
% 1.53/1.06  ----------------------
% 1.53/1.06  #Ref     : 0
% 1.53/1.06  #Sup     : 15
% 1.53/1.06  #Fact    : 0
% 1.53/1.06  #Define  : 0
% 1.53/1.06  #Split   : 0
% 1.53/1.06  #Chain   : 0
% 1.53/1.06  #Close   : 0
% 1.53/1.06  
% 1.53/1.06  Ordering : KBO
% 1.53/1.06  
% 1.53/1.06  Simplification rules
% 1.53/1.06  ----------------------
% 1.53/1.06  #Subsume      : 0
% 1.53/1.06  #Demod        : 6
% 1.53/1.06  #Tautology    : 11
% 1.53/1.06  #SimpNegUnit  : 0
% 1.53/1.06  #BackRed      : 0
% 1.53/1.06  
% 1.53/1.06  #Partial instantiations: 0
% 1.53/1.06  #Strategies tried      : 1
% 1.53/1.06  
% 1.53/1.06  Timing (in seconds)
% 1.53/1.06  ----------------------
% 1.53/1.06  Preprocessing        : 0.25
% 1.53/1.06  Parsing              : 0.14
% 1.53/1.06  CNF conversion       : 0.01
% 1.53/1.06  Main loop            : 0.10
% 1.53/1.06  Inferencing          : 0.03
% 1.53/1.06  Reduction            : 0.04
% 1.53/1.06  Demodulation         : 0.03
% 1.53/1.06  BG Simplification    : 0.01
% 1.53/1.06  Subsumption          : 0.01
% 1.53/1.06  Abstraction          : 0.00
% 1.53/1.06  MUC search           : 0.00
% 1.53/1.06  Cooper               : 0.00
% 1.53/1.06  Total                : 0.37
% 1.53/1.06  Index Insertion      : 0.00
% 1.53/1.06  Index Deletion       : 0.00
% 1.53/1.06  Index Matching       : 0.00
% 1.53/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
