%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:03 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  35 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_10,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [B_8,A_9] :
      ( r1_xboole_0(B_8,A_9)
      | ~ r1_xboole_0(A_9,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_12])).

tff(c_53,plain,(
    ! [A_12,B_13,C_14] :
      ( ~ r1_xboole_0(A_12,B_13)
      | r1_xboole_0(A_12,k3_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [B_18,C_19,A_20] :
      ( r1_xboole_0(k3_xboole_0(B_18,C_19),A_20)
      | ~ r1_xboole_0(A_20,B_18) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_15,B_16,A_17] :
      ( ~ r1_xboole_0(A_15,B_16)
      | r1_xboole_0(A_15,k3_xboole_0(A_17,B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_53])).

tff(c_8,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_79,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_11])).

tff(c_84,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_79])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  %$ r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.82/1.22  
% 1.82/1.22  %Foreground sorts:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Background operators:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Foreground operators:
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.22  
% 1.82/1.22  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 1.82/1.22  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.82/1.22  tff(f_37, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 1.82/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.82/1.22  tff(c_10, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.82/1.22  tff(c_12, plain, (![B_8, A_9]: (r1_xboole_0(B_8, A_9) | ~r1_xboole_0(A_9, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.22  tff(c_15, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_10, c_12])).
% 1.82/1.22  tff(c_53, plain, (![A_12, B_13, C_14]: (~r1_xboole_0(A_12, B_13) | r1_xboole_0(A_12, k3_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.22  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.22  tff(c_81, plain, (![B_18, C_19, A_20]: (r1_xboole_0(k3_xboole_0(B_18, C_19), A_20) | ~r1_xboole_0(A_20, B_18))), inference(resolution, [status(thm)], [c_53, c_4])).
% 1.82/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.22  tff(c_67, plain, (![A_15, B_16, A_17]: (~r1_xboole_0(A_15, B_16) | r1_xboole_0(A_15, k3_xboole_0(A_17, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_53])).
% 1.82/1.22  tff(c_8, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.82/1.22  tff(c_11, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 1.82/1.22  tff(c_79, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_67, c_11])).
% 1.82/1.22  tff(c_84, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_81, c_79])).
% 1.82/1.22  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15, c_84])).
% 1.82/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  Inference rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Ref     : 0
% 1.82/1.22  #Sup     : 24
% 1.82/1.22  #Fact    : 0
% 1.82/1.22  #Define  : 0
% 1.82/1.22  #Split   : 0
% 1.82/1.22  #Chain   : 0
% 1.82/1.22  #Close   : 0
% 1.82/1.22  
% 1.82/1.22  Ordering : KBO
% 1.82/1.22  
% 1.82/1.22  Simplification rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Subsume      : 2
% 1.82/1.22  #Demod        : 3
% 1.82/1.22  #Tautology    : 9
% 1.82/1.22  #SimpNegUnit  : 0
% 1.82/1.22  #BackRed      : 0
% 1.82/1.22  
% 1.82/1.22  #Partial instantiations: 0
% 1.82/1.22  #Strategies tried      : 1
% 1.82/1.22  
% 1.82/1.22  Timing (in seconds)
% 1.82/1.22  ----------------------
% 1.82/1.23  Preprocessing        : 0.28
% 1.82/1.23  Parsing              : 0.16
% 1.82/1.23  CNF conversion       : 0.02
% 1.82/1.23  Main loop            : 0.13
% 1.82/1.23  Inferencing          : 0.05
% 1.82/1.23  Reduction            : 0.05
% 1.82/1.23  Demodulation         : 0.04
% 1.86/1.23  BG Simplification    : 0.01
% 1.86/1.23  Subsumption          : 0.02
% 1.86/1.23  Abstraction          : 0.01
% 1.86/1.23  MUC search           : 0.00
% 1.86/1.23  Cooper               : 0.00
% 1.86/1.23  Total                : 0.45
% 1.86/1.23  Index Insertion      : 0.00
% 1.86/1.23  Index Deletion       : 0.00
% 1.86/1.23  Index Matching       : 0.00
% 1.86/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
