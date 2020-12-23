%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:41 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11,plain,(
    ! [A_12,C_13,B_14] :
      ( r1_tarski(A_12,C_13)
      | ~ r1_tarski(B_14,C_13)
      | ~ r1_tarski(A_12,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_18,A_19,B_20] :
      ( r1_tarski(A_18,k2_xboole_0(A_19,B_20))
      | ~ r1_tarski(A_18,A_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_11])).

tff(c_8,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_8])).

tff(c_34,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:10:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.09  
% 1.53/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.10  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.53/1.10  
% 1.53/1.10  %Foreground sorts:
% 1.53/1.10  
% 1.53/1.10  
% 1.53/1.10  %Background operators:
% 1.53/1.10  
% 1.53/1.10  
% 1.53/1.10  %Foreground operators:
% 1.53/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.53/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.53/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.53/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.53/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.53/1.10  
% 1.53/1.10  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.53/1.10  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.53/1.10  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.53/1.10  tff(f_38, negated_conjecture, ~(![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.53/1.10  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.53/1.10  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.53/1.10  tff(c_11, plain, (![A_12, C_13, B_14]: (r1_tarski(A_12, C_13) | ~r1_tarski(B_14, C_13) | ~r1_tarski(A_12, B_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.53/1.10  tff(c_24, plain, (![A_18, A_19, B_20]: (r1_tarski(A_18, k2_xboole_0(A_19, B_20)) | ~r1_tarski(A_18, A_19))), inference(resolution, [status(thm)], [c_6, c_11])).
% 1.53/1.10  tff(c_8, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.53/1.10  tff(c_29, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_24, c_8])).
% 1.53/1.10  tff(c_34, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_29])).
% 1.53/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.10  
% 1.53/1.10  Inference rules
% 1.53/1.10  ----------------------
% 1.53/1.10  #Ref     : 0
% 1.53/1.10  #Sup     : 5
% 1.53/1.10  #Fact    : 0
% 1.53/1.10  #Define  : 0
% 1.53/1.10  #Split   : 0
% 1.53/1.10  #Chain   : 0
% 1.53/1.10  #Close   : 0
% 1.53/1.10  
% 1.53/1.10  Ordering : KBO
% 1.53/1.10  
% 1.53/1.10  Simplification rules
% 1.53/1.10  ----------------------
% 1.53/1.10  #Subsume      : 0
% 1.53/1.10  #Demod        : 1
% 1.53/1.10  #Tautology    : 0
% 1.53/1.10  #SimpNegUnit  : 0
% 1.53/1.10  #BackRed      : 0
% 1.53/1.10  
% 1.53/1.10  #Partial instantiations: 0
% 1.53/1.10  #Strategies tried      : 1
% 1.53/1.10  
% 1.53/1.10  Timing (in seconds)
% 1.53/1.10  ----------------------
% 1.53/1.11  Preprocessing        : 0.23
% 1.53/1.11  Parsing              : 0.13
% 1.53/1.11  CNF conversion       : 0.01
% 1.53/1.11  Main loop            : 0.07
% 1.53/1.11  Inferencing          : 0.03
% 1.53/1.11  Reduction            : 0.02
% 1.53/1.11  Demodulation         : 0.02
% 1.53/1.11  BG Simplification    : 0.01
% 1.53/1.11  Subsumption          : 0.01
% 1.53/1.11  Abstraction          : 0.00
% 1.53/1.11  MUC search           : 0.00
% 1.53/1.11  Cooper               : 0.00
% 1.53/1.11  Total                : 0.33
% 1.53/1.11  Index Insertion      : 0.00
% 1.53/1.11  Index Deletion       : 0.00
% 1.53/1.11  Index Matching       : 0.00
% 1.53/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
