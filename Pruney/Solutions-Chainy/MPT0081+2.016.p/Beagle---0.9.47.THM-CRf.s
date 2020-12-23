%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:58 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_24,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4])).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17,plain,(
    ! [B_14,A_15] :
      ( r1_xboole_0(B_14,A_15)
      | ~ r1_xboole_0(A_15,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_17])).

tff(c_52,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_xboole_0(A_21,C_22)
      | ~ r1_xboole_0(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_27] :
      ( r1_xboole_0(A_27,'#skF_1')
      | ~ r1_tarski(A_27,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_23,c_52])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    ! [A_31] :
      ( r1_xboole_0('#skF_1',A_31)
      | ~ r1_tarski(A_31,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_121,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_14])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:34:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.20  
% 1.77/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.21  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.77/1.21  
% 1.77/1.21  %Foreground sorts:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Background operators:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Foreground operators:
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.77/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.21  
% 1.77/1.22  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.77/1.22  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.77/1.22  tff(f_48, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 1.77/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.77/1.22  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.77/1.22  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.22  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.22  tff(c_33, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4])).
% 1.77/1.22  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.22  tff(c_17, plain, (![B_14, A_15]: (r1_xboole_0(B_14, A_15) | ~r1_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.22  tff(c_23, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_12, c_17])).
% 1.77/1.22  tff(c_52, plain, (![A_21, C_22, B_23]: (r1_xboole_0(A_21, C_22) | ~r1_xboole_0(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.77/1.22  tff(c_84, plain, (![A_27]: (r1_xboole_0(A_27, '#skF_1') | ~r1_tarski(A_27, '#skF_2'))), inference(resolution, [status(thm)], [c_23, c_52])).
% 1.77/1.22  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.22  tff(c_114, plain, (![A_31]: (r1_xboole_0('#skF_1', A_31) | ~r1_tarski(A_31, '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_2])).
% 1.77/1.22  tff(c_14, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.77/1.22  tff(c_121, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_114, c_14])).
% 1.77/1.22  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_121])).
% 1.77/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.22  
% 1.77/1.22  Inference rules
% 1.77/1.22  ----------------------
% 1.77/1.22  #Ref     : 0
% 1.77/1.22  #Sup     : 29
% 1.77/1.22  #Fact    : 0
% 1.77/1.22  #Define  : 0
% 1.77/1.22  #Split   : 0
% 1.77/1.22  #Chain   : 0
% 1.77/1.22  #Close   : 0
% 1.77/1.22  
% 1.77/1.22  Ordering : KBO
% 1.77/1.22  
% 1.77/1.22  Simplification rules
% 1.77/1.22  ----------------------
% 1.77/1.22  #Subsume      : 2
% 1.77/1.22  #Demod        : 5
% 1.77/1.22  #Tautology    : 8
% 1.77/1.22  #SimpNegUnit  : 0
% 1.77/1.22  #BackRed      : 0
% 1.77/1.22  
% 1.77/1.22  #Partial instantiations: 0
% 1.77/1.22  #Strategies tried      : 1
% 1.77/1.22  
% 1.77/1.22  Timing (in seconds)
% 1.77/1.22  ----------------------
% 1.77/1.22  Preprocessing        : 0.26
% 1.77/1.22  Parsing              : 0.15
% 1.77/1.22  CNF conversion       : 0.01
% 1.77/1.22  Main loop            : 0.14
% 1.77/1.22  Inferencing          : 0.06
% 1.77/1.22  Reduction            : 0.04
% 1.77/1.22  Demodulation         : 0.03
% 1.77/1.22  BG Simplification    : 0.01
% 1.77/1.22  Subsumption          : 0.03
% 1.77/1.22  Abstraction          : 0.01
% 1.77/1.22  MUC search           : 0.00
% 1.77/1.22  Cooper               : 0.00
% 1.77/1.22  Total                : 0.43
% 1.77/1.22  Index Insertion      : 0.00
% 1.77/1.22  Index Deletion       : 0.00
% 1.77/1.22  Index Matching       : 0.00
% 1.77/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
