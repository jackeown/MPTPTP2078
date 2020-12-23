%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:19 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  29 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [B_10,A_11] :
      ( r1_xboole_0(B_10,A_11)
      | ~ r1_xboole_0(A_11,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_12])).

tff(c_20,plain,(
    ! [A_12,C_13,B_14] :
      ( r1_xboole_0(A_12,C_13)
      | ~ r1_xboole_0(B_14,C_13)
      | ~ r1_tarski(A_12,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_16] :
      ( r1_xboole_0(A_16,'#skF_1')
      | ~ r1_tarski(A_16,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_15,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    ! [A_20] :
      ( r1_xboole_0('#skF_1',A_20)
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_8,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_8])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:15:40 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.12  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.59/1.12  
% 1.59/1.12  %Foreground sorts:
% 1.59/1.12  
% 1.59/1.12  
% 1.59/1.12  %Background operators:
% 1.59/1.12  
% 1.59/1.12  
% 1.59/1.12  %Foreground operators:
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.59/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.59/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.12  
% 1.59/1.13  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.59/1.13  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 1.59/1.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.59/1.13  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.59/1.13  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.13  tff(c_10, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.13  tff(c_12, plain, (![B_10, A_11]: (r1_xboole_0(B_10, A_11) | ~r1_xboole_0(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.13  tff(c_15, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_10, c_12])).
% 1.59/1.13  tff(c_20, plain, (![A_12, C_13, B_14]: (r1_xboole_0(A_12, C_13) | ~r1_xboole_0(B_14, C_13) | ~r1_tarski(A_12, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.59/1.13  tff(c_34, plain, (![A_16]: (r1_xboole_0(A_16, '#skF_1') | ~r1_tarski(A_16, '#skF_2'))), inference(resolution, [status(thm)], [c_15, c_20])).
% 1.59/1.13  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.13  tff(c_52, plain, (![A_20]: (r1_xboole_0('#skF_1', A_20) | ~r1_tarski(A_20, '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_2])).
% 1.59/1.13  tff(c_8, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.13  tff(c_59, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_52, c_8])).
% 1.59/1.13  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_59])).
% 1.59/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.13  
% 1.59/1.13  Inference rules
% 1.59/1.13  ----------------------
% 1.59/1.13  #Ref     : 0
% 1.59/1.13  #Sup     : 14
% 1.59/1.13  #Fact    : 0
% 1.59/1.13  #Define  : 0
% 1.59/1.13  #Split   : 0
% 1.59/1.13  #Chain   : 0
% 1.59/1.13  #Close   : 0
% 1.59/1.13  
% 1.59/1.13  Ordering : KBO
% 1.59/1.13  
% 1.59/1.13  Simplification rules
% 1.59/1.13  ----------------------
% 1.59/1.13  #Subsume      : 2
% 1.59/1.13  #Demod        : 2
% 1.59/1.13  #Tautology    : 1
% 1.59/1.13  #SimpNegUnit  : 0
% 1.59/1.13  #BackRed      : 0
% 1.59/1.13  
% 1.59/1.13  #Partial instantiations: 0
% 1.59/1.13  #Strategies tried      : 1
% 1.59/1.13  
% 1.59/1.13  Timing (in seconds)
% 1.59/1.13  ----------------------
% 1.59/1.13  Preprocessing        : 0.24
% 1.59/1.13  Parsing              : 0.14
% 1.59/1.13  CNF conversion       : 0.01
% 1.59/1.13  Main loop            : 0.11
% 1.59/1.13  Inferencing          : 0.05
% 1.59/1.13  Reduction            : 0.03
% 1.59/1.13  Demodulation         : 0.02
% 1.59/1.13  BG Simplification    : 0.01
% 1.59/1.13  Subsumption          : 0.03
% 1.59/1.13  Abstraction          : 0.00
% 1.59/1.13  MUC search           : 0.00
% 1.59/1.13  Cooper               : 0.00
% 1.59/1.13  Total                : 0.38
% 1.59/1.13  Index Insertion      : 0.00
% 1.59/1.13  Index Deletion       : 0.00
% 1.59/1.13  Index Matching       : 0.00
% 1.59/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
