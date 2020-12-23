%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:31 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [B_10,A_11] :
      ( r1_xboole_0(B_10,A_11)
      | ~ r1_xboole_0(A_11,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15,plain,(
    ! [B_7,A_6] : r1_xboole_0(B_7,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_6,c_12])).

tff(c_21,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_xboole_0(A_14,C_15)
      | ~ r1_xboole_0(B_16,C_15)
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [A_20,A_21,B_22] :
      ( r1_xboole_0(A_20,k4_xboole_0(A_21,B_22))
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(resolution,[status(thm)],[c_15,c_21])).

tff(c_8,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_29,c_8])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.14  
% 1.52/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.14  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.52/1.14  
% 1.52/1.14  %Foreground sorts:
% 1.52/1.14  
% 1.52/1.14  
% 1.52/1.14  %Background operators:
% 1.52/1.14  
% 1.52/1.14  
% 1.52/1.14  %Foreground operators:
% 1.52/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.52/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.52/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.52/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.52/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.14  
% 1.52/1.15  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.52/1.15  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.52/1.15  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.52/1.15  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.52/1.15  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.52/1.15  tff(c_6, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.52/1.15  tff(c_12, plain, (![B_10, A_11]: (r1_xboole_0(B_10, A_11) | ~r1_xboole_0(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.15  tff(c_15, plain, (![B_7, A_6]: (r1_xboole_0(B_7, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_6, c_12])).
% 1.52/1.15  tff(c_21, plain, (![A_14, C_15, B_16]: (r1_xboole_0(A_14, C_15) | ~r1_xboole_0(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.52/1.15  tff(c_29, plain, (![A_20, A_21, B_22]: (r1_xboole_0(A_20, k4_xboole_0(A_21, B_22)) | ~r1_tarski(A_20, B_22))), inference(resolution, [status(thm)], [c_15, c_21])).
% 1.52/1.15  tff(c_8, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.52/1.15  tff(c_36, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_29, c_8])).
% 1.52/1.15  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_36])).
% 1.52/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.15  
% 1.52/1.15  Inference rules
% 1.52/1.15  ----------------------
% 1.52/1.15  #Ref     : 0
% 1.52/1.15  #Sup     : 7
% 1.52/1.15  #Fact    : 0
% 1.52/1.15  #Define  : 0
% 1.52/1.15  #Split   : 0
% 1.52/1.15  #Chain   : 0
% 1.52/1.15  #Close   : 0
% 1.52/1.15  
% 1.52/1.15  Ordering : KBO
% 1.52/1.15  
% 1.52/1.15  Simplification rules
% 1.52/1.15  ----------------------
% 1.52/1.15  #Subsume      : 0
% 1.52/1.15  #Demod        : 2
% 1.52/1.15  #Tautology    : 1
% 1.52/1.15  #SimpNegUnit  : 0
% 1.52/1.15  #BackRed      : 0
% 1.52/1.15  
% 1.52/1.15  #Partial instantiations: 0
% 1.52/1.15  #Strategies tried      : 1
% 1.52/1.15  
% 1.52/1.15  Timing (in seconds)
% 1.52/1.15  ----------------------
% 1.52/1.15  Preprocessing        : 0.26
% 1.52/1.15  Parsing              : 0.14
% 1.52/1.15  CNF conversion       : 0.02
% 1.52/1.16  Main loop            : 0.09
% 1.52/1.16  Inferencing          : 0.04
% 1.52/1.16  Reduction            : 0.02
% 1.52/1.16  Demodulation         : 0.02
% 1.52/1.16  BG Simplification    : 0.01
% 1.52/1.16  Subsumption          : 0.02
% 1.52/1.16  Abstraction          : 0.00
% 1.52/1.16  MUC search           : 0.00
% 1.52/1.16  Cooper               : 0.00
% 1.52/1.16  Total                : 0.38
% 1.52/1.16  Index Insertion      : 0.00
% 1.52/1.16  Index Deletion       : 0.00
% 1.52/1.16  Index Matching       : 0.00
% 1.52/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
