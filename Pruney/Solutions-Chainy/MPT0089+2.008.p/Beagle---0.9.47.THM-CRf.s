%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:24 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_xboole_0(k4_xboole_0(A_1,B_2),B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_xboole_0(A_8,k4_xboole_0(B_9,C_10))
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_11,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_6])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.06  %$ r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.49/1.06  
% 1.49/1.06  %Foreground sorts:
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  %Background operators:
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  %Foreground operators:
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.49/1.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.49/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.06  
% 1.49/1.07  tff(f_27, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.49/1.07  tff(f_31, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 1.49/1.07  tff(f_34, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 1.49/1.07  tff(c_2, plain, (![A_1, B_2]: (r1_xboole_0(k4_xboole_0(A_1, B_2), B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.49/1.07  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_xboole_0(A_8, k4_xboole_0(B_9, C_10)) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.49/1.07  tff(c_6, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.49/1.07  tff(c_11, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_8, c_6])).
% 1.49/1.07  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_11])).
% 1.49/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.07  
% 1.52/1.07  Inference rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Ref     : 0
% 1.52/1.07  #Sup     : 1
% 1.52/1.07  #Fact    : 0
% 1.52/1.07  #Define  : 0
% 1.52/1.07  #Split   : 0
% 1.52/1.07  #Chain   : 0
% 1.52/1.07  #Close   : 0
% 1.52/1.07  
% 1.52/1.07  Ordering : KBO
% 1.52/1.07  
% 1.52/1.07  Simplification rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Subsume      : 0
% 1.52/1.07  #Demod        : 1
% 1.52/1.07  #Tautology    : 0
% 1.52/1.07  #SimpNegUnit  : 0
% 1.52/1.07  #BackRed      : 0
% 1.52/1.07  
% 1.52/1.07  #Partial instantiations: 0
% 1.52/1.07  #Strategies tried      : 1
% 1.52/1.07  
% 1.52/1.07  Timing (in seconds)
% 1.52/1.07  ----------------------
% 1.52/1.07  Preprocessing        : 0.24
% 1.52/1.07  Parsing              : 0.13
% 1.52/1.07  CNF conversion       : 0.01
% 1.52/1.07  Main loop            : 0.05
% 1.52/1.07  Inferencing          : 0.02
% 1.52/1.07  Reduction            : 0.01
% 1.52/1.07  Demodulation         : 0.01
% 1.52/1.07  BG Simplification    : 0.01
% 1.52/1.07  Subsumption          : 0.01
% 1.52/1.07  Abstraction          : 0.00
% 1.52/1.07  MUC search           : 0.00
% 1.52/1.07  Cooper               : 0.00
% 1.52/1.07  Total                : 0.32
% 1.52/1.07  Index Insertion      : 0.00
% 1.52/1.07  Index Deletion       : 0.00
% 1.52/1.07  Index Matching       : 0.00
% 1.52/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
