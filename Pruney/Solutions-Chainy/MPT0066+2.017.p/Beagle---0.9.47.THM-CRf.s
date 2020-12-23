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
% DateTime   : Thu Dec  3 09:43:14 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  22 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9,plain,(
    ! [A_4,C_5,B_6] :
      ( r2_xboole_0(A_4,C_5)
      | ~ r2_xboole_0(B_6,C_5)
      | ~ r1_tarski(A_4,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13,plain,(
    ! [A_7] :
      ( r2_xboole_0(A_7,'#skF_3')
      | ~ r1_tarski(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_9])).

tff(c_4,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13,c_4])).

tff(c_23,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.16  
% 1.59/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.16  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.59/1.16  
% 1.59/1.16  %Foreground sorts:
% 1.59/1.16  
% 1.59/1.16  
% 1.59/1.16  %Background operators:
% 1.59/1.16  
% 1.59/1.16  
% 1.59/1.16  %Foreground operators:
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.16  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.16  
% 1.59/1.17  tff(f_38, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.59/1.17  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l58_xboole_1)).
% 1.59/1.17  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.17  tff(c_6, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.17  tff(c_9, plain, (![A_4, C_5, B_6]: (r2_xboole_0(A_4, C_5) | ~r2_xboole_0(B_6, C_5) | ~r1_tarski(A_4, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.17  tff(c_13, plain, (![A_7]: (r2_xboole_0(A_7, '#skF_3') | ~r1_tarski(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_9])).
% 1.59/1.17  tff(c_4, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.17  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13, c_4])).
% 1.59/1.17  tff(c_23, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 1.59/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.17  
% 1.59/1.17  Inference rules
% 1.59/1.17  ----------------------
% 1.59/1.17  #Ref     : 0
% 1.59/1.17  #Sup     : 3
% 1.59/1.17  #Fact    : 0
% 1.59/1.17  #Define  : 0
% 1.59/1.17  #Split   : 0
% 1.59/1.17  #Chain   : 0
% 1.59/1.17  #Close   : 0
% 1.59/1.17  
% 1.59/1.17  Ordering : KBO
% 1.59/1.17  
% 1.59/1.17  Simplification rules
% 1.59/1.17  ----------------------
% 1.59/1.17  #Subsume      : 0
% 1.59/1.17  #Demod        : 1
% 1.59/1.17  #Tautology    : 0
% 1.59/1.17  #SimpNegUnit  : 0
% 1.59/1.17  #BackRed      : 0
% 1.59/1.17  
% 1.59/1.17  #Partial instantiations: 0
% 1.59/1.17  #Strategies tried      : 1
% 1.59/1.17  
% 1.59/1.17  Timing (in seconds)
% 1.59/1.17  ----------------------
% 1.59/1.17  Preprocessing        : 0.29
% 1.59/1.18  Parsing              : 0.16
% 1.59/1.18  CNF conversion       : 0.02
% 1.59/1.18  Main loop            : 0.08
% 1.59/1.18  Inferencing          : 0.04
% 1.59/1.18  Reduction            : 0.02
% 1.59/1.18  Demodulation         : 0.01
% 1.59/1.18  BG Simplification    : 0.02
% 1.59/1.18  Subsumption          : 0.01
% 1.59/1.18  Abstraction          : 0.00
% 1.59/1.18  MUC search           : 0.00
% 1.59/1.18  Cooper               : 0.00
% 1.59/1.18  Total                : 0.39
% 1.59/1.18  Index Insertion      : 0.00
% 1.59/1.18  Index Deletion       : 0.00
% 1.59/1.18  Index Matching       : 0.00
% 1.59/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
