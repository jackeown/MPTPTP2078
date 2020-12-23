%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:31 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   29 (  40 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k4_xboole_0(A,B),C)
        & r1_tarski(k4_xboole_0(B,A),C) )
     => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_25,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(A_15,C_16)
      | ~ r1_tarski(B_17,C_16)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,'#skF_2')
      | ~ r1_tarski(A_15,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_25])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,'#skF_2')
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_25])).

tff(c_118,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(k5_xboole_0(A_32,B_33),C_34)
      | ~ r1_tarski(k4_xboole_0(B_33,A_32),C_34)
      | ~ r1_tarski(k4_xboole_0(A_32,B_33),C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_151,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_10])).

tff(c_162,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_171,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_162])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_171])).

tff(c_181,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_194,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_33,c_181])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.63  
% 2.34/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.63  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.34/1.63  
% 2.34/1.63  %Foreground sorts:
% 2.34/1.63  
% 2.34/1.63  
% 2.34/1.63  %Background operators:
% 2.34/1.63  
% 2.34/1.63  
% 2.34/1.63  %Foreground operators:
% 2.34/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.34/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.63  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.63  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.63  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.63  
% 2.34/1.65  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.34/1.65  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.34/1.65  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.34/1.65  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 2.34/1.65  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.65  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.65  tff(c_25, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, C_16) | ~r1_tarski(B_17, C_16) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.65  tff(c_33, plain, (![A_15]: (r1_tarski(A_15, '#skF_2') | ~r1_tarski(A_15, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_25])).
% 2.34/1.65  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.65  tff(c_34, plain, (![A_15]: (r1_tarski(A_15, '#skF_2') | ~r1_tarski(A_15, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_25])).
% 2.34/1.65  tff(c_118, plain, (![A_32, B_33, C_34]: (r1_tarski(k5_xboole_0(A_32, B_33), C_34) | ~r1_tarski(k4_xboole_0(B_33, A_32), C_34) | ~r1_tarski(k4_xboole_0(A_32, B_33), C_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.65  tff(c_10, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.65  tff(c_151, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_118, c_10])).
% 2.34/1.65  tff(c_162, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_151])).
% 2.34/1.65  tff(c_171, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_34, c_162])).
% 2.34/1.65  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_171])).
% 2.34/1.65  tff(c_181, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_151])).
% 2.34/1.65  tff(c_194, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_33, c_181])).
% 2.34/1.65  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_194])).
% 2.34/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.65  
% 2.34/1.65  Inference rules
% 2.34/1.65  ----------------------
% 2.34/1.65  #Ref     : 0
% 2.34/1.65  #Sup     : 46
% 2.34/1.65  #Fact    : 0
% 2.34/1.65  #Define  : 0
% 2.34/1.65  #Split   : 1
% 2.34/1.65  #Chain   : 0
% 2.34/1.65  #Close   : 0
% 2.34/1.65  
% 2.34/1.65  Ordering : KBO
% 2.34/1.65  
% 2.34/1.65  Simplification rules
% 2.34/1.65  ----------------------
% 2.34/1.65  #Subsume      : 9
% 2.34/1.65  #Demod        : 8
% 2.34/1.65  #Tautology    : 6
% 2.34/1.65  #SimpNegUnit  : 0
% 2.34/1.65  #BackRed      : 0
% 2.34/1.65  
% 2.34/1.65  #Partial instantiations: 0
% 2.34/1.65  #Strategies tried      : 1
% 2.34/1.65  
% 2.34/1.65  Timing (in seconds)
% 2.34/1.65  ----------------------
% 2.34/1.65  Preprocessing        : 0.40
% 2.34/1.65  Parsing              : 0.22
% 2.34/1.65  CNF conversion       : 0.03
% 2.34/1.65  Main loop            : 0.30
% 2.34/1.65  Inferencing          : 0.12
% 2.34/1.65  Reduction            : 0.08
% 2.34/1.65  Demodulation         : 0.06
% 2.34/1.65  BG Simplification    : 0.01
% 2.34/1.65  Subsumption          : 0.07
% 2.34/1.65  Abstraction          : 0.01
% 2.34/1.65  MUC search           : 0.00
% 2.34/1.65  Cooper               : 0.00
% 2.34/1.65  Total                : 0.75
% 2.34/1.65  Index Insertion      : 0.00
% 2.34/1.65  Index Deletion       : 0.00
% 2.34/1.65  Index Matching       : 0.00
% 2.34/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
