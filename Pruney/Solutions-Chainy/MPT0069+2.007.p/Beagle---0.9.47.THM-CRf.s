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
% DateTime   : Thu Dec  3 09:43:17 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_30,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    r2_xboole_0('#skF_1',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11,plain,(
    ! [A_9,C_10,B_11] :
      ( r2_xboole_0(A_9,C_10)
      | ~ r2_xboole_0(B_11,C_10)
      | ~ r1_tarski(A_9,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_15,plain,(
    ! [A_12] :
      ( r2_xboole_0(A_12,k1_xboole_0)
      | ~ r1_tarski(A_12,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_11])).

tff(c_2,plain,(
    ! [A_1] : ~ r2_xboole_0(A_1,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_21,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_15,c_2])).

tff(c_26,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.42/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.42/1.04  
% 1.42/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.42/1.04  %$ r2_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_1
% 1.42/1.04  
% 1.42/1.04  %Foreground sorts:
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  %Background operators:
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  %Foreground operators:
% 1.42/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.42/1.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.42/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.42/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.42/1.04  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.42/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.42/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.42/1.04  
% 1.53/1.05  tff(f_30, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.53/1.05  tff(f_40, negated_conjecture, ~(![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_xboole_1)).
% 1.53/1.05  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.53/1.05  tff(f_28, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.53/1.05  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.53/1.05  tff(c_8, plain, (r2_xboole_0('#skF_1', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.53/1.05  tff(c_11, plain, (![A_9, C_10, B_11]: (r2_xboole_0(A_9, C_10) | ~r2_xboole_0(B_11, C_10) | ~r1_tarski(A_9, B_11))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.53/1.05  tff(c_15, plain, (![A_12]: (r2_xboole_0(A_12, k1_xboole_0) | ~r1_tarski(A_12, '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_11])).
% 1.53/1.05  tff(c_2, plain, (![A_1]: (~r2_xboole_0(A_1, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.53/1.05  tff(c_21, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_15, c_2])).
% 1.53/1.05  tff(c_26, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_21])).
% 1.53/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.05  
% 1.53/1.05  Inference rules
% 1.53/1.05  ----------------------
% 1.53/1.05  #Ref     : 0
% 1.53/1.05  #Sup     : 3
% 1.53/1.05  #Fact    : 0
% 1.53/1.05  #Define  : 0
% 1.53/1.05  #Split   : 0
% 1.53/1.05  #Chain   : 0
% 1.53/1.05  #Close   : 0
% 1.53/1.05  
% 1.53/1.05  Ordering : KBO
% 1.53/1.05  
% 1.53/1.05  Simplification rules
% 1.53/1.05  ----------------------
% 1.53/1.05  #Subsume      : 0
% 1.53/1.05  #Demod        : 1
% 1.53/1.05  #Tautology    : 0
% 1.53/1.05  #SimpNegUnit  : 0
% 1.53/1.05  #BackRed      : 0
% 1.53/1.05  
% 1.53/1.05  #Partial instantiations: 0
% 1.53/1.05  #Strategies tried      : 1
% 1.53/1.05  
% 1.53/1.05  Timing (in seconds)
% 1.53/1.05  ----------------------
% 1.53/1.05  Preprocessing        : 0.23
% 1.53/1.05  Parsing              : 0.12
% 1.53/1.05  CNF conversion       : 0.01
% 1.53/1.05  Main loop            : 0.07
% 1.53/1.05  Inferencing          : 0.03
% 1.53/1.05  Reduction            : 0.02
% 1.53/1.05  Demodulation         : 0.01
% 1.53/1.05  BG Simplification    : 0.01
% 1.53/1.05  Subsumption          : 0.01
% 1.53/1.05  Abstraction          : 0.00
% 1.53/1.05  MUC search           : 0.00
% 1.53/1.05  Cooper               : 0.00
% 1.53/1.05  Total                : 0.32
% 1.53/1.05  Index Insertion      : 0.00
% 1.53/1.05  Index Deletion       : 0.00
% 1.53/1.05  Index Matching       : 0.00
% 1.53/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
