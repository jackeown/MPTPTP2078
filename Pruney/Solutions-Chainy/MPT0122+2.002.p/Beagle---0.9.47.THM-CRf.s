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
% DateTime   : Thu Dec  3 09:45:35 EST 2020

% Result     : Theorem 1.31s
% Output     : CNFRefutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   11 (  11 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_28,axiom,(
    ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_xboole_1)).

tff(c_2,plain,(
    ! [A_1] : ~ r2_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4,plain,(
    r2_xboole_0('#skF_1',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.31/0.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.31/0.99  
% 1.31/0.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.31/1.00  %$ r2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.31/1.00  
% 1.31/1.00  %Foreground sorts:
% 1.31/1.00  
% 1.31/1.00  
% 1.31/1.00  %Background operators:
% 1.31/1.00  
% 1.31/1.00  
% 1.31/1.00  %Foreground operators:
% 1.31/1.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.31/1.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.31/1.00  tff('#skF_1', type, '#skF_1': $i).
% 1.31/1.00  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.31/1.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.31/1.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.31/1.00  
% 1.31/1.01  tff(f_28, axiom, (![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_xboole_1)).
% 1.31/1.01  tff(f_32, negated_conjecture, ~(![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_xboole_1)).
% 1.31/1.01  tff(c_2, plain, (![A_1]: (~r2_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.31/1.01  tff(c_4, plain, (r2_xboole_0('#skF_1', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.31/1.01  tff(c_5, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2, c_4])).
% 1.31/1.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.31/1.01  
% 1.31/1.01  Inference rules
% 1.31/1.01  ----------------------
% 1.31/1.01  #Ref     : 0
% 1.31/1.01  #Sup     : 0
% 1.31/1.01  #Fact    : 0
% 1.31/1.01  #Define  : 0
% 1.31/1.01  #Split   : 0
% 1.31/1.01  #Chain   : 0
% 1.31/1.01  #Close   : 0
% 1.31/1.01  
% 1.31/1.01  Ordering : KBO
% 1.31/1.01  
% 1.31/1.01  Simplification rules
% 1.31/1.01  ----------------------
% 1.31/1.01  #Subsume      : 1
% 1.31/1.01  #Demod        : 0
% 1.31/1.01  #Tautology    : 0
% 1.31/1.01  #SimpNegUnit  : 1
% 1.31/1.01  #BackRed      : 0
% 1.31/1.01  
% 1.31/1.01  #Partial instantiations: 0
% 1.31/1.01  #Strategies tried      : 1
% 1.31/1.01  
% 1.31/1.01  Timing (in seconds)
% 1.31/1.01  ----------------------
% 1.31/1.01  Preprocessing        : 0.22
% 1.31/1.01  Parsing              : 0.11
% 1.31/1.01  CNF conversion       : 0.01
% 1.31/1.01  Main loop            : 0.02
% 1.31/1.01  Inferencing          : 0.00
% 1.31/1.01  Reduction            : 0.01
% 1.31/1.01  Demodulation         : 0.00
% 1.31/1.01  BG Simplification    : 0.01
% 1.31/1.01  Subsumption          : 0.00
% 1.31/1.01  Abstraction          : 0.00
% 1.31/1.01  MUC search           : 0.00
% 1.31/1.01  Cooper               : 0.00
% 1.31/1.01  Total                : 0.27
% 1.31/1.01  Index Insertion      : 0.00
% 1.31/1.01  Index Deletion       : 0.00
% 1.31/1.02  Index Matching       : 0.00
% 1.31/1.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
