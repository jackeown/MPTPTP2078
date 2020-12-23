%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:35 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_xboole_0(k4_xboole_0(A_3,B_4),B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.42/0.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.42/1.00  
% 1.42/1.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.42/1.01  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.42/1.01  
% 1.42/1.01  %Foreground sorts:
% 1.42/1.01  
% 1.42/1.01  
% 1.42/1.01  %Background operators:
% 1.42/1.01  
% 1.42/1.01  
% 1.42/1.01  %Foreground operators:
% 1.42/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.42/1.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.42/1.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.42/1.01  tff('#skF_2', type, '#skF_2': $i).
% 1.42/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.42/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.42/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.42/1.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.42/1.01  
% 1.42/1.02  tff(f_29, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.42/1.02  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.42/1.02  tff(f_32, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 1.42/1.02  tff(c_4, plain, (![A_3, B_4]: (r1_xboole_0(k4_xboole_0(A_3, B_4), B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.42/1.02  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.42/1.02  tff(c_6, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2')), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.42/1.02  tff(c_7, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.42/1.02  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_7])).
% 1.42/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.42/1.02  
% 1.42/1.02  Inference rules
% 1.42/1.02  ----------------------
% 1.42/1.02  #Ref     : 0
% 1.42/1.02  #Sup     : 0
% 1.42/1.02  #Fact    : 0
% 1.42/1.02  #Define  : 0
% 1.42/1.02  #Split   : 0
% 1.42/1.02  #Chain   : 0
% 1.42/1.02  #Close   : 0
% 1.42/1.02  
% 1.42/1.02  Ordering : KBO
% 1.42/1.02  
% 1.42/1.02  Simplification rules
% 1.42/1.02  ----------------------
% 1.42/1.02  #Subsume      : 2
% 1.42/1.02  #Demod        : 2
% 1.42/1.02  #Tautology    : 0
% 1.42/1.02  #SimpNegUnit  : 0
% 1.42/1.02  #BackRed      : 0
% 1.42/1.02  
% 1.42/1.02  #Partial instantiations: 0
% 1.42/1.02  #Strategies tried      : 1
% 1.42/1.02  
% 1.42/1.02  Timing (in seconds)
% 1.42/1.02  ----------------------
% 1.42/1.02  Preprocessing        : 0.23
% 1.42/1.02  Parsing              : 0.13
% 1.42/1.02  CNF conversion       : 0.01
% 1.42/1.02  Main loop            : 0.02
% 1.42/1.02  Inferencing          : 0.00
% 1.42/1.02  Reduction            : 0.01
% 1.42/1.02  Demodulation         : 0.01
% 1.42/1.02  BG Simplification    : 0.01
% 1.42/1.02  Subsumption          : 0.00
% 1.42/1.02  Abstraction          : 0.00
% 1.42/1.02  MUC search           : 0.00
% 1.42/1.02  Cooper               : 0.00
% 1.42/1.02  Total                : 0.29
% 1.42/1.02  Index Insertion      : 0.00
% 1.42/1.02  Index Deletion       : 0.00
% 1.42/1.02  Index Matching       : 0.00
% 1.42/1.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
