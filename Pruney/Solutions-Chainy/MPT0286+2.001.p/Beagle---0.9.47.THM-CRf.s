%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:31 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_30,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k3_tarski(k2_tarski(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    k3_tarski(k2_tarski('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:37:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.40/0.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.40/1.00  
% 1.40/1.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.40/1.01  %$ k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_1
% 1.40/1.01  
% 1.40/1.01  %Foreground sorts:
% 1.40/1.01  
% 1.40/1.01  
% 1.40/1.01  %Background operators:
% 1.40/1.01  
% 1.40/1.01  
% 1.40/1.01  %Foreground operators:
% 1.40/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.40/1.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.40/1.01  tff('#skF_2', type, '#skF_2': $i).
% 1.40/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.40/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.40/1.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.40/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.40/1.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.40/1.01  
% 1.40/1.01  tff(f_27, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.40/1.01  tff(f_30, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 1.40/1.01  tff(c_2, plain, (![A_1, B_2]: (k3_tarski(k2_tarski(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.40/1.01  tff(c_4, plain, (k3_tarski(k2_tarski('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.40/1.01  tff(c_6, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.40/1.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.40/1.01  
% 1.40/1.01  Inference rules
% 1.40/1.01  ----------------------
% 1.40/1.01  #Ref     : 0
% 1.40/1.01  #Sup     : 0
% 1.40/1.01  #Fact    : 0
% 1.40/1.01  #Define  : 0
% 1.40/1.01  #Split   : 0
% 1.40/1.01  #Chain   : 0
% 1.40/1.01  #Close   : 0
% 1.40/1.01  
% 1.40/1.01  Ordering : KBO
% 1.40/1.01  
% 1.40/1.01  Simplification rules
% 1.40/1.01  ----------------------
% 1.40/1.01  #Subsume      : 1
% 1.40/1.01  #Demod        : 1
% 1.40/1.01  #Tautology    : 0
% 1.40/1.01  #SimpNegUnit  : 0
% 1.40/1.01  #BackRed      : 0
% 1.40/1.01  
% 1.40/1.01  #Partial instantiations: 0
% 1.40/1.01  #Strategies tried      : 1
% 1.40/1.01  
% 1.40/1.01  Timing (in seconds)
% 1.40/1.01  ----------------------
% 1.40/1.02  Preprocessing        : 0.22
% 1.40/1.02  Parsing              : 0.12
% 1.40/1.02  CNF conversion       : 0.01
% 1.40/1.02  Main loop            : 0.02
% 1.40/1.02  Inferencing          : 0.00
% 1.40/1.02  Reduction            : 0.01
% 1.40/1.02  Demodulation         : 0.01
% 1.40/1.02  BG Simplification    : 0.00
% 1.40/1.02  Subsumption          : 0.00
% 1.40/1.02  Abstraction          : 0.00
% 1.40/1.02  MUC search           : 0.00
% 1.40/1.02  Cooper               : 0.00
% 1.40/1.02  Total                : 0.27
% 1.40/1.02  Index Insertion      : 0.00
% 1.40/1.02  Index Deletion       : 0.00
% 1.40/1.02  Index Matching       : 0.00
% 1.40/1.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
