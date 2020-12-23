%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:49 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_30,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_13,B_14] : r1_tarski(k1_tarski(A_13),k2_tarski(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2])).

tff(c_10,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.10  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.65/1.10  
% 1.65/1.10  %Foreground sorts:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Background operators:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Foreground operators:
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.65/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.10  
% 1.65/1.11  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.65/1.11  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.65/1.11  tff(f_36, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.65/1.11  tff(c_30, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.11  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.11  tff(c_36, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), k2_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2])).
% 1.65/1.11  tff(c_10, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.11  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 1.65/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  Inference rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Ref     : 0
% 1.65/1.11  #Sup     : 7
% 1.65/1.11  #Fact    : 0
% 1.65/1.11  #Define  : 0
% 1.65/1.11  #Split   : 0
% 1.65/1.11  #Chain   : 0
% 1.65/1.11  #Close   : 0
% 1.65/1.11  
% 1.65/1.11  Ordering : KBO
% 1.65/1.11  
% 1.65/1.11  Simplification rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Subsume      : 0
% 1.65/1.11  #Demod        : 1
% 1.65/1.11  #Tautology    : 6
% 1.65/1.11  #SimpNegUnit  : 0
% 1.65/1.11  #BackRed      : 1
% 1.65/1.11  
% 1.65/1.11  #Partial instantiations: 0
% 1.65/1.11  #Strategies tried      : 1
% 1.65/1.11  
% 1.65/1.11  Timing (in seconds)
% 1.65/1.11  ----------------------
% 1.65/1.11  Preprocessing        : 0.28
% 1.65/1.11  Parsing              : 0.15
% 1.65/1.11  CNF conversion       : 0.02
% 1.65/1.11  Main loop            : 0.06
% 1.65/1.11  Inferencing          : 0.03
% 1.65/1.11  Reduction            : 0.02
% 1.65/1.11  Demodulation         : 0.02
% 1.65/1.11  BG Simplification    : 0.01
% 1.65/1.11  Subsumption          : 0.01
% 1.65/1.11  Abstraction          : 0.01
% 1.65/1.11  MUC search           : 0.00
% 1.65/1.11  Cooper               : 0.00
% 1.65/1.11  Total                : 0.36
% 1.65/1.11  Index Insertion      : 0.00
% 1.65/1.11  Index Deletion       : 0.00
% 1.65/1.11  Index Matching       : 0.00
% 1.65/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
