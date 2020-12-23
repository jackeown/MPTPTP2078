%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:49 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_21,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_27,plain,(
    ! [A_11,B_12] : r1_tarski(k1_tarski(A_11),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_2])).

tff(c_10,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.13  
% 1.54/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.14  %$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.54/1.14  
% 1.54/1.14  %Foreground sorts:
% 1.54/1.14  
% 1.54/1.14  
% 1.54/1.14  %Background operators:
% 1.54/1.14  
% 1.54/1.14  
% 1.54/1.14  %Foreground operators:
% 1.54/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.54/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.54/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.54/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.54/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.54/1.14  
% 1.54/1.14  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.54/1.14  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.54/1.14  tff(f_36, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.54/1.14  tff(c_21, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.54/1.14  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.14  tff(c_27, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_21, c_2])).
% 1.54/1.14  tff(c_10, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.54/1.14  tff(c_35, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_10])).
% 1.54/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.14  
% 1.54/1.14  Inference rules
% 1.54/1.14  ----------------------
% 1.54/1.14  #Ref     : 0
% 1.54/1.14  #Sup     : 5
% 1.54/1.14  #Fact    : 0
% 1.54/1.14  #Define  : 0
% 1.54/1.14  #Split   : 0
% 1.54/1.14  #Chain   : 0
% 1.54/1.14  #Close   : 0
% 1.54/1.14  
% 1.54/1.14  Ordering : KBO
% 1.54/1.14  
% 1.54/1.14  Simplification rules
% 1.54/1.14  ----------------------
% 1.54/1.14  #Subsume      : 0
% 1.54/1.14  #Demod        : 1
% 1.54/1.14  #Tautology    : 4
% 1.54/1.14  #SimpNegUnit  : 0
% 1.54/1.14  #BackRed      : 1
% 1.54/1.14  
% 1.54/1.14  #Partial instantiations: 0
% 1.54/1.14  #Strategies tried      : 1
% 1.54/1.14  
% 1.54/1.14  Timing (in seconds)
% 1.54/1.14  ----------------------
% 1.54/1.14  Preprocessing        : 0.25
% 1.54/1.14  Parsing              : 0.13
% 1.54/1.14  CNF conversion       : 0.01
% 1.54/1.14  Main loop            : 0.06
% 1.54/1.14  Inferencing          : 0.02
% 1.54/1.14  Reduction            : 0.02
% 1.54/1.15  Demodulation         : 0.01
% 1.54/1.15  BG Simplification    : 0.01
% 1.54/1.15  Subsumption          : 0.01
% 1.54/1.15  Abstraction          : 0.01
% 1.54/1.15  MUC search           : 0.00
% 1.54/1.15  Cooper               : 0.00
% 1.54/1.15  Total                : 0.33
% 1.54/1.15  Index Insertion      : 0.00
% 1.54/1.15  Index Deletion       : 0.00
% 1.54/1.15  Index Matching       : 0.00
% 1.54/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
