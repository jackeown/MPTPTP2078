%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:51 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_tarski(k2_tarski(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_9,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:29:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.39/0.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.39/0.97  
% 1.39/0.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.39/0.98  %$ k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.39/0.98  
% 1.39/0.98  %Foreground sorts:
% 1.39/0.98  
% 1.39/0.98  
% 1.39/0.98  %Background operators:
% 1.39/0.98  
% 1.39/0.98  
% 1.39/0.98  %Foreground operators:
% 1.39/0.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.39/0.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.39/0.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.39/0.98  tff('#skF_2', type, '#skF_2': $i).
% 1.39/0.98  tff('#skF_1', type, '#skF_1': $i).
% 1.39/0.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.39/0.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.39/0.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.39/0.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.39/0.98  
% 1.39/0.99  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.39/0.99  tff(f_29, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.39/0.99  tff(f_32, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 1.39/0.99  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.39/0.99  tff(c_4, plain, (![A_3, B_4]: (k3_tarski(k2_tarski(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.39/0.99  tff(c_6, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.39/0.99  tff(c_7, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.39/0.99  tff(c_9, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7])).
% 1.39/0.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  Inference rules
% 1.39/0.99  ----------------------
% 1.39/0.99  #Ref     : 0
% 1.39/0.99  #Sup     : 0
% 1.39/0.99  #Fact    : 0
% 1.39/0.99  #Define  : 0
% 1.39/0.99  #Split   : 0
% 1.39/0.99  #Chain   : 0
% 1.39/0.99  #Close   : 0
% 1.39/0.99  
% 1.39/0.99  Ordering : KBO
% 1.39/0.99  
% 1.39/0.99  Simplification rules
% 1.39/0.99  ----------------------
% 1.39/0.99  #Subsume      : 2
% 1.39/0.99  #Demod        : 2
% 1.39/0.99  #Tautology    : 0
% 1.39/0.99  #SimpNegUnit  : 0
% 1.39/0.99  #BackRed      : 0
% 1.39/0.99  
% 1.39/0.99  #Partial instantiations: 0
% 1.39/0.99  #Strategies tried      : 1
% 1.39/0.99  
% 1.39/0.99  Timing (in seconds)
% 1.39/0.99  ----------------------
% 1.39/0.99  Preprocessing        : 0.23
% 1.39/0.99  Parsing              : 0.13
% 1.39/0.99  CNF conversion       : 0.01
% 1.39/0.99  Main loop            : 0.02
% 1.39/0.99  Inferencing          : 0.00
% 1.39/0.99  Reduction            : 0.01
% 1.39/0.99  Demodulation         : 0.01
% 1.39/0.99  BG Simplification    : 0.01
% 1.39/0.99  Subsumption          : 0.00
% 1.39/0.99  Abstraction          : 0.00
% 1.39/0.99  MUC search           : 0.00
% 1.39/0.99  Cooper               : 0.00
% 1.39/0.99  Total                : 0.29
% 1.39/0.99  Index Insertion      : 0.00
% 1.39/0.99  Index Deletion       : 0.00
% 1.39/0.99  Index Matching       : 0.00
% 1.39/0.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
