%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:38 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  14 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k2_xboole_0(A_11,B_12),C_13) = k2_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k1_tarski(A_17),k2_xboole_0(k1_tarski(B_18),C_19)) = k2_xboole_0(k2_tarski(A_17,B_18),C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_18])).

tff(c_71,plain,(
    ! [A_17,A_4,B_5] : k2_xboole_0(k2_tarski(A_17,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_17),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_75,plain,(
    ! [A_17,A_4,B_5] : k2_xboole_0(k2_tarski(A_17,A_4),k1_tarski(B_5)) = k1_enumset1(A_17,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_8,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:33:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.15  
% 1.62/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.15  %$ k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.62/1.15  
% 1.62/1.15  %Foreground sorts:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Background operators:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Foreground operators:
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.62/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.15  
% 1.62/1.16  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.62/1.16  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.62/1.16  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.62/1.16  tff(f_34, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.62/1.16  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.16  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.16  tff(c_18, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k2_xboole_0(A_11, B_12), C_13)=k2_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.16  tff(c_50, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k1_tarski(A_17), k2_xboole_0(k1_tarski(B_18), C_19))=k2_xboole_0(k2_tarski(A_17, B_18), C_19))), inference(superposition, [status(thm), theory('equality')], [c_4, c_18])).
% 1.62/1.16  tff(c_71, plain, (![A_17, A_4, B_5]: (k2_xboole_0(k2_tarski(A_17, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_17), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_50])).
% 1.62/1.16  tff(c_75, plain, (![A_17, A_4, B_5]: (k2_xboole_0(k2_tarski(A_17, A_4), k1_tarski(B_5))=k1_enumset1(A_17, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_71])).
% 1.62/1.16  tff(c_8, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.62/1.16  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_8])).
% 1.62/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.16  
% 1.62/1.16  Inference rules
% 1.62/1.16  ----------------------
% 1.62/1.16  #Ref     : 0
% 1.62/1.16  #Sup     : 21
% 1.62/1.16  #Fact    : 0
% 1.62/1.16  #Define  : 0
% 1.62/1.16  #Split   : 0
% 1.62/1.16  #Chain   : 0
% 1.62/1.16  #Close   : 0
% 1.62/1.16  
% 1.62/1.16  Ordering : KBO
% 1.62/1.16  
% 1.62/1.16  Simplification rules
% 1.62/1.16  ----------------------
% 1.62/1.16  #Subsume      : 0
% 1.62/1.16  #Demod        : 14
% 1.62/1.16  #Tautology    : 14
% 1.62/1.16  #SimpNegUnit  : 0
% 1.62/1.16  #BackRed      : 1
% 1.62/1.16  
% 1.62/1.16  #Partial instantiations: 0
% 1.62/1.16  #Strategies tried      : 1
% 1.62/1.16  
% 1.62/1.16  Timing (in seconds)
% 1.62/1.16  ----------------------
% 1.62/1.16  Preprocessing        : 0.24
% 1.62/1.16  Parsing              : 0.13
% 1.62/1.16  CNF conversion       : 0.01
% 1.62/1.16  Main loop            : 0.11
% 1.62/1.16  Inferencing          : 0.05
% 1.62/1.16  Reduction            : 0.03
% 1.62/1.16  Demodulation         : 0.03
% 1.62/1.16  BG Simplification    : 0.01
% 1.62/1.16  Subsumption          : 0.01
% 1.62/1.16  Abstraction          : 0.01
% 1.62/1.16  MUC search           : 0.00
% 1.62/1.16  Cooper               : 0.00
% 1.62/1.16  Total                : 0.37
% 1.62/1.16  Index Insertion      : 0.00
% 1.62/1.16  Index Deletion       : 0.00
% 1.62/1.16  Index Matching       : 0.00
% 1.62/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
