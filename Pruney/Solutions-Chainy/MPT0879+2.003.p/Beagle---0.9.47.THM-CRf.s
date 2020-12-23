%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:30 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  27 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_22,B_23,C_24] : k2_zfmisc_1(k2_tarski(A_22,B_23),k1_tarski(C_24)) = k2_tarski(k4_tarski(A_22,C_24),k4_tarski(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [B_23,C_24] : k2_zfmisc_1(k2_tarski(B_23,B_23),k1_tarski(C_24)) = k1_tarski(k4_tarski(B_23,C_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2])).

tff(c_110,plain,(
    ! [B_23,C_24] : k2_zfmisc_1(k1_tarski(B_23),k1_tarski(C_24)) = k1_tarski(k4_tarski(B_23,C_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_116,plain,(
    ! [B_25,C_26] : k2_zfmisc_1(k1_tarski(B_25),k1_tarski(C_26)) = k1_tarski(k4_tarski(B_25,C_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [B_25,C_26,C_10] : k3_zfmisc_1(k1_tarski(B_25),k1_tarski(C_26),C_10) = k2_zfmisc_1(k1_tarski(k4_tarski(B_25,C_26)),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_10])).

tff(c_12,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_216,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_12])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_110,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.27  
% 1.95/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.27  %$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.04/1.27  
% 2.04/1.27  %Foreground sorts:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Background operators:
% 2.04/1.27  
% 2.04/1.27  
% 2.04/1.27  %Foreground operators:
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.04/1.27  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.04/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.27  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.27  
% 2.04/1.28  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.04/1.28  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.28  tff(f_31, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.04/1.28  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.04/1.28  tff(f_38, negated_conjecture, ~(![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_mcart_1)).
% 2.04/1.28  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.28  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.28  tff(c_65, plain, (![A_22, B_23, C_24]: (k2_zfmisc_1(k2_tarski(A_22, B_23), k1_tarski(C_24))=k2_tarski(k4_tarski(A_22, C_24), k4_tarski(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.28  tff(c_84, plain, (![B_23, C_24]: (k2_zfmisc_1(k2_tarski(B_23, B_23), k1_tarski(C_24))=k1_tarski(k4_tarski(B_23, C_24)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_2])).
% 2.04/1.28  tff(c_110, plain, (![B_23, C_24]: (k2_zfmisc_1(k1_tarski(B_23), k1_tarski(C_24))=k1_tarski(k4_tarski(B_23, C_24)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_84])).
% 2.04/1.28  tff(c_116, plain, (![B_25, C_26]: (k2_zfmisc_1(k1_tarski(B_25), k1_tarski(C_26))=k1_tarski(k4_tarski(B_25, C_26)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_84])).
% 2.04/1.28  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.28  tff(c_125, plain, (![B_25, C_26, C_10]: (k3_zfmisc_1(k1_tarski(B_25), k1_tarski(C_26), C_10)=k2_zfmisc_1(k1_tarski(k4_tarski(B_25, C_26)), C_10))), inference(superposition, [status(thm), theory('equality')], [c_116, c_10])).
% 2.04/1.28  tff(c_12, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.04/1.28  tff(c_216, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_12])).
% 2.04/1.28  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_110, c_216])).
% 2.04/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  Inference rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Ref     : 0
% 2.04/1.28  #Sup     : 50
% 2.04/1.28  #Fact    : 0
% 2.04/1.28  #Define  : 0
% 2.04/1.28  #Split   : 0
% 2.04/1.28  #Chain   : 0
% 2.04/1.28  #Close   : 0
% 2.04/1.28  
% 2.04/1.28  Ordering : KBO
% 2.04/1.28  
% 2.04/1.28  Simplification rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Subsume      : 0
% 2.04/1.28  #Demod        : 35
% 2.04/1.28  #Tautology    : 31
% 2.04/1.28  #SimpNegUnit  : 0
% 2.04/1.28  #BackRed      : 1
% 2.04/1.28  
% 2.04/1.28  #Partial instantiations: 0
% 2.04/1.28  #Strategies tried      : 1
% 2.04/1.28  
% 2.04/1.28  Timing (in seconds)
% 2.04/1.28  ----------------------
% 2.04/1.28  Preprocessing        : 0.26
% 2.04/1.28  Parsing              : 0.13
% 2.04/1.28  CNF conversion       : 0.01
% 2.04/1.28  Main loop            : 0.24
% 2.04/1.28  Inferencing          : 0.09
% 2.04/1.28  Reduction            : 0.09
% 2.04/1.28  Demodulation         : 0.07
% 2.04/1.28  BG Simplification    : 0.02
% 2.04/1.28  Subsumption          : 0.02
% 2.04/1.28  Abstraction          : 0.02
% 2.04/1.28  MUC search           : 0.00
% 2.04/1.28  Cooper               : 0.00
% 2.04/1.28  Total                : 0.52
% 2.04/1.28  Index Insertion      : 0.00
% 2.04/1.28  Index Deletion       : 0.00
% 2.04/1.28  Index Matching       : 0.00
% 2.04/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
