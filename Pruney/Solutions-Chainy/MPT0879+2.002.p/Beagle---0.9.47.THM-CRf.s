%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:30 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   12 (  13 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_tarski(k4_tarski(A_3,B_4),C_5) = k3_mcart_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_zfmisc_1(k1_tarski(A_1),k1_tarski(B_2)) = k1_tarski(k4_tarski(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_12,B_13] : k2_zfmisc_1(k1_tarski(A_12),k1_tarski(B_13)) = k1_tarski(k4_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_zfmisc_1(k2_zfmisc_1(A_6,B_7),C_8) = k3_zfmisc_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_12,B_13,C_8] : k3_zfmisc_1(k1_tarski(A_12),k1_tarski(B_13),C_8) = k2_zfmisc_1(k1_tarski(k4_tarski(A_12,B_13)),C_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6])).

tff(c_8,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k1_tarski('#skF_3')) != k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  %$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.64/1.12  
% 1.64/1.12  %Foreground sorts:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Background operators:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Foreground operators:
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.64/1.12  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.64/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.12  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.12  
% 1.64/1.13  tff(f_29, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.64/1.13  tff(f_27, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 1.64/1.13  tff(f_31, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.64/1.13  tff(f_34, negated_conjecture, ~(![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_mcart_1)).
% 1.64/1.13  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_tarski(k4_tarski(A_3, B_4), C_5)=k3_mcart_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.13  tff(c_2, plain, (![A_1, B_2]: (k2_zfmisc_1(k1_tarski(A_1), k1_tarski(B_2))=k1_tarski(k4_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.13  tff(c_24, plain, (![A_12, B_13]: (k2_zfmisc_1(k1_tarski(A_12), k1_tarski(B_13))=k1_tarski(k4_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.13  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_zfmisc_1(k2_zfmisc_1(A_6, B_7), C_8)=k3_zfmisc_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.13  tff(c_30, plain, (![A_12, B_13, C_8]: (k3_zfmisc_1(k1_tarski(A_12), k1_tarski(B_13), C_8)=k2_zfmisc_1(k1_tarski(k4_tarski(A_12, B_13)), C_8))), inference(superposition, [status(thm), theory('equality')], [c_24, c_6])).
% 1.64/1.13  tff(c_8, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.64/1.13  tff(c_65, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k1_tarski('#skF_3'))!=k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8])).
% 1.64/1.13  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_65])).
% 1.64/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  Inference rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Ref     : 0
% 1.64/1.13  #Sup     : 14
% 1.64/1.13  #Fact    : 0
% 1.64/1.13  #Define  : 0
% 1.64/1.13  #Split   : 0
% 1.64/1.13  #Chain   : 0
% 1.64/1.13  #Close   : 0
% 1.64/1.13  
% 1.64/1.13  Ordering : KBO
% 1.64/1.13  
% 1.64/1.13  Simplification rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Subsume      : 0
% 1.64/1.13  #Demod        : 6
% 1.64/1.13  #Tautology    : 10
% 1.64/1.13  #SimpNegUnit  : 0
% 1.64/1.13  #BackRed      : 1
% 1.64/1.13  
% 1.64/1.13  #Partial instantiations: 0
% 1.64/1.13  #Strategies tried      : 1
% 1.64/1.13  
% 1.64/1.13  Timing (in seconds)
% 1.64/1.13  ----------------------
% 1.64/1.13  Preprocessing        : 0.25
% 1.64/1.13  Parsing              : 0.14
% 1.64/1.13  CNF conversion       : 0.01
% 1.64/1.13  Main loop            : 0.09
% 1.64/1.13  Inferencing          : 0.05
% 1.64/1.13  Reduction            : 0.02
% 1.64/1.13  Demodulation         : 0.02
% 1.64/1.13  BG Simplification    : 0.01
% 1.64/1.13  Subsumption          : 0.01
% 1.64/1.13  Abstraction          : 0.01
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.14  Total                : 0.35
% 1.64/1.14  Index Insertion      : 0.00
% 1.64/1.14  Index Deletion       : 0.00
% 1.64/1.14  Index Matching       : 0.00
% 1.64/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
