%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:31 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  17 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k2_tarski(B,C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,B,D),k3_mcart_1(A,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_mcart_1)).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4] : k2_zfmisc_1(k1_tarski(A_2),k2_tarski(B_3,C_4)) = k2_tarski(k4_tarski(A_2,B_3),k4_tarski(A_2,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_34,B_35,C_36] : k2_zfmisc_1(k2_tarski(A_34,B_35),k1_tarski(C_36)) = k2_tarski(k4_tarski(A_34,C_36),k4_tarski(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_195,plain,(
    ! [A_2,B_3,C_4,C_36] : k2_zfmisc_1(k2_zfmisc_1(k1_tarski(A_2),k2_tarski(B_3,C_4)),k1_tarski(C_36)) = k2_tarski(k4_tarski(k4_tarski(A_2,B_3),C_36),k4_tarski(k4_tarski(A_2,C_4),C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_157])).

tff(c_221,plain,(
    ! [A_2,B_3,C_4,C_36] : k3_zfmisc_1(k1_tarski(A_2),k2_tarski(B_3,C_4),k1_tarski(C_36)) = k2_tarski(k3_mcart_1(A_2,B_3,C_36),k3_mcart_1(A_2,C_4,C_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_8,c_195])).

tff(c_12,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:35:25 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  %$ k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.57/1.39  
% 2.57/1.39  %Foreground sorts:
% 2.57/1.39  
% 2.57/1.39  
% 2.57/1.39  %Background operators:
% 2.57/1.39  
% 2.57/1.39  
% 2.57/1.39  %Foreground operators:
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.57/1.39  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.57/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.39  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.39  
% 2.57/1.40  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.57/1.40  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.57/1.40  tff(f_31, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.57/1.40  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k3_zfmisc_1(k1_tarski(A), k2_tarski(B, C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, B, D), k3_mcart_1(A, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_mcart_1)).
% 2.57/1.40  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.40  tff(c_8, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.40  tff(c_4, plain, (![A_2, B_3, C_4]: (k2_zfmisc_1(k1_tarski(A_2), k2_tarski(B_3, C_4))=k2_tarski(k4_tarski(A_2, B_3), k4_tarski(A_2, C_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.40  tff(c_157, plain, (![A_34, B_35, C_36]: (k2_zfmisc_1(k2_tarski(A_34, B_35), k1_tarski(C_36))=k2_tarski(k4_tarski(A_34, C_36), k4_tarski(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.40  tff(c_195, plain, (![A_2, B_3, C_4, C_36]: (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(A_2), k2_tarski(B_3, C_4)), k1_tarski(C_36))=k2_tarski(k4_tarski(k4_tarski(A_2, B_3), C_36), k4_tarski(k4_tarski(A_2, C_4), C_36)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_157])).
% 2.57/1.40  tff(c_221, plain, (![A_2, B_3, C_4, C_36]: (k3_zfmisc_1(k1_tarski(A_2), k2_tarski(B_3, C_4), k1_tarski(C_36))=k2_tarski(k3_mcart_1(A_2, B_3, C_36), k3_mcart_1(A_2, C_4, C_36)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_8, c_195])).
% 2.57/1.40  tff(c_12, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.40  tff(c_584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_12])).
% 2.57/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.40  
% 2.57/1.40  Inference rules
% 2.57/1.40  ----------------------
% 2.57/1.40  #Ref     : 0
% 2.57/1.40  #Sup     : 138
% 2.57/1.40  #Fact    : 0
% 2.57/1.40  #Define  : 0
% 2.57/1.40  #Split   : 0
% 2.57/1.40  #Chain   : 0
% 2.57/1.40  #Close   : 0
% 2.57/1.40  
% 2.57/1.40  Ordering : KBO
% 2.57/1.40  
% 2.57/1.40  Simplification rules
% 2.57/1.40  ----------------------
% 2.57/1.40  #Subsume      : 4
% 2.57/1.40  #Demod        : 108
% 2.57/1.40  #Tautology    : 70
% 2.57/1.40  #SimpNegUnit  : 0
% 2.57/1.40  #BackRed      : 1
% 2.57/1.40  
% 2.57/1.40  #Partial instantiations: 0
% 2.57/1.40  #Strategies tried      : 1
% 2.57/1.40  
% 2.57/1.40  Timing (in seconds)
% 2.57/1.40  ----------------------
% 2.57/1.40  Preprocessing        : 0.26
% 2.57/1.40  Parsing              : 0.14
% 2.57/1.40  CNF conversion       : 0.01
% 2.57/1.40  Main loop            : 0.33
% 2.57/1.40  Inferencing          : 0.13
% 2.57/1.40  Reduction            : 0.12
% 2.57/1.40  Demodulation         : 0.10
% 2.57/1.40  BG Simplification    : 0.02
% 2.57/1.40  Subsumption          : 0.04
% 2.57/1.40  Abstraction          : 0.03
% 2.57/1.40  MUC search           : 0.00
% 2.57/1.40  Cooper               : 0.00
% 2.57/1.40  Total                : 0.61
% 2.57/1.40  Index Insertion      : 0.00
% 2.57/1.40  Index Deletion       : 0.00
% 2.57/1.40  Index Matching       : 0.00
% 2.57/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
